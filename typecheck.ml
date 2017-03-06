open Printf
open Atom
open Types
open Equations
open Terms
open Symbols
open Print
open Typerr

(* ------------------------------------------------------------------------- *)

(* Specification of the type-checker. *)

(* The core of the typechecker is made up of two mutually recursive
   functions. [infer] infers a type and returns it; [check] infers a
   type, checks that it is equal to the expected type, and returns
   nothing. *)

(* The type [ty] that is produced by [infer] should be correct, that
   is, the typing judgement [hyps, tenv |- term : ty] should hold.
   Furthermore, it should be unique, that is, for every type [ty']
   such that the judgement [hyps, tenv |- term : ty'] holds, the
   hypotheses [hyps] entail the equation [ty = ty']. *)

(* The function [check] should be correct, that is, if it succeeds,
   then the typing judgement [hyps, tenv |- term : expected] holds. *)

(* ------------------------------------------------------------------------- *)

(* A completeness issue. *)

(* Ideally, the functions [infer] and [check] should be complete, that
   is, if they fail, then the term is ill-typed according to the
   typing rules in Pottier and Gauthier's paper. However, with the
   tools that we provide, this goal is difficult to meet, for the
   following reason.

   Consider, for instance, a function application [x1 x2]. We can use
   [infer] to obtain the types of [x1] and [x2], say, [ty1] and
   [ty2]. Then, we must check that, FOR SOME TYPE [ty], THE HYPOTHESES
   [hyps] ENTAIL THAT the type [ty1] is equal to the function type
   [TyArrow ty2 ty].

   This is a bit problematic. Of course, if the hypotheses [hyps] are
   empty, this is easy: it is just a syntactic check. If somehow the
   type [ty] was known, this would be easy as well: it would be an
   entailment check, for which we provide a decision procedure.
   However, in the general case, we need to solve a more difficult
   problem -- entailment with unknowns -- for which (out of laziness,
   perhaps) we haven't provided an algorithm.

   As a result, we suggest that you stick with a simple syntactic
   check. Your type-checker will thus be incomplete. That will not be
   a real problem: the user can work around it by adding an explicit
   type annotation to convert [ty1] into the desired function type
   [TyArrow ty1 ty]. The sample file [test/good/conversion.f]
   illustrates this.
   
   If you follow our suggestion and develop an incomplete
   type-checker, then you may run into a problem when implementing
   defunctionalization. The program produced by your
   defunctionalization phase may be well-typed, yet may be rejected by
   your type-checker, for the above reason. If this happens, you will
   have to work around the problem by having your defunctionalization
   algorithm produce explicit type annotations where appropriate. *)

(* ------------------------------------------------------------------------- *)

(* The type-checker. *)

let rec infer              (* [infer] expects... *)
    (p : program)          (* a program, which provides information about type & data constructors; *)
    (xenv : Export.env)    (* a pretty-printer environment, for printing types; *)
    (loc : Error.location) (* a location, for reporting errors; *)
    (hyps : equations)     (* a set of equality assumptions *)
    (tenv : tenv)          (* a typing environment; *)
    (term : fterm)         (* a term; *)
    : ftype =              (* ...and returns a type. *)

  match term with

  | TeVar a -> lookup a tenv 

  | TeAbs(x, typ, e, info) ->
      let body_type = infer p (Export.bind xenv x) loc hyps
        (bind x typ tenv) e in
      let fty = TyArrow (typ, body_type) in
      info := Some {hyps = hyps; tenv = tenv; fty = fty};
      fty

  | TeApp(e1, e2, info) ->
      let fty = infer p xenv loc hyps tenv e1 in (* tau = t -> t ? *)
      let dom, codom = deconstruct_arrow xenv loc fty in
      check p xenv hyps tenv e2 dom;
      info := Some {domain = dom; codomain = codom};
      codom

  | TeLet(x, e1, e2) ->
      let typ1 = infer p xenv loc hyps tenv e1 in
      infer p (Export.bind xenv x) loc hyps (bind x typ1 tenv) e2

  | TeFix(x, typ, e) ->
      check p (Export.bind xenv x) hyps (bind x typ tenv) e typ; typ

  | TeTyAbs(alpha, e) ->
      let typ = infer p (Export.bind xenv alpha) loc hyps tenv e in
      TyForall (abstract alpha typ)

  | TeTyApp(e, tau) ->
      let typ = infer p xenv loc hyps tenv e in
      let univtyp = deconstruct_univ xenv loc typ in
      fill univtyp tau

  | TeData(k, types, terms) ->
      (* get the type associated to k and instantiate the head variables *)
      let univ = type_scheme p k in
      let inst_type = inst_datacon xenv loc k univ types in
      (* check that the equality constraints hold and add them to the context *)
      let (inst_type, hyps) = check_typequs xenv loc inst_type hyps in
      (* verify that the [terms] have the right [types] *)
      let (exp_tuple, res) = deconstruct_arrow xenv loc inst_type in
      let exp_types = deconstruct_tuple xenv loc exp_tuple in
      if (List.length exp_types != List.length terms) then
        arity_mismatch xenv loc "data constructor" k "term"
          (List.length exp_types) (List.length terms)
      else
        List.iter2 (check p xenv hyps tenv) terms exp_types;
      res


  | TeTyAnnot(term, typ) ->
      check p xenv hyps tenv term typ;
      typ

  | TeMatch(e, rettyp, clauses) ->
      let datatyp = infer p xenv loc hyps tenv e in
      let tycon, contyps = deconstruct_tycon_l xenv loc datatyp in
      let possible_datacons = data_constructors p tycon in
      let abs_datacons = type_clauses p xenv hyps tenv rettyp tycon contyps 
        possible_datacons clauses in
      (* add treatment of missing clauses *)
      AtomSet.iter (missing_clauses p xenv loc hyps tenv rettyp tycon contyps)
        abs_datacons;
      rettyp

  | TeLoc(loc, term) -> infer p xenv loc hyps tenv term

and type_clauses
  (p : program)
  (xenv : Export.env)
  (hyps : equations)
  (tenv : tenv)
  (exp_rettyp : ftype)
  (exp_tycon : Atom.atom)
  (contyps : ftype list)
  (poss_datacons : AtomSet.t)
  (clauses : clause list)
  : AtomSet.t =
  match clauses with
  | [] ->
      poss_datacons

  | clause::clauses ->
      let Clause(patt, term) = clause in
      let PatData(loc, k, typarams, params) = patt in
      let tyabsvars = List.map (fun p -> TyFreeVar p) typarams in
      let xenv2 = Export.sbind xenv typarams in
      (* instantiate the head quantifiers *)
      let univ = type_scheme p k in
      let inst_type = inst_datacon xenv2 loc k univ tyabsvars in
      (* add the constraints to the environment *)
      let (inst_type, hyps2) = add_typequs inst_type hyps in
      (* get the actual term types tuple and data constructor *)
      let (param_tytuple, rettyp) = deconstruct_arrow xenv2 loc inst_type in
      let param_types = deconstruct_tuple xenv2 loc param_tytuple in
      let (tycon, ret_contyps) = deconstruct_tycon_l xenv2 loc rettyp in
      (* check we have the right type constructor *)
      begin if Atom.equal tycon exp_tycon = false then
        typecon_mismatch xenv2 loc k exp_tycon tycon end;
      (* check we didn't already have a clause with this datacon *)
      begin if AtomSet.mem k poss_datacons = false then
        redundant_clause loc end;
      (* check we have the right number of term parameters *)
      begin if List.length params <> List.length param_types then
        arity_mismatch xenv2 loc "data constructor" k "term"
          (List.length param_types) (List.length params) end;
      (* add contyps = ret_contyps to the context *)
      let hyps2 = add_hyps hyps2 contyps ret_contyps in
      (* add the parameters to the typing environment *)
      let tenv2 = binds (List.combine params param_types) tenv in
      let xenv2 = Export.sbind xenv2 params in
      begin
      if inconsistent hyps2 then begin
       inaccessible_clause loc end
      else
        check p xenv2 hyps2 tenv2 term exp_rettyp;
      end;
      type_clauses p xenv hyps tenv exp_rettyp exp_tycon contyps
        (AtomSet.remove k poss_datacons) clauses
      
and missing_clauses p xenv loc hyps tenv exp_rettyp exp_tycon contyps datacon =
  let univ = type_scheme p datacon in
  let rec fill_univ xenv = function
    | TyForall c ->
        let a = Atom.fresha datacon in
        fill_univ (Export.bind xenv a) (fill c (TyFreeVar a))
    | t -> xenv, t in
  let xenv, inst_type = fill_univ xenv univ in
  let inst_type, hyps = add_typequs inst_type hyps in
  let _, rettyp = deconstruct_arrow xenv loc inst_type in
  let _, ret_contyps = deconstruct_tycon_l xenv loc rettyp in
  let hyps = add_hyps hyps contyps ret_contyps in
  if inconsistent hyps = false then
    missing_clause xenv hyps loc datacon 


and check                  (* [check] expects... *)
    (p : program)          (* a program, which provides information about type & data constructors; *)
    (xenv : Export.env)    (* a pretty-printer environment, for printing types; *)
    (hyps : equations)     (* a set of equality assumptions *)
    (tenv : tenv)          (* a typing environment; *)
    (term : fterm)         (* a term; *)
    (expected : ftype)     (* an expected type; *)
    : unit =               (* ...and returns nothing. *)

  (* We bet that the term begins with a [TeLoc] constructor. This should be
     true because the parser inserts one such constructor between every two
     ordinary nodes. In fact, this is not quite true, because the parser
     sometimes expands syntactic sugar without creating intermediate [TeLoc]
     nodes. If you invoke [check] in reasonable places, it should just work. *)

  match term with
  | TeLoc (loc, term) ->
      let inferred = infer p xenv loc hyps tenv term in
      if entailment hyps [(expected, inferred)] = false then
        mismatch xenv loc hyps expected inferred

  | _ ->
      (* out of luck! *)
      assert false

(* ------------------------------------------------------------------------- *)

(* A complete program is typechecked within empty environments. *)

let run (Prog (tctable, dctable, term) as p : program) =
  let xenv = Export.empty
  and loc = Error.dummy
  and hyps = []
  and tenv = Types.empty in
  let xenv = AtomMap.fold (fun tc _ xenv -> Export.bind xenv tc) tctable xenv in
  let xenv = AtomMap.fold (fun dc _ xenv -> Export.bind xenv dc) dctable xenv in
  xenv, infer p xenv loc hyps tenv term
