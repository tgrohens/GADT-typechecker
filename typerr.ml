open Printf
open Types
open Print
open Symbols
open Equations

(* Auxiliary functions for the type-checker. *)

(* ------------------------------------------------------------------------- *)

(* Error messages. *)

let print_hypotheses xenv hyps =
  match hyps with
  | [] ->
      ""
  | _ ->
      sprintf "Hypotheses:\n%s" (print_equations xenv hyps)

let mismatch xenv loc hyps expected inferred =
  Error.error [loc] (sprintf
    "Type mismatch.\nExpected: %s\nInferred: %s\n%s"
    (print_type xenv expected)
    (print_type xenv inferred)
    (print_hypotheses xenv hyps)
  )

let unsatisfied_equation xenv loc hyps lhs rhs =
  Error.error [loc] (sprintf
    "This type equation should but does not hold:\n%s%s"
    (print_equations xenv [ lhs, rhs ])
    (print_hypotheses xenv hyps)
  )

let expected_form xenv loc form ty =
  Error.error [loc] (sprintf
    "Type mismatch: I expected %s type.\nInferred: %s\n"
    form
    (print_type xenv ty)
  )

let typecon_mismatch xenv loc d expected found =
  Error.error [loc] (sprintf
    "Data constructor mismatch.\n\
     Expected a data constructor associated with the type constructor: %s\n\
     Found the data constructor: %s\n\
     which is associated with the type constructor: %s\n"
    (print_atom xenv expected)
    (print_atom xenv d)
    (print_atom xenv found)
  )

let arity_mismatch xenv loc kind1 x kind2 expected found =
  Error.error [loc] (sprintf
    "The %s %s expects %d %s arguments,\nbut is applied to %d %s arguments.\n"
    kind1 (print_atom xenv x) expected kind2 found kind2
  )

let redundant_clause loc =
  Error.warning [loc] "Warning: this clause is redundant.\n"

let inaccessible_clause loc =
  Error.warning [loc] "Warning: this clause is inaccessible.\n"

let missing_clause xenv hyps loc dc =
  Error.error [loc] (sprintf
    "A case for the data constructor %s is missing.\n%s"
    (print_atom xenv dc)
    (print_hypotheses xenv hyps)
  )

(* ------------------------------------------------------------------------- *)

(* Functions that require a type to exhibit a certain shape, and deconstruct
   it. *)

let deconstruct_arrow xenv loc : ftype -> ftype * ftype =
  function
    | TyArrow (domain, codomain) ->
	domain, codomain
    | ty ->
	expected_form xenv loc "an arrow" ty

let deconstruct_univ xenv loc : ftype -> ftype_context =
  function
    | TyForall body ->
	body
    | ty ->
	expected_form xenv loc "a universal" ty

let deconstruct_tycon xenv loc : ftype -> Atom.atom =
  function
    | TyCon (tc, _) ->
	tc
    | ty ->
	expected_form xenv loc "an algebraic data" ty

let deconstruct_tycon_l xenv loc : ftype -> Atom.atom * ftype list =
  function
    | TyCon (tc, tl) ->
	tc, tl
    | ty ->
	expected_form xenv loc "an algebraic data" ty

let deconstruct_tuple xenv loc : ftype -> ftype list =
  function
    | TyTuple l -> l
    | ty -> expected_form xenv loc "a tuple" ty (* shouldn't happen *)

(* ------------------------------------------------------------------------- *)

(* Functions that help manipulate type and data constructors. *)

let inst_datacon xenv loc k univ types = 
  let rec inst_list count univ types = match types with
    | [] ->
        let foralls = count_foralls univ in
        if foralls > 0 then
          arity_mismatch xenv loc "data constructor" k "type"
            (foralls+count) count
        else univ 
    | typ::types ->
        (* we don't directly use deconstruct_univ to remember the number of
           applied type arguments *)
        let ty_con = match univ with
          | TyForall c -> c
          | _ -> arity_mismatch xenv loc "data constructor" k "type"
              count (count + (List.length types) + 1) in
        inst_list (count+1) (fill ty_con typ) types in
  inst_list 0 univ types

let rec check_typequs xenv loc typ hyps =
  match typ with
    | TyWhere (typ, lhs, rhs) ->
        if entailment hyps [(lhs, rhs)] = false then
          unsatisfied_equation xenv loc hyps lhs rhs
        else
          check_typequs xenv loc typ ((lhs, rhs)::hyps)
    | _ -> typ, hyps

let rec add_typequs typ hyps =
  match typ with
    | TyWhere (typ, lhs, rhs) ->
        let typ, hyps = add_typequs typ hyps in
        typ, (lhs, rhs)::hyps
    | _ -> typ, hyps
    
let rec add_hyps hyps typs1 typs2 =
  match typs1, typs2 with
    | [], [] -> hyps
    | t1::t1s, t2::t2s -> (t1, t2)::(add_hyps hyps t1s t2s)
    | _ -> assert false (* shouldn't happen *)
