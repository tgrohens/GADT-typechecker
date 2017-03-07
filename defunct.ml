open Types
open Terms
open Atom
open Symbols

(* helper functions *)

let rec ftv_equs = function
  | [] -> AtomSet.empty
  | (typ1, typ2)::c ->
      AtomSet.union (AtomSet.union (ftv typ1) (ftv typ2))
        (ftv_equs c)

let rec ftv_tenv tenv =
  AtomMap.fold (fun _ typ -> AtomSet.union (ftv typ)) tenv AtomSet.empty

let deconst_arrow = function
  | TyArrow(t1, t2) -> t1, t2
  | _ -> assert false

let get = function
  | Some x -> x
  | _ -> assert false

(* translate a type by replacing arrows with the arrow type constructor *)

let rec translate_type arrow_con typ = match typ with
  | TyBoundVar _
  | TyFreeVar _ -> typ

  | TyArrow(typ1, typ2) ->
      TyCon(arrow_con, [translate_type arrow_con typ1;
        translate_type arrow_con typ2])

  | TyForall context ->
      let a = Atom.fresha arrow_con in
      let typ = fill context (TyFreeVar a) in
      let typ = translate_type arrow_con typ in
      TyForall (abstract a typ)

  | TyCon(tycon, types) ->
      TyCon(tycon, List.map (translate_type arrow_con) types)

  | TyTuple types ->
      TyTuple (List.map (translate_type arrow_con) types)

  | TyWhere(t1, t2, t3) ->
      TyWhere(translate_type arrow_con t1, translate_type arrow_con t2,
        translate_type arrow_con t2)  

(* return the term and a list of newly created data constructors matching the
   λ-abstractions inside the term *)

let rec translate_term p arrow_con apply term = match term with
  | TeVar a -> [], term

  | TeAbs(x, typ, e, info_ref) ->
      let newdatacons, e' = translate_term p arrow_con apply e in
      let info = get (!info_ref) in
      let arg_ty, ret_ty = deconst_arrow info.fty in
      let freetyvars =
        AtomSet.union (AtomSet.union (ftv_equs info.hyps) (ftv_tenv info.tenv))
                      (AtomSet.union (ftv arg_ty) (ftv ret_ty)) in
      let absdatacons = Atom.fresh
        (Identifier.mk "Apply_lambda" Syntax.term_sort) in
      (* translate the typing env and constraint *)
      let trans_hyps = List.map (fun (ty1, ty2) ->
        (translate_type arrow_con ty1, translate_type arrow_con ty2)) info.hyps in
      let tenv_vars, tenv_types = List.split (AtomMap.bindings info.tenv) in
      let trans_types = List.map (translate_type arrow_con) tenv_types in
      (* construct the type scheme of the new data constructor *)
      let base_type = TyArrow (TyTuple trans_types,
        TyCon (arrow_con,
          [translate_type arrow_con arg_ty; translate_type arrow_con ret_ty])) in
      let equs_type = wheres base_type trans_hyps in
      let univ_type = foralls (AtomSet.elements freetyvars) equs_type in
      (absdatacons, univ_type)::newdatacons,
      TeData(absdatacons,
        List.map (fun v -> TyFreeVar v) (AtomSet.elements freetyvars),
        List.map (fun x -> TeVar x) tenv_vars)



  | TeApp(e1, e2, inf) ->
      let info = get !inf in
      let new1, e1' = translate_term p arrow_con apply e1 in
      let new2, e2' = translate_term p arrow_con apply e2 in
      let typ1 = translate_type arrow_con info.domain in
      let typ2 = translate_type arrow_con info.codomain in 
      new1@new2, TeApp(TeApp(TeTyApp(TeTyApp(TeVar(apply), typ1), typ2),
                       e1', ref None), e2', ref None)

  | TeLet(x, e1, e2) -> failwith "todo"

  | TeFix(x, typ, e) -> failwith "todo"

  | TeTyAbs(alpha, e) -> failwith "todo"

  | TeTyApp(e, tau) -> failwith "todo"

  | TeData(k, types, terms) -> failwith "todo"

  | TeTyAnnot(term, typ) -> failwith "todo"

  | TeMatch(e, rettyp, clauses) -> failwith "todo"

  | TeLoc(loc, term) -> failwith "todo"



let translate (prog : Terms.program) =
  prog (* do something here! *)
