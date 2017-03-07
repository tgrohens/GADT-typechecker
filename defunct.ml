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

let is_tycon typ1 typ2 =
  (match typ1 with TyTuple _ -> true | _ -> false) &&
  (match typ2 with TyCon(_, _) -> true | _ -> false)

(* translate a type by replacing arrows with the arrow type constructor *)

let rec translate_type arrow typ = match typ with
  | TyBoundVar _
  | TyFreeVar _ -> typ

  | TyArrow(typ1, typ2) when is_tycon typ1 typ2 ->
      TyArrow(translate_type arrow typ1, translate_type arrow typ2)

  | TyArrow(typ1, typ2) ->
      TyCon(arrow, [translate_type arrow typ1;
        translate_type arrow typ2])

  | TyForall context ->
      let a = Atom.fresha arrow in
      let typ = fill context (TyFreeVar a) in
      let typ = translate_type arrow typ in
      TyForall (abstract a typ)

  | TyCon(tycon, types) ->
      TyCon(tycon, List.map (translate_type arrow) types)

  | TyTuple types ->
      TyTuple (List.map (translate_type arrow) types)

  | TyWhere(t1, t2, t3) ->
      TyWhere(translate_type arrow t1, translate_type arrow t2,
        translate_type arrow t2)  

(* return the term and a list of newly created data constructors matching the
   λ-abstractions inside the term *)

let rec translate_term p arrow apply term = match term with
  | TeVar a -> [], term

  | TeAbs(x, typ, e, info_ref) ->
      let newdatacons, e' = translate_term p arrow apply e in
      let info = get (!info_ref) in
      let arg_ty, ret_ty = deconst_arrow info.fty in
      let freetyvars =
        AtomSet.union (AtomSet.union (ftv_equs info.hyps) (ftv_tenv info.tenv))
                      (AtomSet.union (ftv arg_ty) (ftv ret_ty)) in
      let absdatacons = Atom.fresh
        (Identifier.mk "Apply_lambda" Syntax.term_sort) in
      (* translate the typing env and constraint *)
      let trans_hyps = List.map (fun (ty1, ty2) ->
        (translate_type arrow ty1, translate_type arrow ty2)) info.hyps in
      let tenv_vars, tenv_types = List.split (AtomMap.bindings info.tenv) in
      let trans_types = List.map (translate_type arrow) tenv_types in
      (* construct the type scheme of the new data constructor *)
      let base_type = TyArrow (TyTuple trans_types,
        TyCon (arrow,
          [translate_type arrow arg_ty; translate_type arrow ret_ty])) in
      let equs_type = wheres base_type trans_hyps in
      let univ_type = foralls (AtomSet.elements freetyvars) equs_type in
      (absdatacons, univ_type)::newdatacons,
      TeData(absdatacons,
        List.map (fun v -> TyFreeVar v) (AtomSet.elements freetyvars),
        List.map (fun x -> TeVar x) tenv_vars)



  | TeApp(e1, e2, inf) ->
      let info = get !inf in
      let new1, e1' = translate_term p arrow apply e1 in
      let new2, e2' = translate_term p arrow apply e2 in
      let typ1 = translate_type arrow info.domain in
      let typ2 = translate_type arrow info.codomain in 
      new1@new2, TeApp(TeApp(TeTyApp(TeTyApp(TeVar(apply), typ1), typ2),
                       e1', ref None), e2', ref None)

  | TeLet(x, e1, e2) ->
      let new1, e1' = translate_term p arrow apply e1 in
      let new2, e2' = translate_term p arrow apply e2 in
      new1@new2, TeLet(x, e1', e2')

  | TeFix(x, typ, e) ->
      let newdatacons, e' = translate_term p arrow apply e in
      let typ' = translate_type arrow typ in
      newdatacons, TeFix(x, typ', e')

  | TeTyAbs(alpha, e) ->
      let newdatacons, e' = translate_term p arrow apply e in
      newdatacons, TeTyAbs(alpha, e')

  | TeTyApp(e, tau) ->
      let newdatacons, e' = translate_term p arrow apply e in
      let tau' = translate_type arrow tau in
      newdatacons, TeTyApp(e', tau')

  | TeData(k, types, terms) ->
      let newdatacons, terms' = List.fold_right
        (fun term (dclist, tlist) ->
          let newdcs, term' = translate_term p arrow apply term in
          newdcs@dclist, term'::tlist) terms ([], []) in
      let types' = List.map (translate_type arrow) types in
      newdatacons, TeData(k, types', terms')

  | TeTyAnnot(term, typ) ->
      let newdatacons, term' = translate_term p arrow apply term in
      let typ' = translate_type arrow typ in
      newdatacons, TeTyAnnot(term', typ')

  | TeMatch(e, rettyp, clauses) ->
      let newdatacons, e' = translate_term p arrow apply e in
      let rettyp' = translate_type arrow rettyp in
      let newdatacons, clauses' = List.fold_right
        (fun clause (dclist, clist) ->
          let newdcs, clause' = translate_clause p arrow apply clause in
          newdcs@dclist, clause'::clist) clauses (newdatacons, []) in
      newdatacons, TeMatch(e', rettyp', clauses')

  | TeLoc(loc, term) ->
      let newdatacons, term' = translate_term p arrow apply term in
      newdatacons, TeLoc(loc, term')

and translate_clause p arrow apply clause =
  let Clause (patt, e) = clause in
  let newdatacons, e' = translate_term p arrow apply e in
  newdatacons, Clause(patt, e')

let translate (prog : Terms.program) =
  let Prog(types, datacons, body) = prog in
  let arrow = Atom.fresh (Identifier.mk "arrow" Syntax.typecon_sort) in
  let apply = Atom.fresh (Identifier.mk "Apply" Syntax.term_sort) in
  let types = AtomMap.add arrow 2 types in
  let datacon_table = AtomMap.map (translate_type arrow) datacons in
  let newdatacons, body = translate_term prog arrow apply body in
  let apply_code = TeVar apply in
  let datacons = List.fold_left
    (fun dcs (newdc, scheme) -> AtomMap.add newdc scheme dcs)
    datacon_table newdatacons in
  Prog(types, datacons, TeLet(apply, apply_code, body))
