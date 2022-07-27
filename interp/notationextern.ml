(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Declaration of uninterpretation functions (i.e. printing rules)
    for notations *)

(*i*)
open Util
open Names
open Globnames
open Constrexpr
open Notation_term
open Glob_term
(*i*)

let notation_entry_level_eq s1 s2 = match (s1,s2) with
| InConstrEntrySomeLevel, InConstrEntrySomeLevel -> true
| InCustomEntryLevel (s1,n1), InCustomEntryLevel (s2,n2) -> String.equal s1 s2 && n1 = n2
| (InConstrEntrySomeLevel | InCustomEntryLevel _), _ -> false

let pair_eq f g (x1, y1) (x2, y2) = f x1 x2 && g y1 y2

let notation_binder_source_eq s1 s2 = match s1, s2 with
| NtnParsedAsIdent,  NtnParsedAsIdent -> true
| NtnParsedAsName,  NtnParsedAsName -> true
| NtnParsedAsPattern b1, NtnParsedAsPattern b2 -> b1 = b2
| NtnBinderParsedAsConstr bk1, NtnBinderParsedAsConstr bk2 -> bk1 = bk2
| NtnParsedAsBinder,  NtnParsedAsBinder -> true
| (NtnParsedAsIdent | NtnParsedAsName | NtnParsedAsPattern _ | NtnBinderParsedAsConstr _ | NtnParsedAsBinder), _ -> false

let ntpe_eq t1 t2 = match t1, t2 with
| NtnTypeConstr, NtnTypeConstr -> true
| NtnTypeBinder s1, NtnTypeBinder s2 -> notation_binder_source_eq s1 s2
| NtnTypeConstrList, NtnTypeConstrList -> true
| NtnTypeBinderList, NtnTypeBinderList -> true
| (NtnTypeConstr | NtnTypeBinder _ | NtnTypeConstrList | NtnTypeBinderList), _ -> false

let var_attributes_eq (_, ((entry1, sc1), tp1)) (_, ((entry2, sc2), tp2)) =
  notation_entry_level_eq entry1 entry2 &&
  pair_eq (Option.equal String.equal) (List.equal String.equal) sc1 sc2 &&
  ntpe_eq tp1 tp2

let interpretation_eq (vars1, t1 as x1) (vars2, t2 as x2) =
  x1 == x2 ||
  List.equal var_attributes_eq vars1 vars2 &&
  Notation_ops.eq_notation_constr (List.map fst vars1, List.map fst vars2) t1 t2

(* Uninterpretation tables *)

type interp_rule =
  | NotationRule of specific_notation
  | AbbrevRule of KerName.t

(* We define keys for glob_constr and aconstr to split the syntax entries
   according to the key of the pattern (adapted from Chet Murthy by HH) *)

type key =
  | RefKey of GlobRef.t
  | Oth

let key_compare k1 k2 = match k1, k2 with
  | RefKey gr1, RefKey gr2 -> GlobRef.CanOrd.compare gr1 gr2
  | RefKey _, Oth -> -1
  | Oth, RefKey _ -> 1
  | Oth, Oth -> 0

module KeyOrd = struct type t = key let compare = key_compare end
module KeyMap = Map.Make(KeyOrd)

type notation_applicative_status =
  | AppBoundedNotation of int
  | AppUnboundedNotation
  | NotAppNotation

type notation_rule = interp_rule * interpretation * notation_applicative_status

let notation_rule_eq (rule1,pat1,s1 as x1) (rule2,pat2,s2 as x2) =
  x1 == x2 || (rule1 = rule2 && interpretation_eq pat1 pat2 && s1 = s2)

let adjust_application c1 c2 =
  match c1, c2 with
  | NApp (t1, a1), (NList (_,_,NApp (_, a2),_,_) | NApp (_, a2)) when List.length a1 >= List.length a2 ->
      NApp (t1, List.firstn (List.length a2) a1)
  | NApp (t1, a1), _ ->
      t1
  | _ -> c1

let strictly_finer_interpretation_than (_,(_,(vars1,c1),_)) (_,(_,(vars2,c2),_)) =
  let c1 = adjust_application c1 c2 in
  Notation_ops.strictly_finer_notation_constr (List.map fst vars1, List.map fst vars2) c1 c2

let keymap_add key interp map =
  let old = try KeyMap.find key map with Not_found -> [] in
  (* strictly finer interpretation are kept in front *)
  let strictly_finer, rest = List.partition (fun c -> strictly_finer_interpretation_than c interp) old in
  KeyMap.add key (strictly_finer @ interp :: rest) map

let keymap_remove key interp map =
  let old = try KeyMap.find key map with Not_found -> [] in
  KeyMap.add key (List.remove_first (fun (_,rule) -> notation_rule_eq interp rule) old) map

let keymap_find key map =
  try KeyMap.find key map
  with Not_found -> []

(* Scopes table : interpretation -> scope_name *)
(* Boolean = for cases pattern also *)
let notations_key_table = ref (KeyMap.empty : (bool * notation_rule) list KeyMap.t)

let glob_prim_constr_key c = match DAst.get c with
  | GRef (ref, _) -> Some (canonical_gr ref)
  | GApp (c, _) ->
    begin match DAst.get c with
    | GRef (ref, _) -> Some (canonical_gr ref)
    | _ -> None
    end
  | GProj ((cst,_), _, _) -> Some (canonical_gr (GlobRef.ConstRef cst))
  | _ -> None

let glob_constr_keys c = match DAst.get c with
  | GApp (c, _) ->
    begin match DAst.get c with
    | GRef (ref, _) -> [RefKey (canonical_gr ref); Oth]
    | _ -> [Oth]
    end
  | GProj ((cst,_), _, _) -> [RefKey (canonical_gr (GlobRef.ConstRef cst))]
  | GRef (ref,_) -> [RefKey (canonical_gr ref)]
  | _ -> [Oth]

let cases_pattern_key c = match DAst.get c with
  | PatCstr (ref,_,_) -> RefKey (canonical_gr (GlobRef.ConstructRef ref))
  | _ -> Oth

let notation_constr_key = function (* Rem: NApp(NRef ref,[]) stands for @ref *)
  | NApp (NRef (ref,_),args) -> RefKey(canonical_gr ref), AppBoundedNotation (List.length args)
  | NProj ((cst,_),args,_) -> RefKey(canonical_gr (GlobRef.ConstRef cst)), AppBoundedNotation (List.length args + 1)
  | NList (_,_,NApp (NRef (ref,_),args),_,_)
  | NBinderList (_,_,NApp (NRef (ref,_),args),_,_) ->
      RefKey (canonical_gr ref), AppBoundedNotation (List.length args)
  | NRef (ref,_) -> RefKey(canonical_gr ref), NotAppNotation
  | NApp (NList (_,_,NApp (NRef (ref,_),args),_,_), args') ->
      RefKey (canonical_gr ref), AppBoundedNotation (List.length args + List.length args')
  | NApp (NList (_,_,NApp (_,args),_,_), args') ->
      Oth, AppBoundedNotation (List.length args + List.length args')
  | NApp (_,args) -> Oth, AppBoundedNotation (List.length args)
  | NList (_,_,NApp (NVar x,_),_,_) when x = Notation_ops.ldots_var -> Oth, AppUnboundedNotation
  | _ -> Oth, NotAppNotation

let uninterp_notations c =
  List.map_append (fun key -> List.map snd (keymap_find key !notations_key_table))
    (glob_constr_keys c)

let filter_also_for_pattern =
  List.map_filter (function (true,x) -> Some x | _ -> None)

let uninterp_cases_pattern_notations c =
  filter_also_for_pattern (keymap_find (cases_pattern_key c) !notations_key_table)

let uninterp_ind_pattern_notations ind =
  filter_also_for_pattern (keymap_find (RefKey (canonical_gr (GlobRef.IndRef ind))) !notations_key_table)

let remove_uninterpretation rule (metas,c as pat) =
  let (key,n) = notation_constr_key c in
  notations_key_table := keymap_remove key ((rule,pat,n)) !notations_key_table

let declare_uninterpretation ?(also_in_cases_pattern=true) rule (metas,c as pat) =
  let (key,n) = notation_constr_key c in
  notations_key_table := keymap_add key (also_in_cases_pattern,(rule,pat,n)) !notations_key_table

let freeze ~marshallable =
  !notations_key_table

let unfreeze fkm =
  notations_key_table := fkm

let init () =
  notations_key_table := KeyMap.empty

let _ =
  Summary.declare_summary "notation_uninterpretation"
    { stage = Summary.Stage.Interp;
      Summary.freeze_function = freeze;
      Summary.unfreeze_function = unfreeze;
      Summary.init_function = init }

let with_notation_uninterpretation_protection f x =
  let fs = freeze ~marshallable:false in
  try let a = f x in unfreeze fs; a
  with reraise ->
    let reraise = Exninfo.capture reraise in
    let () = unfreeze fs in
    Exninfo.iraise reraise
