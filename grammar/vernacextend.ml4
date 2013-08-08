(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2012     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

(*i camlp4deps: "tools/compat5b.cmo" i*)

open Pp
open Util
open Q_util
open Argextend
open Tacextend
open Pcoq
open Egramml
open Compat

let rec make_let e = function
  | [] -> e
  | GramNonTerminal(loc,t,_,Some p)::l ->
      let loc = of_coqloc loc in
      let p = Names.Id.to_string p in
      let loc = CompatLoc.merge loc (MLast.loc_of_expr e) in
      let e = make_let e l in
      <:expr< let $lid:p$ = Genarg.out_gen $make_rawwit loc t$ $lid:p$ in $e$ >>
  | _::l -> make_let e l

let check_unicity s l =
  let l' = List.map (fun (_,l,_,_) -> extract_signature l) l in
  if not (Util.List.distinct l') then
    msg_warning
      (strbrk ("Two distinct rules of entry "^s^" have the same "^
      "non-terminals in the same order: put them in distinct vernac entries"))

let make_clause (_,pt,_,e) =
  (make_patt pt,
   vala (Some (make_when (MLast.loc_of_expr e) pt)),
   make_let e pt)

(* To avoid warnings *)
let mk_ignore c pt =
  let names = CList.map_filter (function
  | GramNonTerminal(_,_,_,Some p) -> Some (Names.Id.to_string p)
  | _ -> None) pt in
  let names = List.map (fun n -> <:expr< $lid:n$ >>) names in
  <:expr< do { ignore($list:names$); $c$ } >>

let make_clause_classifier cg s (_,pt,c,_) =
  match c ,cg with
  | Some c, _ ->
     (make_patt pt,
      vala (Some (make_when (MLast.loc_of_expr c) pt)),
      make_let (mk_ignore c pt) pt)
  | None, Some cg ->
     (make_patt pt,
      vala (Some (make_when (MLast.loc_of_expr cg) pt)),
      <:expr< fun () -> $cg$ $str:s$ >>)
  | None, None -> msg_warning
      (strbrk("Vernac entry \""^s^"\" misses a classifier. "^
         "A classifier is a function that returns an expression "^
         "of type vernac_classification (see Vernacexpr). You can: ")++
       str"- "++hov 0 (
        strbrk("Use '... EXTEND "^s^" CLASSIFIED AS QUERY ...' if the "^
          "new vernacular command does not alter the system state;"))++fnl()++
       str"- "++hov 0 (
        strbrk("Use '... EXTEND "^s^" CLASSIFIED AS SIDEFF ...' if the "^
          "new vernacular command alters the system state but not the "^
          "parser nor it starts a proof or ends one;"))++fnl()++
       str"- "++hov 0 (
        strbrk("Use '... EXTEND "^s^" CLASSIFIED BY f ...' to specify "^
          "a global function f.  The function f will be called passing "^
          "\""^s^"\" as the only argument;")) ++fnl()++
       str"- "++hov 0 (
        strbrk"Add a specific classifier in each clause using the syntax:"
        ++fnl()++strbrk("'[...] => [ f ] -> [...]'. "))++fnl()++
       strbrk("Specific classifiers have precedence over global "^
         "classifiers. Only one classifier is called.")++fnl());
    (make_patt pt,
      vala (Some (make_when loc pt)),
      <:expr< fun () -> (Vernacexpr.VtUnknown, Vernacexpr.VtNow) >>)

let make_fun_clauses loc s l =
  check_unicity s l;
  Compat.make_fun loc (List.map make_clause l)

let make_fun_classifiers loc s c l =
  Compat.make_fun loc (List.map (make_clause_classifier c s) l)

let mlexpr_of_clause =
  mlexpr_of_list
    (fun (a,b,_,_) -> mlexpr_of_list make_prod_item
       (Option.List.cons (Option.map (fun a -> GramTerminal a) a) b))

let declare_command loc s c nt cl =
  let se = mlexpr_of_string s in
  let gl = mlexpr_of_clause cl in
  let funcl = make_fun_clauses loc s cl in
  let classl = make_fun_classifiers loc s c cl in
  declare_str_items loc
    [ <:str_item< do {
	try do { 
          Vernacinterp.vinterp_add $se$ $funcl$;
          Vernac_classifier.declare_vernac_classifier $se$ $classl$ }
	with [ e when Errors.noncritical e ->
	  Pp.msg_warning
	    (Pp.app
	       (Pp.str ("Exception in vernac extend " ^ $se$ ^": "))
	       (Errors.print e)) ];
	Egramml.extend_vernac_command_grammar $se$ $nt$ $gl$
      } >> ]

open Pcaml
open PcamlSig

EXTEND
  GLOBAL: str_item;
  str_item:
    [ [ "VERNAC"; "COMMAND"; "EXTEND"; s = UIDENT; c = OPT classification;
        OPT "|"; l = LIST1 rule SEP "|";
        "END" ->
         declare_command loc s c <:expr<None>> l
      | "VERNAC"; nt = LIDENT ; "EXTEND"; s = UIDENT; c = OPT classification;
        OPT "|"; l = LIST1 rule SEP "|";
        "END" ->
          declare_command loc s c <:expr<Some $lid:nt$>> l ] ]
  ;
  classification:
    [ [ "CLASSIFIED"; "BY"; c = LIDENT -> <:expr< $lid:c$ >>
      | "CLASSIFIED"; "AS"; "SIDEFF" ->
          <:expr< fun _ -> Vernac_classifier.classify_as_sideeff >>
      | "CLASSIFIED"; "AS"; "QUERY" ->
          <:expr< fun _ -> Vernac_classifier.classify_as_query >>
    ] ]
  ;
  (* spiwack: comment-by-guessing: it seems that the isolated string (which
      otherwise could have been another argument) is not passed to the
      VernacExtend interpreter function to discriminate between the clauses. *)
  rule:
    [ [ "["; s = STRING; l = LIST0 args; "]";
        c = OPT [ "=>"; "["; c = Pcaml.expr; "]" -> <:expr< fun () -> $c$>> ];
                  "->"; "["; e = Pcaml.expr; "]" ->
      if String.is_empty s then
        Errors.user_err_loc (!@loc,"",Pp.str"Command name is empty.");
      (Some s,l,c,<:expr< fun () -> $e$ >>)
      | "[" ; "-" ; l = LIST1 args ; "]" ;
        c = OPT [ "=>"; "["; c = Pcaml.expr; "]" -> <:expr< fun () -> $c$>> ];
                  "->"; "["; e = Pcaml.expr; "]" ->
      (None,l,c,<:expr< fun () -> $e$ >>)
    ] ]
  ;
  args:
    [ [ e = LIDENT; "("; s = LIDENT; ")" ->
        let t, g = interp_entry_name false None e "" in
        GramNonTerminal (!@loc, t, g, Some (Names.Id.of_string s))
      | e = LIDENT; "("; s = LIDENT; ","; sep = STRING; ")" ->
        let t, g = interp_entry_name false None e sep in
        GramNonTerminal (!@loc, t, g, Some (Names.Id.of_string s))
      | s = STRING ->
        GramTerminal s
    ] ]
  ;
  END
;;
