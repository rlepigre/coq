(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2018       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Pp
open CErrors

type 'a vernac_command = 'a -> atts:Vernacexpr.vernac_flags -> st:Vernacstate.t -> Vernacstate.t

type plugin_args = Genarg.raw_generic_argument list

(* Table of vernac entries *)
let vernac_tab =
  (Hashtbl.create 211 :
    (Vernacexpr.extend_name, bool * plugin_args vernac_command) Hashtbl.t)

let vinterp_add depr s f =
  try
    Hashtbl.add vernac_tab s (depr, f)
  with Failure _ ->
    user_err ~hdr:"vinterp_add"
      (str"Cannot add the vernac command " ++ str (fst s) ++ str" twice.")

let vinterp_map s =
  try
    Hashtbl.find vernac_tab s
  with Failure _ | Not_found ->
    user_err ~hdr:"Vernac Interpreter"
      (str"Cannot find vernac command " ++ str (fst s) ++ str".")

let warn_deprecated_command =
  let open CWarnings in
  create ~name:"deprecated-command" ~category:"deprecated"
         (fun pr -> str "Deprecated vernacular command: " ++ pr)

(* Interpretation of a vernac command *)

let call opn converted_args ~atts ~st =
  let phase = ref "Looking up command" in
  try
    let depr, callback = vinterp_map opn in
    let () = if depr then
      let rules = Egramml.get_extend_vernac_rule opn in
      let pr_gram = function
      | Egramml.GramTerminal s -> str s
      | Egramml.GramNonTerminal _ -> str "_"
      in
      let pr = pr_sequence pr_gram rules in
      warn_deprecated_command pr;
    in
    phase := "Checking arguments";
    let hunk = callback converted_args in
    phase := "Executing command";
    hunk ~atts ~st
  with
    | reraise ->
        let reraise = CErrors.push reraise in
        if !Flags.debug then
          Feedback.msg_debug (str"Vernac Interpreter " ++ str !phase);
        iraise reraise

(** VERNAC EXTEND registering *)

type classifier = Genarg.raw_generic_argument list -> Vernacexpr.vernac_classification

type (_, _) ty_sig =
| TyNil : (atts:Vernacexpr.vernac_flags -> st:Vernacstate.t -> Vernacstate.t, Vernacexpr.vernac_classification) ty_sig
| TyTerminal : string * ('r, 's) ty_sig -> ('r, 's) ty_sig
| TyNonTerminal : ('a, 'b, 'c) Extend.ty_user_symbol * ('r, 's) ty_sig -> ('a -> 'r, 'a -> 's) ty_sig

type ty_ml = TyML : bool * ('r, 's) ty_sig * 'r * 's option -> ty_ml

let type_error () = CErrors.anomaly (Pp.str "Ill-typed VERNAC EXTEND")

let rec untype_classifier : type r s. (r, s) ty_sig -> s -> classifier = function
| TyNil -> fun f args ->
  begin match args with
  | [] -> f
  | _ :: _ -> type_error ()
  end
| TyTerminal (_, ty) -> fun f args -> untype_classifier ty f args
| TyNonTerminal (tu, ty) -> fun f args ->
  let open Genarg in
  begin match args with
  | [] -> type_error ()
  | GenArg (Rawwit tag, v) :: args ->
    match Genarg.genarg_type_eq tag (Egramml.proj_symbol tu) with
    | None -> type_error ()
    | Some Refl -> untype_classifier ty (f v) args
  end

(** Stupid GADTs forces us to duplicate the definition just for typing *)
let rec untype_command : type r s. (r, s) ty_sig -> r -> plugin_args vernac_command = function
| TyNil -> fun f args ->
  begin match args with
  | [] -> f
  | _ :: _ -> type_error ()
  end
| TyTerminal (_, ty) -> fun f args -> untype_command ty f args
| TyNonTerminal (tu, ty) -> fun f args ->
  let open Genarg in
  begin match args with
  | [] -> type_error ()
  | GenArg (Rawwit tag, v) :: args ->
    match genarg_type_eq tag (Egramml.proj_symbol tu) with
    | None -> type_error ()
    | Some Refl -> untype_command ty (f v) args
  end

let rec untype_user_symbol : type s a b c. (a, b, c) Extend.ty_user_symbol -> (s, a) Extend.symbol =
  let open Extend in function
| TUlist1 l -> Alist1 (untype_user_symbol l)
| TUlist1sep (l, s) -> Alist1sep (untype_user_symbol l, Atoken (CLexer.terminal s))
| TUlist0 l -> Alist0 (untype_user_symbol l)
| TUlist0sep (l, s) -> Alist0sep (untype_user_symbol l, Atoken (CLexer.terminal s))
| TUopt o -> Aopt (untype_user_symbol o)
| TUentry a -> Aentry (Pcoq.genarg_grammar (Genarg.ExtraArg a))
| TUentryl (a, i) -> Aentryl (Pcoq.genarg_grammar (Genarg.ExtraArg a), string_of_int i)

let rec untype_grammar : type r s. (r, s) ty_sig -> Vernacexpr.vernac_expr Egramml.grammar_prod_item list = function
| TyNil -> []
| TyTerminal (tok, ty) -> Egramml.GramTerminal tok :: untype_grammar ty
| TyNonTerminal (tu, ty) ->
  let t = Genarg.rawwit (Egramml.proj_symbol tu) in
  let symb = untype_user_symbol tu in
  Egramml.GramNonTerminal (Loc.tag (t, symb)) :: untype_grammar ty

let _ = untype_classifier, untype_command, untype_grammar, untype_user_symbol

let classifiers : classifier array String.Map.t ref = ref String.Map.empty

let get_vernac_classifier (name, i) args =
  (String.Map.find name !classifiers).(i) args

let declare_vernac_classifier name f =
  classifiers := String.Map.add name f !classifiers

let vernac_extend ~command ?classifier ?entry ext =
  let get_classifier (TyML (_, ty, _, cl)) = match cl with
  | Some cl -> untype_classifier ty cl
  | None ->
    match classifier with
    | Some cl -> fun _ -> cl command
    | None ->
      let e = match entry with
      | None -> "COMMAND"
      | Some e -> Pcoq.Gram.Entry.name e
      in
      let msg = Printf.sprintf "\
        Vernac entry \"%s\" misses a classifier. \
        A classifier is a function that returns an expression \
        of type vernac_classification (see Vernacexpr). You can: \n\
        - Use '... EXTEND %s CLASSIFIED AS QUERY ...' if the \
          new vernacular command does not alter the system state;\n\
        - Use '... EXTEND %s CLASSIFIED AS SIDEFF ...' if the \
          new vernacular command alters the system state but not the \
          parser nor it starts a proof or ends one;\n\
        - Use '... EXTEND %s CLASSIFIED BY f ...' to specify \
          a global function f.  The function f will be called passing\
          \"%s\" as the only argument;\n\
        - Add a specific classifier in each clause using the syntax:\n\
          '[...] => [ f ] -> [...]'.\n\
        Specific classifiers have precedence over global \
        classifiers. Only one classifier is called."
          command e e e command
      in
      CErrors.user_err (Pp.strbrk msg)
  in
  let cl = Array.map_of_list get_classifier ext in
  let iter i (TyML (depr, ty, f, _)) =
    let f = untype_command ty f in
    let r = untype_grammar ty in
    let () = vinterp_add depr (command, i) f in
    Egramml.extend_vernac_command_grammar (command, i) entry r
  in
  let () = declare_vernac_classifier command cl in
  List.iteri iter ext

(** VERNAC ARGUMENT EXTEND registering *)

type 'a argument_rule =
| Arg_alias of 'a Pcoq.Entry.t
| Arg_rules of 'a Extend.production_rule list

type 'a vernac_argument = {
  arg_printer : 'a -> Pp.t;
  arg_parsing : 'a argument_rule;
}

let vernac_argument_extend ~name arg =
  let wit = Genarg.create_arg name in
  let entry = match arg.arg_parsing with
  | Arg_alias e ->
    let () = Pcoq.register_grammar wit e in
    e
  | Arg_rules rules ->
    let e = Pcoq.create_generic_entry Pcoq.utactic name (Genarg.rawwit wit) in
    let () = Pcoq.grammar_extend e None (None, [(None, None, rules)]) in
    e
  in
  let pr = arg.arg_printer in
  let pr x = Genprint.PrinterBasic (fun () -> pr x) in
  let () = Genprint.register_vernac_print0 wit pr in
  (wit, entry)
