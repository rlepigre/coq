(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Constr
open Environ
open Esubst
open RedFlags

(** Lazy reduction. *)

(** [fconstr] is the type of frozen constr *)

type fconstr
(** [fconstr] can be accessed by using the function [fterm_of] and by
   matching on type [fterm] *)

type finvert

type evar_repack

type usubs = fconstr subs UVars.puniverses

type table_key = Constant.t UVars.puniverses tableKey

(** Relevances (eg in binder_annot or case_info) have NOT been substituted
    when there is a usubs field *)
type fterm =
  | FRel of int
  | FAtom of constr (** Metas and Sorts *)
  | FFlex of table_key
  | FInd of pinductive
  | FConstruct of pconstructor
  | FApp of fconstr * fconstr array
  | FProj of Projection.t * Sorts.relevance * fconstr
  | FFix of fixpoint * usubs
  | FCoFix of cofixpoint * usubs
  | FCaseT of case_info * UVars.Instance.t * constr array * case_return * fconstr * case_branch array * usubs (* predicate and branches are closures *)
  | FCaseInvert of case_info * UVars.Instance.t * constr array * case_return * finvert * fconstr * case_branch array * usubs
  | FLambda of int * (Name.t Context.binder_annot * constr) list * constr * usubs
  | FProd of Name.t Context.binder_annot * fconstr * constr * usubs
  | FLetIn of Name.t Context.binder_annot * fconstr * fconstr * constr * usubs
  | FEvar of Evar.t * constr list * usubs * evar_repack
  | FInt of Uint63.t
  | FFloat of Float64.t
  | FArray of UVars.Instance.t * fconstr Parray.t * fconstr
  | FLIFT of int * fconstr
  | FCLOS of constr * usubs
  | FIrrelevant
  | FLOCKED
  | FPrimitive of CPrimitives.t * pconstant * fconstr * fconstr array
    (* operator, constr def, primitive as an fconstr, full array of suitably evaluated arguments *)
  | FBlock of constr * constr * constr * usubs
    (* @block as a constr, its type as a constr, the contents of the block *)
  | FEta of int * constr * constr array * int * usubs
  (* [FEta (n, h, args, m, e)], represents [FCLOS (mkApp (h, Array.append args [|#1 ... #m|]), e)]. *)
  | FLAZY of fconstr Lazy.t

(***********************************************************************
  s A [stack] is a context of arguments, arguments are pushed by
   [append_stack] one array at a time *)
type 'a next_native_args = (CPrimitives.arg_kind * 'a) list

module [@ocaml.warning "-32"] RedState : sig
  type [@ocaml.immediate] t
  type [@ocaml.immediate] mode
  type [@ocaml.immediate] red_state


  val ntrl : red_state
  val cstr : red_state
  val red  : red_state

  val normal_whnf : mode
  val normal_full : mode
  val full        : mode
  val identity    : mode

  val neutr : t -> t

  val mk : red_state -> mode -> t
  val red_state : t -> red_state
  val mode : t -> mode

  val is_red : t -> bool
  val is_cstr : t -> bool
  val is_ntrl : t -> bool
  val set_red : t -> t
  val set_cstr : t -> t
  val set_ntrl : t -> t
  val neutr : t -> t
  val is_normal_whnf : t -> bool
  val is_normal_full : t -> bool
  val is_full : t -> bool
  val is_identity : t -> bool
  val set_normal_whnf : t -> t
  val set_normal_full : t -> t
  val set_full : t -> t
  val set_identity : t -> t
  val copy_red : t -> t -> t
  val copy_mode : t -> t -> t
end

open RedState

type stack_member =
  | Zapp of fconstr array
  | ZcaseT of case_info * UVars.Instance.t * constr array * case_return * case_branch array * usubs * mode
  | Zproj of Projection.Repr.t * Sorts.relevance * mode
  | Zfix of fconstr * stack
  | Zprimitive of CPrimitives.t * pconstant * fconstr * fconstr list * fconstr next_native_args
       (* operator, constr def, primitive as an fconstr, arguments already seen (in rev order), next arguments *)
  | Zshift of int
  | Zupdate of fconstr
  | Zunblock of constr * constr * usubs * mode
  (* unblock as a constr, its type argument, the substitution for both constrs, saved reduction flags *)
  | Zrun of constr * constr * constr * constr * usubs * mode
  (* run as a constr, its type argument, its continuation, the substitution for all constrs, saved reduction flags *)

and stack = stack_member list

val empty_stack : stack
val append_stack : fconstr array -> stack -> stack

val check_native_args : CPrimitives.t -> stack -> bool

val stack_args_size : stack -> int

val inductive_subst : Declarations.mutual_inductive_body
  -> UVars.Instance.t
  -> fconstr array
  -> usubs

val usubs_lift : usubs -> usubs
val usubs_liftn : int -> usubs -> usubs
val usubs_cons : fconstr -> usubs -> usubs

(** identity if the first instance is empty *)
val usubst_instance : 'a UVars.puniverses -> UVars.Instance.t -> UVars.Instance.t

val usubst_binder : _ UVars.puniverses -> 'a Context.binder_annot -> 'a Context.binder_annot

(** To lazy reduce a constr, create a [clos_infos] with
   [create_clos_infos], inject the term to reduce with [inject]; then use
   a reduction function *)

val inject : constr -> fconstr

(** mk_atom: prevents a term from being evaluated *)
val mk_atom : constr -> fconstr

(** mk_red: makes a reducible term (used in ring) *)
val mk_red : fterm -> fconstr

val fterm_of : fconstr -> fterm
val destFLambda :
  (usubs -> constr -> fconstr) -> fconstr -> Name.t Context.binder_annot * fconstr * fconstr

(** Global and local constant cache *)
type clos_infos
type clos_tab

type 'a evar_expansion =
| EvarDefined of 'a
| EvarUndefined of Evar.t * 'a list

type 'constr evar_handler = {
  evar_expand : 'constr pexistential -> 'constr evar_expansion;
  evar_repack : Evar.t * 'constr list -> 'constr;
  evar_irrelevant : 'constr pexistential -> bool;
  qvar_irrelevant : Sorts.QVar.t -> bool;
}

val default_evar_handler : env -> 'constr evar_handler
val create_conv_infos :
  ?univs:UGraph.t -> ?evars:constr evar_handler -> reds -> env -> clos_infos
val create_clos_infos :
  ?univs:UGraph.t -> ?evars:constr evar_handler -> reds -> env -> clos_infos
val oracle_of_infos : clos_infos -> Conv_oracle.oracle

val create_tab : unit -> clos_tab

val info_env : clos_infos -> env
val info_flags: clos_infos -> reds
val info_univs : clos_infos -> UGraph.t
val unfold_projection : clos_infos -> Projection.t -> Sorts.relevance -> stack_member option

val push_relevance : clos_infos -> 'b Context.binder_annot -> clos_infos
val push_relevances : clos_infos -> 'b Context.binder_annot array -> clos_infos
val set_info_relevances : clos_infos -> Sorts.relevance Range.t -> clos_infos

val info_relevances : clos_infos -> Sorts.relevance Range.t

val is_irrelevant : clos_infos -> Sorts.relevance -> bool

val infos_with_reds : clos_infos -> reds -> clos_infos

val term_of_fconstr : info:clos_infos -> tab:clos_tab -> fconstr -> constr

(** Reduction function *)

(** [norm_val] is for strong normalization *)
val norm_val : clos_infos -> clos_tab -> fconstr -> constr

(** Same as [norm_val] but for terms *)
val norm_term : ?mode:mode -> clos_infos -> clos_tab -> usubs -> Constr.constr -> Constr.constr

(** [whd_val] is for weak head normalization *)
val whd_val : clos_infos -> clos_tab -> fconstr -> constr

(** [whd_stack] performs weak head normalization in a given stack. It
   stops whenever a reduction is blocked. *)
val whd_stack :
  clos_infos -> clos_tab -> fconstr -> stack -> fconstr * stack

val skip_irrelevant_stack : clos_infos -> stack -> stack

val eta_expand_stack : clos_infos -> Name.t Context.binder_annot -> stack -> stack

val mk_eta_args : constr array -> int -> constr array
val eta_reduce : fconstr -> fconstr

(** [eta_expand_ind_stack env ind c s t] computes stacks corresponding
    to the conversion of the eta expansion of t, considered as an inhabitant
    of ind, and the Constructor c of this inductive type applied to arguments
    s.
    Assumes [t] is a rigid term, and not a constructor. [ind] is the inductive
    of the constructor term [c]
    @raise Not_found if the inductive is not a primitive record, or if the
    constructor is partially applied.
 *)
val eta_expand_ind_stack : env -> pinductive -> fconstr -> stack ->
   (fconstr * stack) -> stack * stack

(** Conversion auxiliary functions to do step by step normalisation *)

(** Like [unfold_reference], but handles primitives: if there are not
    enough arguments, return [None]. Otherwise return [Some] with
    [ZPrimitive] added to the stack. Produces a [FIrrelevant] when the
    reference is irrelevant and the infos was created with
    [create_conv_infos]. *)
val unfold_ref_with_args
  : clos_infos
  -> clos_tab
  -> table_key
  -> stack
  -> (fconstr * stack) option

(** Hook for Reduction *)
val set_conv : (clos_infos -> clos_tab -> fconstr -> fconstr -> bool) -> unit

(***********************************************************************
  i This is for lazy debug *)

val lift_fconstr      : int -> fconstr -> fconstr
val lift_fconstr_vect : int -> fconstr array -> fconstr array

val mk_clos      : usubs -> constr -> fconstr
val mk_clos_vect : usubs -> constr array -> fconstr array

val kni: clos_infos -> clos_tab -> fconstr -> stack -> fconstr * stack
val knr: clos_infos -> clos_tab -> fconstr -> stack -> fconstr * stack
val kl : clos_infos -> clos_tab -> fconstr -> constr

val zip : fconstr -> stack -> fconstr

val term_of_process : info:clos_infos -> tab:clos_tab -> fconstr -> stack -> constr

val to_constr : info:clos_infos -> tab:clos_tab -> lift UVars.puniverses -> fconstr -> constr

(** End of cbn debug section i*)
