(* To run: [dune build theories/Force && dune exec -- dev/shim/coqc test.v] *)

Require Import Force.Force.

(**** UNIVERSES ****)

Definition check_let_lazy@{u1 u2} : forall (T : Type@{u1}) (K : T -> Type@{u2}) (e : T), (forall v : T, K v) -> K e := @let_lazy.
Definition check_Blocked@{u} : Type@{u} -> Type@{u} := Blocked.
Definition check_block@{u} : forall (T : Type@{u}), T -> Blocked@{u} T := @block.
Definition check_unblock@{u} : forall (T : Type@{u}), Blocked@{u} T -> T := @unblock.

(**** EVALUATION ****)

Ltac syn_refl := lazymatch goal with |- ?t = ?t => exact eq_refl end.
Notation SIMPL t := (ltac:(let x := eval simpl in t in exact x)) (only parsing).
Notation LAZY t := (ltac:(let x := eval lazy  in t in exact x)) (only parsing).
Notation HNF t := (ltac:(let x := eval hnf in t in exact x)) (only parsing).
Notation CBN t := (ltac:(let x := eval cbn in t in exact x)) (only parsing).
Notation CBV t := (ltac:(let x := eval cbv in t in exact x)) (only parsing).
Notation VM_COMPUTE t := (ltac:(let x := eval vm_compute in t in exact x)) (only parsing).
Notation NATIVE_COMPUTE t := (ltac:(let x := eval native_compute in t in exact x)) (only parsing).

Goal SIMPL (let_lazy (1 + 1) (fun x => x + x)) = 4.
Proof. syn_refl. Qed.

Goal SIMPL (let_lazy (1 + 1) (fun x => x + x)) = 4.
Proof. syn_refl. Qed.

Goal LAZY (let_lazy (1 + 1) (fun x => x + x)) = 4.
Proof. syn_refl. Qed.

Goal HNF (let_lazy (1 + 1) (fun x => x + x)) = S (0 + 1 + (1 + 1)).
Proof. syn_refl. Qed.

Goal CBN (let_lazy (1 + 1) (fun x => x + x)) = 4.
Proof. syn_refl. Qed.

(* FIXME: not implemented. *)
(*Goal CBV (let_lazy (1 + 1) (fun x => x + x)) = 4.*)
(*Proof. syn_refl. Qed.*)

(* FIXME: not implemented. *)
(*Goal VM_COMPUTE (let_lazy (1 + 1) (fun x => x + x)) = 4.*)
(*Proof. syn_refl. Qed.*)

(* FIXME: not implemented. *)
(*Goal NATIVE_COMPUTE (let_lazy (1 + 1) (fun x => x + x)) = 4.*)
(*Proof. syn_refl. Qed.*)

(**** TEST ****)

Axiom F : let_lazy (1 + 1) (fun x => forall y, y = x).
Goal True. let t := constr:(F 0) in match type of t with 0 = 2 => idtac end. Abort.

Axiom G : let x := 1 + 1 in forall y, y = x.
Goal True. let t := constr:(G 0) in match type of t with 0 = 1 + 1 => idtac end. Abort.

Axiom H : (fun x => forall y, y = x) (1 + 1).
Goal True. let t := constr:(H 0) in match type of t with 0 = 1 + 1 => idtac end. Abort.

(**** BLOCKED ****)

Goal LAZY (block (2 + 2)) = block (2 + 2).
Proof. syn_refl. Qed.

Goal LAZY (unblock (block 42)) = 42.
Proof. syn_refl. Qed.

Goal LAZY (block (fun x => (2 + 2) + x)) = block (fun x => (2 + 2) + x).
Proof. syn_refl. Qed.

Goal LAZY (unblock (block (fun x => (2 + 2) + x))) = fun x => S (S (S (S x))).
Proof. syn_refl. Qed.

Goal HNF (block (2 + 2)) = block (2 + 2).
Proof. syn_refl. Qed.

Goal SIMPL (block (2 + 2)) = block 4. (* FIXME? *)
Proof. syn_refl. Qed.

Goal CBN (block (2 + 2)) = block 4. (* FIXME? *)
Proof. syn_refl. Qed.
