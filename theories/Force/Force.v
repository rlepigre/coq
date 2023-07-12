Primitive let_lazy : forall (T : Type) (K : T -> Type) (e : T), (forall v : T, K v) -> K e := #let_lazy.

Primitive Blocked := #blocked_type.
Primitive block : forall (T : Type), T -> Blocked T := #block.
Primitive unblock : forall (T : Type), Blocked T -> T := #unblock.

Arguments let_lazy {_ _} _ _.
Arguments block {_} _.
Arguments unblock {_} _.
