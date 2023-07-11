Primitive let_lazy : forall (T K : Type), T -> (T -> K) -> K := #let_lazy.

Primitive Blocked := #blocked_type.
Primitive block : forall (T : Type), T -> Blocked T := #block.
Primitive unblock : forall (T : Type), Blocked T -> T := #unblock.
