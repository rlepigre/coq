exception Error of string

(** [reset ()] resets the instruction counter to 0, and immediately starts the
    counter. Note that upon the first call to this function, the counter state
    is also initialised (prior to starting the counter). In case of error, the
    function raises the [Error] exception. *)
val reset : unit -> unit

(** [count ()] stops the instruction counter, and returns its value. Note that
    this function can be called at most once each [reset ()] call, and it must
    be called to be able to call [reset ()] again. The function raises [Error]
    in case of error. *)
val count : unit -> int
