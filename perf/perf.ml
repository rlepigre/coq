external internal_reset : unit -> unit = "CAML_reset"
external internal_count : unit -> int  = "CAML_count"

exception Error of string

let reset : unit -> unit = fun _ ->
  try internal_reset () with Failure(msg) -> raise (Error(msg))

let count : unit -> int = fun _ ->
  try internal_count () with Failure(msg) -> raise (Error(msg))
