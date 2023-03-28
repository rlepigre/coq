exception NotSupported
exception Error of string

let reset : unit -> unit = fun _ -> raise NotSupported
let count : unit -> int  = fun _ -> raise NotSupported
