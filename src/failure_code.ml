type t =
  | NOT_FRESH_TYPE
  | NOT_FRESH_TERM
  | NOT_EQUIV
  | NOT_SUB_TYPE
  | NOT_FUN
  | NOT_NAB
  | NOT_UNV
  | NEG_UNV_LEVEL
  | NOT_SUB_UNV
  | UNBOUND_VAR
  | UNBOUND_NAME
  | UNBOUND_REC
  | UNBOUND_TCN

let to_string : t -> string = fun t ->
  match t with
  | NOT_FRESH_TYPE -> "NOT_FRESH_TYPE"
  | NOT_FRESH_TERM -> "NOT_FRESH_TERM"
  | NOT_EQUIV      -> "NOT_EQUIV"
  | NOT_SUB_TYPE   -> "NOT_SUB_TYPE"
  | NOT_FUN        -> "NOT_FUN"
  | NOT_NAB        -> "NOT_NAB"
  | NOT_UNV        -> "NOT_UNV"
  | NEG_UNV_LEVEL  -> "NEG_UNV_LEVEL"
  | NOT_SUB_UNV    -> "NOT_SUB_UNV"
  | UNBOUND_VAR    -> "UNBOUND_VAR"
  | UNBOUND_NAME   -> "UNBOUND_NAME"
  | UNBOUND_REC    -> "UNBOUND_REC"
  | UNBOUND_TCN    -> "UNBOUND_TCN"
