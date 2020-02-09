type ('a, 'b) t =
  | Empty
  | Comma of ('a, 'b) t * 'a
  | Ortho of ('a, 'b) t * 'b

