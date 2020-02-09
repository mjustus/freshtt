type t = E | V of t | N of t | Wv of t | Wn of t

let rec compose : t -> t -> t = fun w w' ->
  match w,  w' with
  | _   , E     -> w
  | V  w, V  w' -> V  (compose w w')
  | Wv w, V  w' -> Wv (compose w w')
  | N  w, N  w' -> N  (compose w w')
  | Wn w, N  w' -> Wn (compose w w')
  | w   , Wv w' -> compose w w'
  | w   , Wn w' -> compose w w'
  | _   , _     -> failwith "Mismatched weakenings."

let rec id : ('a, 'b) Context_base.t -> t = function
  | Context_base.Empty        -> E
  | Context_base.Comma (c, _) -> V (id c)
  | Context_base.Ortho (c, _) -> N (id c)

(*
let rec dom : t -> Context.t = function
  | E    -> Context.Empty
  | V  w
  | Wv w -> Context.Times (dom w)
  | N  w
  | Wn w -> Context.Star  (dom w)

let rec cod : t -> Context.t = function
  | E    -> Context.Empty
  | V  w -> Context.Times (cod w)
  | N  w -> Context.Star  (cod w)
  | Wv w -> cod w
  | Wn w -> cod w
*)

let rec shiftv : t -> t = function
  | V  w -> Wv w
  | Wv w -> Wv (shiftv w)
  | Wn w -> Wn (shiftv w)
  | _ -> failwith "Ill-kinded weakening"

let rec shiftn : t -> t = function
  | N  w -> Wn w
  | Wn w -> Wn (shiftn w)
  | Wv w -> Wv (shiftn w)
  | _ -> failwith "Ill-kinded weakening"

(*
let rec name : t -> int -> int = fun w n ->
  match w, n with
   | Id  , _ -> n
   | V  w, _ -> name w n
   | N  w, 0 -> 0
   | N  w, _ -> (name w (n - 1)) + 1
   | Wv w, _ -> name w n
   | Wn w, _ -> (name w n) + 1

let rec var : t -> int -> int = fun w v ->
  match w, v with
   | Id  , _ -> v
   | V  w, 0 -> 0
   | V  w, _ -> (var w (v - 1)) + 1
   | N  w, _ -> var w v
   | Wv w, _ -> (var w v) + 1
   | Wn w, _ -> var w v
*)

