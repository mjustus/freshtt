include Context_base

let empty : ('a, 'b) t = Empty
let comma : ('a, 'b) t -> 'a -> ('a, 'b) t = fun t a -> Comma (t, a)
let ortho : ('a, 'b) t -> 'b -> ('a, 'b) t = fun t b -> Ortho (t, b)

let neutral : ('a, 'b) t = Empty
let rec mult : ('a, 'b) t -> ('a, 'b) t -> ('a, 'b) t = fun t t' ->
  match t with
  | Comma (t, a) -> Comma (mult t t', a)
  | Ortho (t, b) -> Ortho (mult t t', b)
  | Empty       -> t'

(*
let rec length_var : _ t -> int = function
  | Empty        -> 0
  | Comma (t, _) -> length_var t + 1
  | Ortho (t, _) -> length_var t

let rec length_name : _ t -> int = function
  | Empty   -> 0
  | Comma (t, _) -> length_name t
  | Ortho (t, _) -> length_name t + 1
*)

let rec map : ('a1 -> 'a2) -> ('b1 -> 'b2) -> ('a1, 'b1) t -> ('a2, 'b2) t = fun f g t ->
  match t with
  | Empty        -> Empty
  | Comma (t, a) -> Comma (map f g t, f a)
  | Ortho (t, b) -> Ortho (map f g t, g b)

let map_right : ('b1 -> 'b2) -> ('a, 'b1) t -> ('a, 'b2) t = fun g ->
  map (fun x -> x) g

let rec lookup_var : ('a, _) t -> Var.t -> 'a Error.String.t = fun t v ->
  match t, v with
  | Empty       , _       -> Error.String.fail "Variable not found in environment."
  | Comma (_, a), Var.Z   -> Error.String.pure a
  | Comma (t, _), Var.V v -> lookup_var t v
  | Ortho (t, _), Var.N v -> lookup_var t v
  | _                     -> Error.String.fail "Ill-kinded environment/variable."

let rec lookup_name : (_, 'b) t -> Name.t -> 'b Error.String.t = fun t n ->
  match t, n with
  | Empty       , _        -> Error.String.fail "Name not found in environment."
  | Ortho (_, b), Name.Z   -> Error.String.pure b
  | Ortho (t, _), Name.N n -> lookup_name t n
  | Comma (t, _), Name.V n -> lookup_name t n
  | _                      -> Error.String.fail "Ill-kinded environment/name."

module Traversable (A : Applicative.S) = struct
  type 'a t = ('a, 'a) Context_base.t

  let rec traverse f t =
    let module Op = Applicative.Op (A) in
    let open Op in
    match t with
    | Empty        -> A.pure Empty
    | Ortho (t, a) -> ortho <$> traverse f t <*> f a
    | Comma (t, a) -> comma <$> traverse f t <*> f a

  module Applicative = A
end

module Traversable2 (A : Applicative.S) = struct
  type ('a, 'b) t = ('a, 'b) Context_base.t

  let rec traverse f g t =
    let module Op = Applicative.Op (A) in
    let open Op in
    match t with
    | Empty        -> A.pure Empty
    | Comma (t, a) -> comma <$> traverse f g t <*> f a
    | Ortho (t, b) -> ortho <$> traverse f g t <*> g b

  module Applicative = A
end

let rec map_option : ('a1 -> 'a2 Option.t) -> ('b1 -> 'b2 Option.t) -> ('a1, 'b1) t -> ('a2, 'b2) t Option.t = fun f g t ->
  let open Option.Operators in
  match t with
  | Empty        -> Option.pure Empty
  | Comma (t, a) -> comma <$> map_option f g t <*> f a
  | Ortho (t, b) -> ortho <$> map_option f g t <*> g b

let map_option_right : ('b1 -> 'b2 Option.t) -> ('a, 'b1) t -> ('a, 'b2) t Option.t = fun g ->
  map_option (fun x -> Option.pure x) g

let rec fold : 'a 'b 'c. 'c -> ('c -> 'a -> 'c) -> ('c -> 'b -> 'c) -> ('a, 'b) t -> 'c = fun f_e f_c f_o t ->
  match t with
  | Empty        -> f_e
  | Comma (t, a) -> f_c (fold f_e f_c f_o t) a
  | Ortho (t, b) -> f_o (fold f_e f_c f_o t) b

let length : 'a 'b. ('a, 'b) t -> int = fun t ->
  fold 0 (fun n _ -> n + 1) (fun n _ -> n + 1) t

(*
module Map_m (M : Monad.MONAD) : sig
  val map_m : ('a1 -> 'a2 M.t) -> ('b1 -> 'b2 M.t) -> ('a1, 'b1) t -> ('a2, 'b2) t M.t
end = struct
  module Op = Monad.Op (M)
  open Op
  
  let rec map_m f g = function
    | Empty        -> M.pure Empty
    | Comma (t, a) -> comma <$> map_m f g t <*> f a
    | Ortho (t, b) -> ortho <$> map_m f g t <*> g b
end
 *)
