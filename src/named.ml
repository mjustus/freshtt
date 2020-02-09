type 'a t = Bound of Binder.t * 'a
let bind : Binder.t -> 'a -> 'a t = fun x a -> Bound (x, a)
let body : 'a t -> 'a = function Bound (_, a) -> a

module Opt = struct
  type 'a t = Bound of Binder.t_opt * 'a
  let bind : Binder.t_opt -> 'a -> 'a t = fun x a -> Bound (x, a)
  let body : 'a t -> 'a = function Bound (_, a) -> a
end

module List = struct
  type ('a, 'b) t = Bound of (Binder.t * 'a) list * 'b

  let bind : (Binder.t * 'a) list -> 'b -> ('a, 'b) t = fun xs a -> Bound (xs, a)
  let body : ('a, 'b) t -> 'b = function Bound (_, a) -> a
  let identifiers : ('a, 'b) t -> Binder.t list = function
    | Bound (xs, _) -> List.map fst xs
end

module Vec = struct
  type ('n, 'a, 'b) t = Bound of ('n, 'a) Vec.t * (('n, Binder.t) Vec.t * 'b)

  let bind : 'n. ('n, Binder.t) Vec.t -> ('n, 'a) Vec.t -> 'b -> ('n, 'a, 'b) t = fun is xs a -> Bound (xs, (is, a))
  let body : 'n. ('n, 'a, 'b) t -> 'b = function Bound (_, (_, a)) -> a
  let identifiers : 'n. ('n, 'a, 'b) t -> ('n, Binder.t) Vec.t = function
    | Bound (_, (is, _)) -> is
end


module Mult_opt = struct
  type 'a t = Bound of Binder.t_nlist_opt * 'a
  let bind : Binder.t_nlist_opt -> 'a -> 'a t = fun x a -> Bound (x, a)
  let unbind : 'a t -> Binder.t_nlist_opt * 'a = function Bound (x, a) -> (x, a)
  let body : 'a t -> 'a = function Bound (_, a) -> a
end

