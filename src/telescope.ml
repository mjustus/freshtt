type ('a1, 'a2, 'b) t =
  | Fn of 'a1 * ('a1, 'a2, 'b) t Debruijn.var
  | Na of 'a2 * ('a1, 'a2, 'b) t Debruijn.name
  | Up of 'b

let mk_fn : 'a1 'a2 'b. 'a1 -> Binder.t_opt -> ('a1, 'a2, 'b) t -> ('a1, 'a2, 'b) t = fun x i t -> Fn (x, Debruijn.V (i, t))
let mk_na : 'a1 'a2 'b. 'a2 -> Binder.t_opt -> ('a1, 'a2, 'b) t -> ('a1, 'a2, 'b) t = fun x i t -> Na (x, Debruijn.N (i, t))
let mk_up : 'a1 'a2 'b. 'b -> ('a1, 'a2, 'b) t = fun x -> Up x

let rec fold : 'a1 'a2 'b 'd. ('a1 -> Binder.t_opt -> 'd -> 'd) -> ('a2 -> Binder.t_opt -> 'd -> 'd) -> ('b -> 'd) -> ('a1, 'a2, 'b) t -> 'd = fun f g h t ->
  match t with
  | Fn (a1, Debruijn.V (x, t)) -> f a1 x (fold f g h t)
  | Na (a2, Debruijn.N (x, t)) -> g a2 x (fold f g h t)
  | Up b       -> h b

let rec map : 'a1 'a2 'b1 'b2 'c1 'c2. ('a1 -> 'a2) -> ('b1 -> 'b2) -> ('c1 -> 'c2) -> ('a1, 'b1, 'c1) t -> ('a2, 'b2, 'c2) t = fun f g h t ->
  match t with
  | Fn (a, Debruijn.V (x, t)) -> Fn (f a, Debruijn.V (x, map f g h t))
  | Na (b, Debruijn.N (x, t)) -> Na (g b, Debruijn.N (x, map f g h t))
  | Up c                      -> Up (h c)

let map_uniform : 'a. ('a -> 'a) -> ('a, 'a, 'a) t -> ('a, 'a, 'a) t = fun f ->
  map f f f

let to_up : (_, _, 'b) t -> 'b = fun t ->
  fold (fun _ _ t -> t) (fun _ _ t -> t) Function.id t

let length : 'a 'b 'c. ('a, 'b, 'c) t -> int = fun t ->
  fold (fun _ _ -> (+) 1) (fun _ _ -> (+) 1) (fun _ -> 0) t

let rec wkv : (Var.t -> 'a -> 'a) -> (Var.t -> 'b -> 'b) -> (Var.t -> 'c -> 'c) -> Var.t -> ('a, 'b, 'c) t -> ('a, 'b, 'c) t = fun wkv_a wkv_b wkv_c v t ->
  match t with
  | Fn (a, Debruijn.V (x, t)) -> Fn (wkv_a v a, Debruijn.V (x, wkv wkv_a wkv_b wkv_c (Var.V v) t))
  | Na (b, Debruijn.N (x, t)) -> Na (wkv_b v b, Debruijn.N (x, wkv wkv_a wkv_b wkv_c (Var.N v) t))
  | Up c                      -> Up (wkv_c v c)
