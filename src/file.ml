type 'a t =
  | Defn of 'a * 'a * 'a t Named.Opt.t
  | Data : ('a, 'a, 'a) Telescope.t * (_, 'a Constructor.t, 'a t) Named.Vec.t Named.t -> 'a t
  | Done

let mk_defn : 'a. Binder.t_opt -> 'a -> 'a -> 'a t -> 'a t = fun x t1 t1' t2 ->
  Defn (t1, t1', Named.Opt.Bound (x, t2))
let mk_data : type n. Binder.t -> (n, Binder.t) Vec.t -> ('a, 'a, 'a) Telescope.t -> (n, 'a Constructor.t) Vec.t -> 'a t -> 'a t = fun x xs t cs t' ->
  Data (t, Named.Bound (x, Named.Vec.Bound (cs, (xs, t'))))

let unit : 'a t = Done

let rec mult : 'a t -> 'a t -> 'a t = fun f f' ->
  match f with
  | Defn (t, t', Named.Opt.Bound (x, f)) ->
      Defn (t, t', Named.Opt.Bound (x, mult f f'))
  | Data (t, Named.Bound (x, Named.Vec.Bound (cs, (xs, f)))) ->
      Data (t, Named.Bound (x, Named.Vec.Bound (cs, (xs, mult f f'))))
  | Done -> f'

(*
let associ : 'n 'a 'b. 'a -> ('n, 'a) Vec.t -> ('n, 'b) Vec.t -> (int * 'b) Option.t = fun x xs ys ->
  let rec associ : 'n 'a 'b. int -> 'a -> ('n, 'a) Vec.t -> ('n, 'b) Vec.t -> (int * 'b) Option.t = fun (type n) i x (xs : (n, _) Vec.t) (ys : (n, _) Vec.t) ->
    match xs, ys with
    | Vec.Nil, Vec.Nil                              -> Option.fail
    | Vec.Cons (x', _), Vec.Cons (y, _) when x = x' -> Option.pure (i, y)
    | Vec.Cons (_, xs), Vec.Cons (_, ys)            -> associ (i+1) x xs ys
  in
  associ 0 x xs ys
*)
