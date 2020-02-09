type t =
  | Defn of t * Binder.t_opt * (Model.t * Model.t)
  | Data of t * Binder.t     * (Model.telescope * Model.constructor list * (Term.level -> Term.t) * Term.t list)
  | Done

let mk_defn : Binder.t_opt -> Model.t -> Model.t -> t -> t = fun x t t' f ->
  Defn (f, x, (t, t'))

let mk_data : type n. Binder.t -> Model.telescope -> (n, Model.constructor) Vec.t -> (int -> Term.t) -> (n, Term.t) Vec.t -> t -> t = fun x t cs te tm f ->
  Data (f, x, (t, Vec.to_list cs, te, Vec.to_list tm))

type result =
  | R_defn of Model.t * Model.t
  | R_data of Model.telescope * Model.constructor list * (Term.level -> Term.t) * Term.t list

let associ : 'a 'b. 'a -> ('a * 'b) list -> (int * 'b) Option.t = fun x ys ->
  let rec associ : 'a 'b. int -> 'a -> ('a * 'b) list -> (int * 'b) Option.t = fun i x ys ->
    match ys with
    | []                     -> Option.fail
    | (y, a) :: _ when x = y -> Option.pure (i, a)
    | _      :: ys           -> associ (i+1) x ys
  in
  associ 0 x ys

module Op = Monad.Op (Option)
open Op

let rec lookup : Binder.t -> t -> result Option.t = fun x f ->
  match f with
  | Defn (_, Some y, (t, t')) when x = y ->
      Option.pure @@ R_defn (t, t')
  | Data (_,      y, (t, cs, tr, tm)) when x = y ->
      Option.pure @@ R_data (t, cs, tr, tm)
  | Data (f, _, _)
  | Defn (f, _, _) -> lookup x f
  | Done -> Option.fail

let lookup_def : Binder.t -> t -> (Model.t * Model.t) Option.t = fun x f ->
  lookup x f >>= function
  | R_defn (t, t') -> Option.pure (t, t')
  | _              -> Option.fail

let lookup_tcn : Binder.t -> t -> Model.telescope Option.t = fun x f ->
  lookup x f >>= function
  | R_data (t, _, _, _) -> Option.pure t
  | _                   -> Option.fail

let lookup_tcn_length : Binder.t -> t -> int Option.t = fun x f ->
  let telescope_length : Model.telescope -> int = function
    | Model.Telescope.Fn (_, (_, t, _)) -> Telescope.fold (fun _ _ -> (+) 1) (fun _ _ -> (+) 1) (fun _ -> 0) t + 1
    | Model.Telescope.Na (_, (_, t, _)) -> Telescope.fold (fun _ _ -> (+) 1) (fun _ _ -> (+) 1) (fun _ -> 0) t+ 1
    | Model.Telescope.Up _              -> 0
  in
  lookup x f >>= function
  | R_data (t, _, _, _) -> Option.pure @@ (telescope_length t)
  | _                   -> Option.fail

let lookup_dcn : Binder.t -> int -> t -> Model.constructor Option.t = fun x i f ->
  lookup x f >>= function
  | R_data (_, c, _, _) -> Option.pure @@ (List.nth c i)
  | _                   -> Option.fail

let lookup_dcn_length : Binder.t -> t -> int Option.t = fun x f ->
  lookup x f >>= function
  | R_data (_, c, _, _) -> Option.pure @@ (List.length c)
  | _                   -> Option.fail

let lookup_elim : Binder.t -> t -> (int -> Term.t) Option.t = fun x f ->
  lookup x f >>= function
  | R_data (_, _, r, _) -> Option.pure @@ r
  | _                   -> Option.fail

let lookup_method : Binder.t -> int -> t -> Term.t Option.t = fun x i f ->
  lookup x f >>= function
  | R_data (_, _, _, m) -> Option.pure @@ (List.nth m i)
  | _                   -> Option.fail
