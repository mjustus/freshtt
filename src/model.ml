(* TODO: name type annotation for nu's? *)

type level = int

type t_nf =
  | Dwn of t * t
and s = (t, t * Name.t) Context.t
and t =
  | Unv of level
  | Nst
  | Fun of t * t
  | Nab of t * t
  | Nam of t * Name.t
  | New of t_nu
and t_nu =
  | Nu of t * t_nu Debruijn.name
  (* | Nu of Term.t * s *)
  | Vl of t_vl
and t_vl =
  | Cls of Binder.t_opt * Term.t * s
  | Alp of Binder.t_opt * Term.t * s
  | Tcn of Binder.t *       (t, t * Name.t) Spine.t
  | Dcn of Binder.t * int * (t, t * Name.t) Spine.t
  (* Partially applied eliminator waiting for the motive. *)
  | Rmo of Binder.t * int
  (* Partially applied eliminator waiting for further methods and a target. *)
  | Rme of Binder.t * int * t * t list
  (* Partially applied eliminator waiting for further indices and a target. *)
  | Rid of Binder.t * int * t * t list * (t, t * Name.t) Spine.t
  | Up  of t * t_ne
and t_ne =
  | Var of Table.t * Var.t
  | App of t_ne * t_nf
  | Cnc of t_ne * Name.t
  (* Eliminator applied to a neutral target. *)
  | Rne of Binder.t * int * t * t list * (t, t * Name.t) Spine.t * t_ne
  | Cmp of Name.t * t_ne

type spine = (t, t * Name.t) Spine.t

module Telescope = struct
  type ('a1, 'a2, 'b, 'c) t =
    | Fn of 'a1 * (Binder.t_opt * 'b * s)
    | Na of 'a2 * (Binder.t_opt * 'b * s)
    | Up of 'c
end

type telescope = (t, t, Term.telescope, t) Telescope.t
(*
  | Fn of t * (Binder.t_opt * Term.telescope * s)
  | Na of t * (Binder.t_opt * Term.telescope * s)
  | Up of t
*)

type constructor = ((t, (t, t, Term.t Constructor.arg_rec, spine) Telescope.t) Sum.t, t, Term.constructor, spine) Telescope.t

let telescope_to_term : telescope -> t = function
  | Telescope.Fn (t, (x, t', s)) -> Fun (t, New (Vl (Cls (x, Term.telescope_abs Function.id t', s))))
  | Telescope.Na (t, (x, t', s)) -> Nab (t, New (Vl (Alp (x, Term.telescope_abs Function.id t', s))))
  | Telescope.Up t               -> t

let constructor_to_term_arg : Binder.t -> (t, t, Term.t Constructor.arg_rec, spine) Telescope.t -> t = fun x t ->
  match t with
  | Telescope.Fn (t, (y, t', s)) -> Fun (t, New (Vl (Cls (y, Term.arg_rec x t', s))))
  | Telescope.Na (t, (y, t', s)) -> Nab (t, New (Vl (Alp (y, Term.arg_rec x t', s))))
  | Telescope.Up s               -> New (Vl (Tcn (x, s)))

let constructor_to_term : Binder.t -> constructor -> t = fun x t ->
  match t with
  | Telescope.Fn (Sum.Inl t, (y, t', s)) -> Fun (t, New (Vl (Cls (y, Term.constructor_type x t', s))))
  | Telescope.Fn (Sum.Inr t, (y, t', s)) -> Fun (constructor_to_term_arg x t, New (Vl (Cls (y, Term.constructor_type x t', s))))
  | Telescope.Na (t        , (y, t', s)) -> Nab (t, New (Vl (Alp (y, Term.constructor_type x t', s))))
  | Telescope.Up s                       -> New (Vl (Tcn (x, s)))

type file =
  | Defn of t * t * file Named.Opt.t
  | Data : telescope * (_, constructor, file) Named.Vec.t Named.t -> file
  | Done

let mk_defn : Binder.t_opt -> t -> t -> file -> file = fun x t t' f -> Defn (t, t', Named.Opt.Bound (x, f))
let mk_data : type n. Binder.t -> (n, Binder.t) Vec.t -> telescope -> (n, _) Vec.t -> file -> file = fun x xs t cs f -> Data (t, Named.Bound (x, Named.Vec.Bound (cs, (xs, f))))

let comma : s -> t -> s = Context.comma
let ortho : s -> t -> Name.t -> s = fun s t n -> Context.ortho s (t, n)
      
let mk_dwn : t -> t -> t_nf = fun t t' -> Dwn (t, t')
let mk_nu : t -> t_nu Debruijn.name -> t_nu = fun t t' -> Nu (t, t')
(* let nu : Term.t -> s -> t = fun t s -> Nu (t, s) *)
let mk_vl : t_vl -> t_nu = fun t -> Vl t
let mk_unv : level -> t = fun l -> Unv l
let mk_pi : t -> t -> t = fun t t' -> Fun (t, t')
let mk_cls : Binder.t_opt -> Term.t -> s -> t_vl = fun x t s -> Cls (x, t, s)
let mk_nst : t = Nst
let mk_nam : t -> Name.t -> t = fun t a -> Nam (t, a)
let mk_nab : t -> t -> t = fun t t' -> Nab (t, t')
let mk_alp : Binder.t_opt -> Term.t -> s -> t_vl = fun x t s -> Alp (x, t, s)
let mk_up  : t -> t_ne -> t_vl = fun t t' -> Up (t, t')
let mk_var : Table.t -> Var.t -> t_ne = fun p v -> Var (p, v)
let mk_app : t_ne -> t_nf -> t_ne = fun t t' -> App (t, t')
let mk_cnc : t_ne -> Name.t -> t_ne = fun t n -> Cnc (t, n)

let unv_syn : t = Unv (-1)

let rec wkn_s : Name.t -> s -> s = fun n ->
  Context.map (wkn n) (fun (t, m) -> (wkn n t, Name.wkn n m))
and wkn_nf : Name.t -> t_nf -> t_nf = fun n t ->
  match t with
  | Dwn (t, t') -> Dwn (wkn n t, wkn n t')
and wkn_ne : Name.t -> t_ne -> t_ne = fun n t ->
  match t with
  | Var (p, v )               -> Var (Table.wkn n p, Var.wkn n v)
  | App (t, t')               -> App (wkn_ne n t, wkn_nf n t')
  | Cnc (t, m )               -> Cnc (wkn_ne n t, Name.wkn n m)
  | Rne (x, l, t, tm, ti, t') -> Rne (x, l, wkn n t, List.map (wkn n) tm, wkn_spine n ti, wkn_ne n t')
  | Cmp (m, t)                -> Cmp (Name.wkn n m, wkn_ne n t)
and wkn : Name.t -> t -> t = fun n t ->
  match t with
  | Nst | Unv _ -> t
  | Fun (t, t') -> Fun (wkn n t, wkn n t')
  | Nab (t, t') -> Nab (wkn n t, wkn n t')
  | Nam (t, m ) -> Nam (wkn n t, Name.wkn n m)
  | New t       -> New (wkn_nu n t)
and wkn_vl : Name.t -> t_vl -> t_vl = fun n t ->
  match t with
  | Cls (x, t, s )        -> Cls (x, t, wkn_s n s)
  | Alp (x, t, s )        -> Alp (x, t, wkn_s n s)
  | Tcn (x, t)            -> Tcn (x,    wkn_spine n t)
  | Dcn (x, i, t)         -> Dcn (x, i, wkn_spine n t)
  | Rmo (x, l)            -> Rmo (x, l)
  | Rme (x, l, t, tm)     -> Rme (x, l, wkn n t, List.map (wkn n) tm)
  | Rid (x, l, t, tm, ti) -> Rid (x, l, wkn n t, List.map (wkn n) tm, wkn_spine n ti)
  | Up  (t, t')              -> Up  (wkn n t, wkn_ne n t')
and wkn_spine : Name.t -> spine -> spine = fun n ->
  Spine.map (wkn n) (Product.map (wkn n) (Name.wkn n))
and wkn_nu : Name.t -> t_nu -> t_nu = fun n t ->
  match t with
  | Nu (t, t') -> Nu (wkn n t, wkn_nu_name n t')
  | Vl t       -> Vl (wkn_vl n t)
and wkn_nu_name : Name.t -> t_nu Debruijn.name -> t_nu Debruijn.name = fun n t ->
  match t with
  | Debruijn.N (x, t) -> Debruijn.N (x, wkn_nu (Name.N n) t)
  
let rec wkv_s : Var.t -> s -> s = fun v ->
  Context.map (wkv v) (fun (t, m) -> (wkv v t, Name.wkv v m))
and wkv_nf : Var.t -> t_nf -> t_nf = fun n t ->
  match t with
  | Dwn (t, t') -> Dwn (wkv n t, wkv n t')
and wkv_ne : Var.t -> t_ne -> t_ne = fun v t ->
  match t with
  | Var (p, v')               -> Var (Table.wkv v p, Var.wkv v v')
  | App (t, t')               -> App (wkv_ne v t, wkv_nf v t')
  | Cnc (t, n )               -> Cnc (wkv_ne v t, Name.wkv v n)
  | Rne (x, l, t, tm, ti, t') -> Rne (x, l, wkv v t, List.map (wkv v) tm, wkv_spine v ti, wkv_ne v t') 
  | Cmp (n, t)                -> Cmp (Name.wkv v n, wkv_ne v t)
and wkv : Var.t -> t -> t = fun v t ->
  match t with
  | Nst | Unv _ -> t
  | Fun (t, t') -> Fun (wkv v t, wkv v t')
  | Nab (t, t') -> Nab (wkv v t, wkv v t')
  | Nam (t, m ) -> Nam (wkv v t, Name.wkv v m)
  | New t       -> New (wkv_nu v t)
and wkv_vl : Var.t -> t_vl -> t_vl = fun v t ->
  match t with
  | Cls (x, t, s )        -> Cls (x, t, wkv_s v s)
  | Alp (x, t, s )        -> Alp (x, t, wkv_s v s)
  | Tcn (x, t)            -> Tcn (x,    wkv_spine v t)
  | Dcn (x, i, t)         -> Dcn (x, i, wkv_spine v t)
  | Rmo (x, l)            -> Rmo (x, l)
  | Rme (x, l, t, tm)     -> Rme (x, l, wkv v t, List.map (wkv v) tm)
  | Rid (x, l, t, tm, ti) -> Rid (x, l, wkv v t, List.map (wkv v) tm, wkv_spine v ti)
  | Up  (t, t')           -> Up  (wkv v t, wkv_ne v t')
and wkv_spine : Var.t -> spine -> spine = fun v ->
  Spine.map (wkv v) (Product.map (wkv v) (Name.wkv v))
and wkv_nu : Var.t -> t_nu -> t_nu = fun v t ->
  match t with
  | Nu (t, t') -> Nu (wkv v t, wkv_nu_name v t')
  | Vl t       -> Vl (wkv_vl v t)
and wkv_nu_name : Var.t -> t_nu Debruijn.name -> t_nu Debruijn.name = fun v t ->
  match t with
  | Debruijn.N (x, t) -> Debruijn.N (x, wkv_nu (Var.N v) t)

let shiftn : t -> t = fun t -> wkn Name.Z t
let shiftv : t -> t = fun t -> wkv Var.Z t

let shiftn_s : t -> s -> s = fun d s ->
  Context.ortho (wkn_s Name.Z s) (wkn Name.Z d, Name.Z)

let method_type : Binder.t -> int -> Term.constructor -> t = fun x i t ->
  New (Vl (Cls (None, Term.method_type x i t Var.Z, Context.Empty)))
