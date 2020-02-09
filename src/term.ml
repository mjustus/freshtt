open Function

type level = int

type t =
  | Unv of level
  | Nst (* TODO of int *)
  | Fun of t * t
  | Nab of t * t
  | Lam of t Debruijn.var
  | Alp of t Debruijn.name
  | App of t * t
  | Cnc of t * Name.t
  | Swp of Name.t * Name.t * t
  | Nu  of t * t Debruijn.name
  | Cmp of Name.t * t
  | Var of Var.t
  | Nam of Name.t
  | Let of t * t * t Debruijn.var
  (* reference to a file-wide definition *)
  | Ref of Binder.t
  (* type constructor *)
  | Tcn of Binder.t  (* (t, Name.t) Spine.t*)
  (* data constructor *)
  | Dcn of Binder.t * int (* (t, Name.t) Spine.t*)
  | Rec of Binder.t * int
  | Chk of t * t

type telescope   = (t, t, t) Telescope.t
type constructor = t Constructor.t
type file        = t File.t

let mk_let : t -> t -> Binder.t_opt -> t -> t = fun t1 t1' i t2 -> Let (t1, t1', Debruijn.V (i, t2))
let mk_unv : int -> t = fun i -> Unv i
let mk_nst : t = Nst
let mk_fun : t -> t -> t = fun t t' -> Fun (t, t')
let mk_pi  : t -> Binder.t_opt -> t -> t = fun t x t' -> Fun (t, Lam (Debruijn.V (x, t')))
let mk_nab : t -> t -> t = fun t t' -> Nab (t, t')
let mk_na  : t -> Binder.t_opt -> t -> t = fun t x t' -> Nab (t, Alp (Debruijn.N (x, t')))
let mk_lam : Binder.t_opt -> t -> t = fun i t -> Lam (Debruijn.V (i, t))
let mk_alp : Binder.t_opt -> t -> t = fun i t -> Alp (Debruijn.N (i, t))
let mk_app : t -> t -> t = fun t t' -> App (t, t')
let mk_cnc : t -> Name.t -> t = fun t n -> Cnc (t, n)
let mk_var : Var.t -> t = fun v -> Var v
let mk_nam : Name.t -> t = fun n -> Nam n
let mk_swp : Name.t -> Name.t -> t -> t = fun n n' t -> Swp (n, n', t)
let mk_nu  : t -> Binder.t_opt -> t -> t = fun t i t' -> Nu (t, Debruijn.N (i, t'))
let mk_cmp : Name.t -> t -> t = fun n t -> Cmp (n, t)
let mk_chk : t -> t -> t = fun t t' -> Chk (t, t')
let mk_tcn : Binder.t -> t = fun x -> Tcn x

let rec wkv : Var.t -> t -> t = fun v t ->
  match t with
  | Unv _ 
  | Nst
  | Ref _
  | Tcn _
  | Dcn _
  | Rec _ -> t
  | Fun (t, t') -> Fun (wkv v t, wkv v t')
  | Nab (t, t') -> Nab (wkv v t, wkv v t')
  | Lam t -> Lam (wkv_var v t)
  | Alp t -> Alp (wkv_name v t)
  | App (t, t') -> App (wkv v t, wkv v t')
  | Cnc (t, n) -> Cnc (wkv v t, Name.wkv v n)
  | Swp (n, m, t) -> Swp (Name.wkv v n, Name.wkv v m, wkv v t)
  | Nu (t, t') -> Nu (wkv v t, wkv_name v t')
  | Cmp (n, t) -> Cmp (Name.wkv v n, wkv v t)
  | Var w -> Var (Var.wkv v w)
  | Nam n -> Nam (Name.wkv v n)
  | Let (t1, t1', t2) -> Let (wkv v t1, wkv v t1', wkv_var v t2)
  | Chk (t, t') -> Chk (wkv v t, wkv v t')
and wkv_var : Var.t -> t Debruijn.var -> t Debruijn.var = fun v t ->
  match t with
  | Debruijn.V (x, t) -> Debruijn.V (x, wkv (Var.V v) t)
and wkv_name : Var.t -> t Debruijn.name -> t Debruijn.name = fun v t ->
  match t with
  | Debruijn.N (x, t) -> Debruijn.N (x, wkv (Var.N v) t)

let rec wkn : Name.t -> t -> t = fun n t ->
  match t with
  | Unv _ 
  | Nst
  | Ref _
  | Tcn _
  | Dcn _
  | Rec _ -> t
  | Fun (t, t') -> Fun (wkn n t, wkn n t')
  | Nab (t, t') -> Nab (wkn n t, wkn n t')
  | Lam t -> Lam (wkn_var n t)
  | Alp t -> Alp (wkn_name n t)
  | App (t, t') -> App (wkn n t, wkn n t')
  | Cnc (t, m) -> Cnc (wkn n t, Name.wkn n m)
  | Swp (m, m', t) -> Swp (Name.wkn n m, Name.wkn n m', wkn n t)
  | Nu (t, t') -> Nu (wkn n t, wkn_name n t')
  | Cmp (m, t) -> Cmp (Name.wkn n m, wkn n t)
  | Var v -> Var (Var.wkn n v)
  | Nam m -> Nam (Name.wkn n m)
  | Let (t1, t1', t2) -> Let (wkn n t1, wkn n t1', wkn_var n t2)
  | Chk (t, t') -> Chk (wkn n t, wkn n t')
and wkn_var : Name.t -> t Debruijn.var -> t Debruijn.var = fun n t ->
  match t with
  | Debruijn.V (x, t) -> Debruijn.V (x, wkn (Name.V n) t)
and wkn_name : Name.t -> t Debruijn.name -> t Debruijn.name = fun n t ->
  match t with
  | Debruijn.N (x, t) -> Debruijn.N (x, wkn (Name.N n) t)

(* TODO explicitely marked recursive positions *)
type spine = (t, Name.t) Spine.t
(*type constructor_type = ((t, (t, t, spine) Telescope.t) Sum.t, t, spine) Telescope.t*)

type eliminator_type = {motive : t; methods : constructor list; result : Var.t -> telescope}
type eliminator      = {motive : t; methods : constructor list; result : Var.t -> telescope}

let wkv_spine : Var.t -> spine -> spine = fun v ->
  Spine.map (wkv v) (Name.wkv v)

let wkn_spine : Name.t -> spine -> spine = fun n ->
  Spine.map (wkn n) (Name.wkn n)

let wkv_constructor : Var.t -> constructor -> constructor =
  Telescope.wkv (fun v -> Sum.map (wkv v) (Telescope.wkv wkv wkv wkv_spine v)) wkv wkv_spine

let from_spine : t -> spine -> t = fun t s ->
  Spine.fold (fun t -> t) (fun f t t' -> f (mk_app t' t)) (fun f n t' -> f (mk_cnc t' n)) s t

let telescope_abs : 'a. ('a -> t) -> (t, t, 'a) Telescope.t -> t = fun f ->
  Telescope.fold mk_pi mk_na f

let telescope_applied : t -> (t, t, _) Telescope.t -> t = fun t ->
  Telescope.fold (fun _ _ t -> App (wkv Var.Z t, Var Var.Z)) (fun _ _ t -> Cnc (wkn Name.Z t, Name.Z)) (const t)

let telescope_wk : 'a. (Var.t -> 'a -> 'a) -> (Name.t -> 'a -> 'a) -> _ Telescope.t -> 'a -> 'a = fun wkv wkn t a ->
  Telescope.fold (fun _ _ -> wkv Var.Z) (fun _ _ -> wkn Name.Z) (fun _ -> a) t

let telescope_spine : 'a. (t, t, 'a) Telescope.t -> spine = fun t ->
  Telescope.fold
    (fun _ _ t -> Spine.Comma (wkv_spine  Var.Z t, mk_var @@  Var.Z))
    (fun _ _ t -> Spine.Ortho (wkn_spine Name.Z t,           Name.Z))
    (fun _     -> Spine.Empty)
    t
  
let arg_rec : Binder.t -> t Constructor.arg_rec -> t = fun x ->
  telescope_abs (from_spine (mk_tcn x))

let constructor_type : Binder.t -> constructor -> t = fun x ->
  Telescope.fold (mk_pi % Sum.fold id (arg_rec x)) mk_na (from_spine (mk_tcn x))

let rec method_type_rec : (t, t, spine) Telescope.t -> t -> t -> t = fun t t_spine t_applied ->
  match t with
  | Telescope.Fn (t, Debruijn.V (y, t')) -> mk_pi t y (method_type_rec t' (wkv  Var.Z t_spine) (App (wkv  Var.Z t_applied, Var  Var.Z)))
  | Telescope.Na (t, Debruijn.N (y, t')) -> mk_na t y (method_type_rec t' (wkn Name.Z t_spine) (Cnc (wkn Name.Z t_applied,     Name.Z)))
  | Telescope.Up s                       -> App (from_spine t_spine s, t_applied)

let method_type : Binder.t -> int -> constructor -> Var.t -> t = fun x i t motive ->
  let rec method_type_wk : Binder.t -> constructor -> t -> t -> Var.t -> t = fun x t t_spine t_applied motive ->
    match t with
    | Telescope.Fn (Sum.Inl t, Debruijn.V (y, t')) ->
        mk_pi t y (
          method_type_wk x t'
            (wkv Var.Z t_spine)
            (App (wkv Var.Z t_applied, Var Var.Z))
            (Var.wkv Var.Z motive)
        )
    | Telescope.Fn (Sum.Inr t, Debruijn.V (y, t')) ->
        mk_pi (arg_rec x t) y (
          method_type_rec_wk x t'
            (wkv Var.Z t_spine)
            (App (wkv  Var.Z t_applied, Var Var.Z))
            (Var.wkv Var.Z motive)
            (Telescope.wkv wkv wkv wkv_spine Var.Z t)
        )
    | Telescope.Na (t, Debruijn.N (y, t')) ->
        mk_na t y (
          method_type_wk x t'
            (wkn Name.Z t_spine)
            (Cnc (wkn Name.Z t_applied, Name.Z))
            (Var.wkn Name.Z motive)
        )
    | Telescope.Up s ->
        App (from_spine t_spine s, t_applied)
  and method_type_rec_wk : Binder.t -> constructor -> t -> t -> Var.t -> (t, t, spine) Telescope.t -> t = fun x t' t_spine t_applied motive t_telescope ->  
    mk_pi (method_type_rec t_telescope (Var motive) (Var Var.Z)) None (
      method_type_wk x (wkv_constructor Var.Z t')
        (wkv     Var.Z t_spine)
        (wkv     Var.Z t_applied)
        (Var.wkv Var.Z motive)
    )
  in
  method_type_wk x t (Var motive) (Dcn (x, i)) motive

let rec method_term_rec : (t, t, spine) Telescope.t -> t -> t -> t = fun t t_spine t_applied ->
  match t with
  | Telescope.Fn (_, Debruijn.V (y, t')) -> mk_lam y (method_term_rec t' (wkv  Var.Z t_spine) (App (wkv  Var.Z t_applied, Var  Var.Z)))
  | Telescope.Na (_, Debruijn.N (y, t')) -> mk_alp y (method_term_rec t' (wkn Name.Z t_spine) (Cnc (wkn Name.Z t_applied,     Name.Z)))
  | Telescope.Up s                       -> App (from_spine t_spine s, t_applied)

let method_term : constructor -> t = fun t ->
  let rec method_term : constructor -> t -> Var.t -> t = fun t t_applied v_elim ->
    match t with
    | Telescope.Fn (Sum.Inl _, Debruijn.V (_, t')) ->
        method_term t'
          (App (wkv Var.Z t_applied, Var Var.Z))
          (Var.wkv Var.Z v_elim)
    | Telescope.Fn (Sum.Inr t, Debruijn.V (_, t')) ->
        method_term_rec_wk t'
          (App (wkv  Var.Z t_applied, Var Var.Z))
          (Var.wkv Var.Z v_elim)
          (Telescope.wkv wkv wkv wkv_spine Var.Z t)
    | Telescope.Na (_, Debruijn.N (_, t')) ->
        method_term t'
          (Cnc (wkn Name.Z t_applied, Name.Z))
          (Var.wkn Name.Z v_elim)
    | Telescope.Up _ ->
        t_applied
  and method_term_rec_wk : constructor -> t -> Var.t -> (t, t, spine) Telescope.t -> t = fun t' t_applied v_elim t_telescope ->  
    method_term t'
      (App (t_applied, (method_term_rec t_telescope (Var v_elim) (Var Var.Z))))
      v_elim
  in
  method_term t (Var Var.Z) (Var.V Var.Z)

let rec method_types : type n. Binder.t -> int -> (n, constructor) Vec.t -> (Var.t -> t) -> Var.t -> t = fun x i cs f motive ->
  match cs with
  | Vec.Nil          -> f motive
  | Vec.Cons (t, cs) -> mk_pi (method_type x i t motive) None (method_types x (i+1) cs f (Var.V motive))
  
let motive : Binder.t -> level -> telescope -> t = fun x l t ->
  telescope_abs (fun _ -> mk_pi (telescope_applied (Tcn x) t) None (Unv l)) t

let result_type : Binder.t -> telescope -> Var.t -> t = fun x t motive ->
  let target    = telescope_applied (Tcn x) t in
  let telescope = Telescope.(fold mk_fn mk_na (fun _ -> mk_fn target None (mk_up ()))) t in
  let applied   = telescope_applied (Var motive) telescope in
  telescope_abs (const applied) telescope

let elim_type : type n. Binder.t -> level -> telescope -> (n, constructor) Vec.t -> t = fun x l t cs ->
  mk_pi (motive x l t) None (method_types x 0 cs (result_type x t) Var.Z)

let rec more : 'a. Binder.t_nlist_opt -> (Binder.t_opt -> 'a -> 'a) -> 'a -> 'a = function
  | N_list.Last i      -> fun f t -> f i t
  | N_list.More (i, b) -> fun f t -> f i (more b f t)

module StringSet = Set.Make (struct type t = string let compare = Stdlib.compare end)

let rec occurs_var : Var.t -> t -> bool = fun v t ->
  match t with
  | Unv _
  | Nst
  | Nam _
  | Ref _
  | Tcn _
  | Dcn _
  | Rec _ -> false
  | Nu  (t, t') -> occurs_var v t || occurs_var (Var.N v) (Debruijn.name_body t')
  | Alp t -> occurs_var (Var.N v) (Debruijn.name_body t)
  | Lam t -> occurs_var (Var.V v) (Debruijn.var_body t)
  | Nab  (t, t')
  | Fun (t, t')
  | Chk (t, t')
  | App (t, t') -> occurs_var v t || occurs_var v t'
  | Swp (_, _, t)
  | Cnc (t, _) -> occurs_var v t | Cmp (_, t) -> occurs_var v t
  | Var w -> v = w
  | Let (t1, t1', t2) -> occurs_var v t1 || occurs_var v t1' || occurs_var (Var.V v) (Debruijn.var_body t2)

let rec occurs_name : Name.t -> t -> bool = fun n t ->
  match t with
  | Var _
  | Nst
  | Unv _
  | Ref _
  | Tcn _
  | Dcn _
  | Rec _ -> false
  | Nu  (t, Debruijn.N (_, t')) -> occurs_name n t || occurs_name (Name.N n) t'
  | Alp (Debruijn.N (_, t)) -> occurs_name (Name.N n) t
  | Lam (Debruijn.V (_, t)) -> occurs_name (Name.V n) t
  | Fun (t, t')
  | Nab (t, t')
  | Chk (t, t')
  | App (t, t') -> occurs_name n t || occurs_name n t'
  | Cnc (t, m) -> n = m || occurs_name n t
  | Swp (m, m', t) -> n = m || n = m' || occurs_name n t
  | Nam m -> n = m
  | Cmp (m, t) -> n = m || occurs_name n t
  | Let (t1, t1', Debruijn.V (_, t2)) -> occurs_name n t1 || occurs_name n t1' || occurs_name (Name.V n) t2

let collect_spine : 'a 'b. ('a -> StringSet.t) -> ('b -> StringSet.t) -> ('a, 'b) Spine.t -> StringSet.t = fun f g ->
  Spine.fold
    StringSet.empty
    (fun x t -> StringSet.union x (f t))
    (fun x t -> StringSet.union x (g t))

let rec collect_vars : t -> StringSet.t = fun t ->
  match t with
  | Nu (t, t') -> StringSet.union (collect_vars t) (collect_vars_name t')
  | Lam t -> collect_vars_var t
  | Alp t -> collect_vars_name t
  | Fun (t, t')
  | Nab (t, t')
  | Chk (t, t')
  | App (t, t') -> StringSet.union (collect_vars t) (collect_vars t')
  | Cmp (_, t)
  | Cnc (t, _)
  | Swp (_, _, t) -> collect_vars t
  | Unv _
  | Nst
  | Var _
  | Nam _ -> StringSet.empty
  | Let (t1, t1', t2) -> StringSet.union (StringSet.union (collect_vars t1) (collect_vars t1')) (collect_vars_var t2)
  | Ref x -> StringSet.singleton x
  | Tcn x
  | Dcn (x, _)
  | Rec (x, _) -> StringSet.singleton x
and collect_vars_var : t Debruijn.var -> StringSet.t = function
  | Debruijn.V (Some x, t) -> StringSet.add x (collect_vars t)
  | Debruijn.V (None  , t) -> collect_vars t
and collect_vars_name : t Debruijn.name -> StringSet.t = function
  | Debruijn.N (_, t) -> collect_vars t

let rec collect_names : t -> StringSet.t = fun t ->
  match t with
  | Unv _
  | Nst
  | Var _
  | Nam _
  | Ref _
  | Tcn _
  | Dcn _
  | Rec _ -> StringSet.empty
  | Nu (t, t') -> StringSet.union (collect_names t) (collect_names_name t')
  | Lam t -> collect_names_var t
  | Alp t -> collect_names_name t
  | Fun (t, t')
  | Nab (t, t')
  | Chk (t, t')
  | App (t, t') -> StringSet.union (collect_names t) (collect_names t')
  | Cmp (_, t)
  | Cnc (t, _)
  | Swp (_, _, t) -> collect_names t
  | Let (t1, t1', t2) -> StringSet.union (StringSet.union (collect_names t1) (collect_names t1')) (collect_names_var t2)
and collect_names_var : t Debruijn.var -> StringSet.t = function
  | Debruijn.V (_, t) -> collect_names t
and collect_names_name : t Debruijn.name -> StringSet.t = function
  | Debruijn.N (Some x, t) -> StringSet.add x (collect_names t)
  | Debruijn.N (None  , t) -> collect_names t

let collect_vars_spine : (t, Name.t) Spine.t -> StringSet.t =
  Spine.fold
    StringSet.empty
    (fun s t -> StringSet.union s (collect_vars t))
    (fun s _ -> s)

let collect_names_spine : (t, Name.t) Spine.t -> StringSet.t =
  Spine.fold
    StringSet.empty
    (fun s t -> StringSet.union s (collect_names t))
    (fun s _ -> s)

let rec collect_vars_telescope : 'a 'c. ('a -> StringSet.t) -> ('c -> StringSet.t) -> ('a, t, 'c) Telescope.t -> StringSet.t = fun f h t ->
  match t with
  | Telescope.Fn (t, t') -> StringSet.union (f t)            (collect_vars_telescope_var  f h t')
  | Telescope.Na (t, t') -> StringSet.union (collect_vars t) (collect_vars_telescope_name f h t')
  | Telescope.Up t       -> h t
and collect_vars_telescope_var : 'a 'c. ('a -> StringSet.t) -> ('c -> StringSet.t) -> ('a, t, 'c) Telescope.t Debruijn.var -> StringSet.t = fun f h t ->
  match t with
  | Debruijn.V (Some x, t) -> StringSet.add x (collect_vars_telescope f h t)
  | Debruijn.V (None  , t) -> collect_vars_telescope f h t
and collect_vars_telescope_name : 'a 'c. ('a -> StringSet.t) -> ('c -> StringSet.t) -> ('a, t, 'c) Telescope.t Debruijn.name -> StringSet.t = fun f h t ->
  match t with
  | Debruijn.N (_     , t) -> collect_vars_telescope f h t
  
let rec collect_names_telescope : 'a 'c. ('a -> StringSet.t) -> ('c -> StringSet.t) -> ('a, t, 'c) Telescope.t -> StringSet.t = fun f h t ->
  match t with
  | Telescope.Fn (t, t') -> StringSet.union (f t)             (collect_names_telescope_var  f h t')
  | Telescope.Na (t, t') -> StringSet.union (collect_names t) (collect_names_telescope_name f h t')
  | Telescope.Up t       -> h t
and collect_names_telescope_var : 'a 'c. ('a -> StringSet.t) -> ('c -> StringSet.t) -> ('a, t, 'c) Telescope.t Debruijn.var -> StringSet.t = fun f h t ->
  match t with
  | Debruijn.V (_  , t) -> collect_names_telescope f h t
and collect_names_telescope_name : 'a 'c. ('a -> StringSet.t) -> ('c -> StringSet.t) -> ('a, t, 'c) Telescope.t Debruijn.name -> StringSet.t = fun f h t ->
  match t with
  | Debruijn.N (Some x, t) -> StringSet.add x (collect_names_telescope f h t)
  | Debruijn.N (None  , t) -> collect_names_telescope f h t

let collect_vars_constr : constructor -> StringSet.t =
  collect_vars_telescope (Sum.fold collect_vars (collect_vars_telescope collect_vars collect_vars_spine)) collect_vars_spine

let collect_names_constr : constructor -> StringSet.t =
  collect_names_telescope (Sum.fold collect_names (collect_names_telescope collect_names collect_names_spine)) collect_names_spine


let rec collect_vars_file : file -> StringSet.t = function
  | File.Defn (t1, t1', t2) ->
      StringSet.union
        (StringSet.union (collect_vars t1) (collect_vars t1'))
        (collect_vars_file_var t2)
  | File.Data (t, Named.Bound (x, Named.Vec.Bound (cs, (xs, f)))) ->
      StringSet.add x
        (StringSet.union
           (collect_vars_telescope collect_vars collect_vars t)
           (StringSet.union
              (StringSet.union
                 (Vec.fold StringSet.empty (fun x xs -> StringSet.add x xs) xs)
                 (Vec.fold StringSet.empty (fun t xs -> StringSet.union xs (collect_vars_constr t)) cs)
              )
              (collect_vars_file f))
           )
  | File.Done -> StringSet.empty
and  collect_vars_file_var : file Named.Opt.t -> StringSet.t = function
  | Named.Opt.Bound (Some x, t) -> StringSet.add x (collect_vars_file t)
  | Named.Opt.Bound (None  , t) -> collect_vars_file t

let rec collect_names_file : file -> StringSet.t = function
  | File.Defn (t1, t1', t2) ->
      StringSet.union
        (StringSet.union (collect_names t1) (collect_names t1'))
        (collect_names_file_var t2)
  | File.Data (t, Named.Bound (_, Named.Vec.Bound (cs, (_, f)))) ->
      StringSet.union
        (collect_names_telescope collect_names collect_names t)
        (StringSet.union
           (Vec.fold StringSet.empty (fun t xs -> StringSet.union xs (collect_names_constr t)) cs)
          (collect_names_file f)
        )
  | File.Done -> StringSet.empty
and  collect_names_file_var : file Named.Opt.t -> StringSet.t = function
  | Named.Opt.Bound (Some x, t) -> StringSet.add x (collect_names_file t)
  | Named.Opt.Bound (None  , t) -> collect_names_file t

module Print = struct
  module Env = struct
    type t = {
      constr_map : (Binder.t * Binder.t list) list;
      gen_var    : string Brook.t;
      gen_name   : string Brook.t;
      gamma      : (string, string) Context.t
    }
    end

  module M = Reader_t.Make (Env) (Error.String)
  module Op = Monad.Op (M)
  open Op

  let rec prime_close : string list -> string Brook.t = fun xs ->
    lazy (prime_close_data xs)
  and prime_close_data : string list -> string Brook.t_data = fun xs ->
    Brook.prepend_tail xs (prime_close (List.map (fun x -> x ^ "'") xs))

  let generate : string list -> StringSet.t -> string Brook.t = fun base exclude ->
    let extend   = ["0"; "1"; "2"; "3"; "4"; "5"; "6"; "7"; "8"; "9"] in
    let combined = List.fold_left (fun l x -> l @ List.map (fun s -> s ^ x) base) [] extend in
    let prime    = List.map (fun s -> s ^ "'") in
    let pred     = fun s -> not (StringSet.mem s exclude) in
    Brook.filter
      pred
      (Brook.prepend
         (base @ prime base @ combined)
         (prime_close (prime (prime (base @ combined))))
      )

  let init : StringSet.t -> StringSet.t -> Env.t = fun ex_var ex_name -> Env.{
      constr_map = [];
      gen_var    = generate ["x"; "y"; "z"; "u"; "v"; "w"; "r"; "s"; "t"; "p"; "q"] ex_var;
      gen_name   = generate ["n"; "m"; "l"; "a"; "b"; "c"; "d"; "e"] ex_name;
      gamma      = Context.Empty
    }

  let lookup_var : Var.t -> string M.t = fun v {Env.gamma;_} ->
    Error.String.(catch_map (Context.lookup_var gamma v) pure fail)

  let lookup_name : Name.t -> string M.t = fun n {Env.gamma;_} ->
    Error.String.(catch_map (Context.lookup_name gamma n) pure fail)

  let lookup_dcn : Binder.t -> int -> string M.t = fun n i {Env.constr_map;_} ->
    let open Error.String in
    match List.nth (List.assoc n constr_map) i with
    | x                       -> pure x
    | exception Not_found     -> fail "Type constructor not found."
    | exception Failure _     -> fail "Data constructor not found."
  
  let fresh_cons : Binder.t -> Binder.t list -> 'a M.t -> 'a M.t = fun x cs ->
    M.local (fun s ->
      Env.{s with
        constr_map = (x, cs) :: s.constr_map
      }
    )

  let read_name : string M.t = fun {Env.gen_name;_} ->
    Error.String.pure (Brook.head gen_name)
  
  let fresh_name : string option -> (string -> 'a M.t) -> 'a M.t = fun name f ->
    match name with
    | Some n ->
       M.local (fun s ->
          Env.{s with
            gamma    = Context.Ortho (s.gamma, n)
          }
       ) @@
       f n  
    | None   ->
        read_name >>= fun n ->
        M.local (fun s ->
          Env.{s with
            gen_name = Brook.tail s.gen_name;
            gamma    = Context.Ortho (s.gamma, n)
          }
        ) @@
        f n

  let read_var : string M.t = fun {Env.gen_var;_} ->
    Error.String.pure (Brook.head gen_var)

  let fresh_var : string option -> (string -> 'a M.t) -> 'a M.t = fun var f ->
    match var with
    | Some v ->
        M.local (fun s ->
          Env.{s with
            gamma = Context.Comma (s.gamma, v)
          }
        ) @@
        f v
    | None   ->
        read_var >>= fun v ->
        M.local (fun s ->
          Env.{s with
            gen_var = Brook.tail s.gen_var;
            gamma   = Context.Comma (s.gamma, v)
          }
        ) @@
        f v

  let print d =
  PPrint.ToChannel.pretty 1. 78 stdout d;
  print_newline ()
  
  let rec to_raw : t -> Raw.t M.t = fun t ->
    match t with
    | Unv l                    -> M.pure (Raw.Unv l)
    | Nst                      -> M.pure Raw.Nst
    | Fun _
    | Nab _                    -> Raw.mk_abs <$> to_raw_abs t
    | Lam t                    -> Raw.mk_lam <$> to_raw_var t
    | Alp t                    -> Raw.mk_alp <$> to_raw_name t
    | App (t, t')              -> Raw.mk_app <$> to_raw t <*> to_raw t'
    | Cnc (t, n )              -> Raw.mk_cnc <$> to_raw t <*> lookup_name n
    | Var v                    -> Raw.mk_idt <$> lookup_var v
    | Nam n                    -> Raw.mk_idt <$> lookup_name n
    | Swp (n, m, t)            -> Raw.mk_swp <$> lookup_name n <*> lookup_name m <*> to_raw t
    | Nu  (t, t')              -> Raw.mk_nu  <$> to_raw t <*> to_raw_name t'
    | Cmp (n, t)               -> Raw.mk_cmp <$> lookup_name n <*> to_raw t
    | Chk (t, t')              -> Raw.mk_chk <$> to_raw t <*> to_raw t'
    | Let (t1, t1', t2)        -> Raw.mk_let <$> to_raw t1 <*> to_raw t1' <*> to_raw_var t2
    | Ref x                    -> M.pure (Raw.Idt x)
    | Tcn x                    -> M.pure (Raw.Idt x)
    | Dcn (x, i)               -> Raw.mk_idt <$> lookup_dcn x i
    | Rec (x, i)               -> M.pure (Raw.Rec (x, i))
  and to_raw_abs : t -> (Raw.t, Raw.t) Raw.telescope M.t = fun t ->
    match t with
    | Fun (t, Lam (Debruijn.V (x, t'))) ->
        to_raw t >>= fun t ->
        fresh_var x @@ fun n ->
        if occurs_var Var.Z t' then
          Raw.mk_pi t (N_list.Last (Some n)) <$> to_raw_abs t'
        else
          Raw.mk_up % Raw.mk_abs <$> (Raw.mk_pi t (N_list.Last None) <$> (Raw.mk_up <$> to_raw t'))
    | Nab (t, Alp (Debruijn.N (x, t'))) ->
        to_raw t >>= fun t ->
        fresh_name x @@ fun n ->
        if occurs_name Name.Z t' then
          Raw.mk_na t (N_list.Last (Some n)) <$> to_raw_abs t'
        else
          Raw.mk_up % Raw.mk_abs <$> (Raw.mk_na t (N_list.Last None) <$> (Raw.mk_up <$> to_raw t'))
    | Nab _ -> failwith "Whoops. Expected an alpha abstraction."
    | Fun (_, t') -> fun e -> (print @@ Raw.Print.print @@ (Error.String.catch (to_raw t' e) failwith)); failwith "Whoops. Expected a lambda abstraction."
    | _          ->
        Raw.mk_up <$> to_raw t
  and to_raw_name : t Debruijn.name -> Raw.t Raw.binder M.t = function
    | Debruijn.N (x, t) ->
        fresh_name x @@ fun n ->
        if occurs_name Name.Z t then
          Named.Mult_opt.bind (N_list.Last (Some n)) <$> to_raw t
        else
          Named.Mult_opt.bind (N_list.Last  None)    <$> to_raw t
  and to_raw_var : t Debruijn.var -> Raw.t Raw.binder M.t = function
    | Debruijn.V (x, t) ->
        fresh_var x @@ fun v ->
        if occurs_var Var.Z t then
          Named.Mult_opt.bind (N_list.Last (Some v)) <$> to_raw t
        else
          Named.Mult_opt.bind (N_list.Last  None)    <$> to_raw t
(* TODO: optional annotation
  and to_raw_opt : t Option.t -> Raw.t Option.t M.t = fun t ->
    let module A = Monad.ToApplicative (M) in
    let module T = Traversable.Option  (A) in
    T.traverse to_raw t
*)

  let rec to_raw_telescope : ('a -> 'b M.t) -> (t, t, 'a) Telescope.t -> (Raw.t, 'b) Raw.telescope M.t = fun f t ->
    match t with
    | Telescope.Fn (t, Debruijn.V (x, t')) ->
        to_raw t              >>= fun t  ->
        fresh_var x           @@  fun v  ->
        to_raw_telescope f t' >>= fun t' ->
        M.pure @@ Raw.mk_pi t (N_list.Last (Some v)) t'
    | Telescope.Na (t, Debruijn.N (x, t')) ->
        to_raw t              >>= fun t  ->
        fresh_name x          @@  fun n  ->
        to_raw_telescope f t' >>= fun t' ->
        M.pure @@ Raw.mk_na t (N_list.Last (Some n)) t'
    | Telescope.Up t ->
        Raw.mk_up <$> f t
  
  let to_raw_spine : (t, Name.t) Spine.t -> (Raw.t, string) Spine.t M.t =
    let module T = Spine.Traversable2 (Monad.ToApplicative (M)) in
    T.traverse to_raw lookup_name

  let to_raw_constr : Binder.t -> t Constructor.t -> Raw.constr M.t = fun x ->
    to_raw_telescope to_raw_spine % Telescope.map (Sum.fold id (arg_rec x)) id id

  let to_raw_constr_list : type n. Binder.t -> (n, t Constructor.t) Vec.t -> (n, Raw.constr) Vec.t M.t = fun x t ->
    let module T = Traversable.Vec (Monad.ToApplicative (M)) in
    T.traverse (to_raw_constr x) t

  let rec to_raw_file : file -> Raw.file M.t = fun t ->
    match t with
    | File.Defn (t1, t1', t2) -> Raw.mk_defn <$> to_raw t1 <*> to_raw t1' <*> to_raw_file_defn t2
    | File.Data (t, cs)       -> Raw.mk_data <$> to_raw_telescope to_raw t <*> to_raw_file_data cs
    | File.Done               -> M.pure Raw.Done
  and to_raw_file_defn : file Named.Opt.t -> Raw.file Named.Opt.t M.t = function
    | Named.Opt.Bound (x, t) ->
        Named.Opt.bind x <$> to_raw_file t
  and to_raw_file_data : type n. (n, t Constructor.t, file) Named.Vec.t Named.t -> (n, Raw.constr, Raw.file) Named.Vec.t Named.t M.t = fun t ->
    match t with
    | Named.Bound (x, cs) ->
        Named.bind x <$> to_raw_file_constr x cs
  and to_raw_file_constr : type n. Binder.t -> (n, t Constructor.t, file) Named.Vec.t -> (n, Raw.constr, Raw.file) Named.Vec.t M.t = fun x t ->
    match t with
    | Named.Vec.Bound (cs, (xs, f)) ->
        Named.Vec.bind xs <$> to_raw_constr_list x cs <*> fresh_cons x (Vec.to_list xs) (to_raw_file f)

  let print : t -> PPrint.document = fun t ->
    Error.String.catch_map (to_raw t (init (collect_vars t) (collect_names t))) (Raw.Print.print % Raw.compress) failwith

  let print_file : file -> PPrint.document = fun t ->
    Error.String.catch_map(to_raw_file t (init (collect_vars_file t) (collect_names_file t))) (Raw.Print.print_file % Raw.compress_file) failwith
end

module Gamma = struct
  type t =
    | Empty
    | Var   of Binder.t_opt * t
    | Name  of Binder.t_opt * t

  type result =
    | R_var  of Var.t
    | R_name of Name.t

  let result_v : result -> result = function
    | R_var  v -> R_var  (Var.V  v)
    | R_name n -> R_name (Name.V n)

  let result_n : result -> result = function
    | R_var  v -> R_var  (Var.N  v)
    | R_name n -> R_name (Name.N n)
  
  let rec lookup : string -> t -> result option = fun n g ->
    match g with
    | Name (Some m, _) when n = m ->
        Option.pure (R_name Name.Z)
    | Name (_, g) ->
        Option.map result_n (lookup n g)
    | Var (Some m, _) when n = m ->
        Option.pure (R_var Var.Z)
    | Var (_, g) ->
        Option.map result_v (lookup n g)
    | Empty -> Option.fail
end

module Delta = struct
  type t =
    | Defn of Binder.t_opt * t
    | Data of Binder.t     * telescope * (Binder.t * constructor) list * t
    | Done

  type result =
    | R_defn
    | R_data of telescope * (Binder.t * constructor) list
    | R_cons of Binder.t * int * constructor
  
  let lookup_cons : 'a 'b. 'a -> ('a * 'b) list -> (int * 'b) Option.t = fun x ys ->
    let rec lookup_cons : 'a 'b. int -> 'a -> ('a * 'b) list -> (int * 'b) Option.t = fun i x ys ->
      match ys with
      | []                     -> Option.fail
      | (y, b) :: _ when x = y -> Option.pure (i, b)
      | _      :: ys           -> lookup_cons (i+1) x ys
    in
    lookup_cons 0 x ys
  
  let rec lookup : Binder.t -> t -> result Option.t = fun x t ->
    match t with
    | Defn (Some y,       _ ) when x = y -> Option.pure R_defn
    | Defn (_     ,       t')            -> lookup x t'
    | Data (     y, t, c, _ ) when x = y -> Option.pure (R_data (t, c))
    | Data (     y, _, c, t')            -> Option.fold
                                              (fun (i, c) -> Option.pure @@ R_cons (y, i, c))
                                              (fun () -> lookup x t')
                                              (lookup_cons x c)
    | Done                               -> Option.fail
end

module Env = struct
  type result =
    | R_var  of Var.t
    | R_name of Name.t
    | R_defn
    | R_data of telescope * (Binder.t * constructor) list
    | R_cons of Binder.t * int * constructor
  
  type nonrec t = {
    delta : Delta.t
  ; gamma : Gamma.t
  }

  let init : t = {
    delta = Delta.Done
  ; gamma = Gamma.Empty
  }
                    
  let lookup_delta : Binder.t -> Delta.t -> result Option.t = fun x d ->
    Option.map (function
      | Delta.R_defn           -> R_defn
      | Delta.R_data (t, c)    -> R_data (t, c)
      | Delta.R_cons (y, i, c) -> R_cons (y, i, c)
    ) (Delta.lookup x d)

  let lookup_gamma : string -> Gamma.t -> result Option.t = fun n g ->
    Option.map (function
      | Gamma.R_var  v -> R_var  v
      | Gamma.R_name n -> R_name n
    ) (Gamma.lookup n g)    

  let lookup : string -> t -> result Option.t = fun n {delta; gamma} ->
    Option.fold
      Option.pure
      (fun () -> lookup_delta n delta)
      (lookup_gamma n gamma)
end

module M = Reader_t.Make (Env) (Error.String)
module Op = struct
  include Monad.Op (M)

  let fail : string -> 'a M.t = fun s ->
    M.cast (Error.String.fail s)

  let rec bound_ap : 'a. (Binder.t_opt -> 'a M.t -> 'a M.t) -> (Binder.t_opt -> 'a M.t -> 'a M.t) -> Binder.t_nlist_opt -> 'a M.t -> 'a M.t = fun f g xs ->
    match xs with
    | N_list.More (x, xs) -> fun m -> f x @@ bound_ap f g xs m
    | N_list.Last x       -> fun m -> g x m

  let fresh_ap : (Binder.t_opt -> 'a M.t -> 'a M.t) -> (Binder.t_opt -> 'a -> 'a) M.t -> Binder.t_nlist_opt -> 'a M.t -> 'a M.t = fun f op xs ->
    let f' = fun x m -> op <*> M.pure x <*> f x m in
    bound_ap f' f' xs

  let fresh_bound : (Binder.t_opt -> 'a M.t -> 'a M.t) -> Binder.t_nlist_opt -> 'a M.t -> 'a M.t = fun f ->
    N_list.fold_map f Function.(%)

  let fresh_type : Binder.t_opt -> 'a M.t -> 'a M.t = fun x ->
    M.local (fun e -> Env.{e with gamma = Gamma.Var (x, e.gamma)})

  let fresh_name : Binder.t_opt -> 'a M.t -> 'a M.t = fun x ->
    M.local (fun e -> Env.{e with gamma = Gamma.Name (x, e.gamma)})

  let fresh_defn : Binder.t_opt -> 'a M.t -> 'a M.t = fun x ->
    M.local (fun e -> Env.{e with delta = Delta.Defn (x, e.delta)})

  let fresh_data : Binder.t -> telescope -> (Binder.t * constructor) list -> 'a M.t -> 'a M.t = fun x t xs ->
    M.local (fun e -> Env.{e with delta = Delta.Data (x, t, xs, e.delta)})
  
  let lookup_name : Binder.t -> Name.t M.t = fun n {Env.gamma; _} ->
    match Gamma.lookup n gamma with
    | Some (Gamma.R_name n) -> Error.String.pure n
    | _                     -> Error.String.fail @@ "Identifier '" ^ n ^ "' is not a name."
  
  let lookup : Binder.t -> Env.result Option.t M.t = fun x e ->
    Error.String.pure (Env.lookup x e)
end

open Op

let from_raw_idt : Binder.t -> Env.result option -> t M.t = fun x r ->
  match r with
  | Some (Env.R_var  v)         -> M.pure (Var v)
  | Some (Env.R_name n)         -> M.pure (Nam n)
  | Some (Env.R_defn  )         -> M.pure (Ref x)                                   
  | Some (Env.R_data _)         -> M.pure (Tcn x)
  | Some (Env.R_cons (y, i, _)) -> M.pure (Dcn (y, i))
  | None                        -> fail ("Unbound identifier '" ^ x ^ "'.")

let rec from_raw : Raw.t -> t M.t = fun t ->
  match t with
  | Raw.Let (t1, t1', Named.Mult_opt.Bound (xs, t2)) ->
      fresh_ap fresh_type (mk_let <$> from_raw t1 <*> from_raw t1') xs (from_raw t2)
  | Raw.Unv i ->
      M.pure (mk_unv i)
  | Raw.Nst ->
      M.pure Nst
  | Raw.Abs t ->
      from_raw_abs t
  | Raw.Lam (Named.Mult_opt.Bound (xs, t)) ->
      more xs mk_lam <$> (fresh_bound fresh_type xs @@ from_raw t)
  | Raw.Alp (Named.Mult_opt.Bound (xs, t)) ->
      more xs mk_alp <$> (fresh_bound fresh_name xs @@ from_raw t)
  | Raw.App (t, t') ->
      mk_app
      <$> from_raw t
      <*> from_raw t'
  | Raw.Cnc (t, n) ->
      mk_cnc <$> from_raw t <*> lookup_name n
  | Raw.Idt x ->
      lookup x >>= from_raw_idt x
  | Raw.Rec (x, i) ->
      M.pure (Rec (x, i))
  | Raw.Swp (n, n', t) ->
      mk_swp
      <$> lookup_name n
      <*> lookup_name n'
      <*> from_raw t
  | Raw.Nu (t, Named.Mult_opt.Bound (xs, t')) ->
      fresh_ap fresh_name (mk_nu <$> from_raw t) xs (from_raw t')
  | Raw.Cmp (n, t) ->
      mk_cmp <$> lookup_name n <*> from_raw t
  | Raw.Chk (t, t') ->
      mk_chk <$> from_raw t <*> from_raw t'
and from_raw_abs : (Raw.t, Raw.t) Raw.telescope -> t M.t = fun t ->
  match t with
  | Raw.Pi (t, Named.Mult_opt.Bound (xs, t')) ->
      fresh_ap fresh_type (mk_pi <$> from_raw t) xs (from_raw_abs t')
  | Raw.Na (t, Named.Mult_opt.Bound (xs, t')) ->
      fresh_ap fresh_name (mk_na <$> from_raw t) xs (from_raw_abs t')
  | Raw.Up t ->
      from_raw t
(* TODO: optional annotation
   and from_raw_opt : Raw.t Option.t -> t Option.t M.t = fun t ->
   let module A = Monad.ToApplicative (M) in
   let module T = Traversable.Option  (A) in
   T.traverse from_raw t
*)    

let rec from_raw_arg_spine : Binder.t -> Raw.t -> (t, spine) Sum.t M.t = fun x t ->
  match t with
  | Raw.App (t, t')      -> Sum.apply % Sum.map mk_app Spine.comma <$> from_raw_arg_spine x t <*> from_raw t'
  | Raw.Cnc (t, n )      -> Sum.apply % Sum.map mk_cnc Spine.ortho <$> from_raw_arg_spine x t <*> lookup_name n
  | Raw.Idt y when x = y -> lookup y >>= begin function
                              | Some (Env.R_data _) -> M.pure @@ Sum.inr Spine.Empty
                              | r                   -> Sum.inl <$> from_raw_idt x r
                            end
  | t                    -> Sum.inl <$> from_raw t

let rec from_raw_arg_telescope : Binder.t -> (Raw.t, Raw.t) Raw.telescope -> (t Constructor.arg, t Constructor.arg_rec) Sum.t M.t = fun x t ->
  match t with
  | Raw.Pi (t, Named.Mult_opt.Bound (xs, t')) ->
      let f t xs = Sum.map (mk_pi t xs) (Telescope.mk_fn t xs) in
      fresh_ap fresh_type (f <$> from_raw t) xs (from_raw_arg_telescope x t')
  | Raw.Na (t, Named.Mult_opt.Bound (xs, t')) ->
      let f t xs = Sum.map (mk_na t xs) (Telescope.mk_na t xs) in
      fresh_ap fresh_name (f <$> from_raw t) xs (from_raw_arg_telescope x t')
  | Raw.Up t ->
      Sum.map id Telescope.mk_up <$> from_raw_arg_spine x t

let from_raw_arg : Binder.t -> Raw.t -> (t Constructor.arg, t Constructor.arg_rec) Sum.t M.t = fun x t ->
  match t with
  | Raw.Abs t -> from_raw_arg_telescope x t
  | _         -> Sum.map id Telescope.mk_up <$> from_raw_arg_spine x t

let rec from_raw_telescope : 'a 'b 't. (Raw.t -> 't M.t) -> ('a -> 'b M.t) -> (Raw.t, 'a) Raw.telescope -> ('t, t, 'b) Telescope.t M.t = fun f g t ->
  match t with
  | Raw.Pi (t, Named.Mult_opt.Bound (xs, t')) ->
      fresh_ap fresh_type (Telescope.mk_fn <$> f        t) xs (from_raw_telescope f g t')
  | Raw.Na (t, Named.Mult_opt.Bound (xs, t')) ->
      fresh_ap fresh_name (Telescope.mk_na <$> from_raw t) xs (from_raw_telescope f g t')
  | Raw.Up t ->
      Telescope.mk_up <$> g t
           
let from_raw_spine : (Raw.t, string) Spine.t -> (t, Name.t) Spine.t M.t =
  let module T = Spine.Traversable2 (Monad.ToApplicative (M)) in
  T.traverse from_raw lookup_name

let rec from_raw_constr_list : type n. Binder.t -> (n, Raw.constr) Vec.t -> (n, t Constructor.t) Vec.t M.t = fun x cs ->
  match cs with
  | Vec.Nil          -> M.pure Vec.Nil
  | Vec.Cons (c, cs) -> Vec.cons <$> from_raw_telescope (from_raw_arg x) from_raw_spine c <*> from_raw_constr_list x cs

let rec from_raw_file : Raw.file -> file M.t =
  function
  | Raw.Defn (t, t', Named.Opt.Bound (x, f)) ->
      File.mk_defn x <$> from_raw t <*> from_raw t' <*> (fresh_defn x @@ from_raw_file f)
  | Raw.Data (t, Named.Bound (x, Named.Vec.Bound (cs, (xs, f)))) ->
      from_raw_telescope from_raw from_raw t                          >>= fun t  ->
      fresh_data x t [] @@ from_raw_constr_list x cs                  >>= fun cs ->
      fresh_data x t (Vec.to_list (Vec.zip xs cs)) @@ from_raw_file f >>= fun f  ->
      M.pure @@ File.mk_data x xs t cs f
  | Raw.Done ->
      M.pure File.Done
