type level = int

type nf =
  | Unv of level
  | Nst
  | Fun of nf * nf
  | Nab of nf * nf
  | Nam of Name.t
  | Rnf of rnf
and rnf =
  | Nu of nf * rnf Debruijn.name
  | Vl of vl
and vl =
  | Lam of nf Debruijn.var
  | Alp of nf Debruijn.name
  | Tcn of Binder.t *       (nf, Name.t) Spine.t
  | Dcn of Binder.t * int * (nf, Name.t) Spine.t
  | Neu of ne
and ne =
  | Var of Table.t * Var.t
  | App of ne * nf
  | Cnc of ne * Name.t
  | Rne of Binder.t * int * nf * nf list * (nf, Name.t) Spine.t * ne
  | Cmp of Name.t * ne

type spine = (nf, Name.t) Spine.t
type telescope = (nf, nf, nf) Telescope.t
type constructor = nf Constructor.t
type file = nf File.t

let mk_fun : nf -> nf -> nf = fun t t' -> Fun (t, t')
let mk_nab : nf -> nf -> nf = fun t t' -> Nab (t, t')
let mk_nam : Name.t -> nf = fun n -> Nam n
let mk_nu : nf -> rnf Debruijn.name -> rnf = fun t t' -> Nu (t, t')
let mk_vl : vl -> rnf = fun t -> Vl t
let mk_neu : ne -> vl = fun t -> Neu t
let mk_rnf : rnf -> nf = fun t -> Rnf t
let mk_alp : nf Debruijn.name -> vl = fun t -> Alp t
let mk_lam : nf Debruijn.var -> vl = fun t -> Lam t
let mk_var : Table.t -> Var.t -> ne = fun p v -> Var (p, v)
let mk_app : ne -> nf -> ne = fun t t' -> App (t, t')
let mk_cnc : ne -> Name.t -> ne = fun t n -> Cnc (t, n)
let mk_cmp : Name.t -> ne -> ne = fun n t -> Cmp (n, t)

let mk_tcn : Binder.t ->        spine -> vl = fun x   t -> Tcn (x,    t)
let mk_dcn : Binder.t -> int -> spine -> vl = fun x i t -> Dcn (x, i, t)
let mk_rne : Binder.t -> int -> nf -> nf list -> spine -> ne -> ne = fun x l t tm ti t' -> Rne (x, l, t, tm, ti, t')

let rec wkv_ne : Var.t -> ne -> ne = fun v t ->
  match t with
  | Var (p, w )               -> Var (Table.wkv v p, Var.wkv v w)
  | App (t, t')               -> App (wkv_ne v t, wkv_nf v t')
  | Cnc (t, n )               -> Cnc (wkv_ne v t, Name.wkv v n)
  | Rne (x, l, t, tm, ti, t') -> Rne (x, l, wkv_nf v t, List.map (wkv_nf v) tm, wkv_spine v ti, wkv_ne v t')
  | Cmp (n, t)                -> Cmp (Name.wkv v n, wkv_ne v t)
and wkv_vl : Var.t -> vl -> vl = fun v t ->
  match t with
  | Lam t         -> Lam (wkv_nf_var  v t)
  | Alp t         -> Alp (wkv_nf_name v t)
  | Tcn (x,    t) -> Tcn (x,    wkv_spine v t)
  | Dcn (x, i, t) -> Dcn (x, i, wkv_spine v t)
  | Neu t         -> Neu (wkv_ne v t)
and wkv_spine : Var.t -> spine -> spine = fun v ->
  Spine.map (wkv_nf v) (Name.wkv v)
and wkv_nf_var  : Var.t -> nf Debruijn.var  -> nf Debruijn.var  = fun v t ->
  match t with
  | Debruijn.V (x, t) -> Debruijn.V (x, wkv_nf (Var.V v) t)
and wkv_nf_name : Var.t -> nf Debruijn.name -> nf Debruijn.name = fun v t ->
  match t with
  | Debruijn.N (x, t) -> Debruijn.N (x, wkv_nf (Var.N v) t)
and wkv_rnf : Var.t -> rnf -> rnf = fun v t ->
  match t with
  | Nu (t, t') -> Nu (wkv_nf v t, wkv_rnf_name v t')
  | Vl t       -> Vl (wkv_vl v t)
and wkv_rnf_name : Var.t -> rnf Debruijn.name -> rnf Debruijn.name = fun v t ->
  match t with
  | Debruijn.N (x, t) -> Debruijn.N (x, wkv_rnf (Var.N v) t)
and wkv_nf : Var.t -> nf -> nf = fun v t ->
  match t with
  | Unv _
  | Nst         -> t
  | Fun (t, t') -> Fun (wkv_nf v t, wkv_nf v t')
  | Nab (t, t') -> Nab (wkv_nf v t, wkv_nf v t')
  | Nam n       -> Nam (Name.wkv v n)
  | Rnf t       -> Rnf (wkv_rnf v t)

let shiftv : nf -> nf = fun t -> wkv_nf Var.Z t

let rec wkn_ne : Name.t -> ne -> ne = fun n t ->
  match t with
  | Var (p, v )               -> Var (Table.wkn n p, Var.wkn n v)
  | App (t, t')               -> App (wkn_ne n t, wkn_nf n t')
  | Cnc (t, m )               -> Cnc (wkn_ne n t, Name.wkn n m)
  | Rne (x, l, t, tm, ti, t') -> Rne (x, l, wkn_nf n t, List.map (wkn_nf n) tm, wkn_spine n ti, wkn_ne n t')
  | Cmp (m, t)                -> Cmp (Name.wkn n m, wkn_ne n t)
and wkn_vl : Name.t -> vl -> vl = fun n t ->
  match t with
  | Lam t         -> Lam (wkn_nf_var  n t)
  | Alp t         -> Alp (wkn_nf_name n t)
  | Tcn (x, t)    -> Tcn (x,    wkn_spine n t)
  | Dcn (x, i, t) -> Dcn (x, i, wkn_spine n t)
  | Neu t         -> Neu (wkn_ne n t)
and wkn_spine : Name.t -> spine -> spine = fun n ->
  Spine.map (wkn_nf n) (Name.wkn n)
and wkn_nf_var  : Name.t -> nf Debruijn.var  -> nf Debruijn.var  = fun n t ->
  match t with
  | Debruijn.V (x, t) -> Debruijn.V (x, wkn_nf (Name.V n) t)
and wkn_nf_name : Name.t -> nf Debruijn.name -> nf Debruijn.name = fun n t ->
  match t with
  | Debruijn.N (x, t) -> Debruijn.N (x, wkn_nf (Name.N n) t)
and wkn_rnf : Name.t -> rnf -> rnf = fun n t ->
  match t with
  | Nu (t, t') -> Nu (wkn_nf n t, wkn_rnf_name n t')
  | Vl t       -> Vl (wkn_vl n t)
and wkn_rnf_name : Name.t -> rnf Debruijn.name -> rnf Debruijn.name = fun n t ->
  match t with
  | Debruijn.N (x, t) -> Debruijn.N (x, wkn_rnf (Name.N n) t)
and wkn_nf : Name.t -> nf -> nf = fun n t ->
  match t with
  | Unv _
  | Nst         -> t
  | Fun (t, t') -> Fun (wkn_nf n t, wkn_nf n t')
  | Nab (t, t') -> Nab (wkn_nf n t, wkn_nf n t')
  | Nam n       -> Nam (Name.wkn n n)
  | Rnf t       -> Rnf (wkn_rnf n t)

let shiftn : nf -> nf = fun t -> wkn_nf Name.Z t

let rec rem_ne : Name.t -> ne -> ne option = fun n t ->
  let open Option.Operators in
  match t with
  | Var (p, v )                -> mk_var <$> Table.rem n p <*> Option.pure (Var.rem n v)
  | App (t, t')                -> mk_app <$> rem_ne n t <*> rem_nf n t'
  | Cnc (t, m )                -> mk_cnc <$> rem_ne n t <*> Name.rem n m
  | Rne (x, l, tm, tf, ti, t') -> let module A = Monad.ToApplicative (Option) in
                                  let module T = Traversable.List    (A) in
                                  mk_rne x l <$> rem_nf n tm <*> T.traverse (rem_nf n) tf <*> rem_spine n ti <*> rem_ne n t'
  | Cmp (m, t)                 -> mk_cmp <$> Name.rem n m <*> rem_ne n t
and rem_vl : Name.t -> vl -> vl option = fun n t ->
  let open Option.Operators in
  match t with
  | Lam t         -> mk_lam <$> rem_nf_var  n t
  | Alp t         -> mk_alp <$> rem_nf_name n t
  | Tcn (x,    t) -> mk_tcn x   <$> rem_spine n t
  | Dcn (x, i, t) -> mk_dcn x i <$> rem_spine n t
  | Neu t         -> mk_neu <$> rem_ne n t
and rem_spine : Name.t -> spine -> spine option = fun n ->
  let module A = Monad.ToApplicative (Option) in
  let module T = Spine.Traversable2  (A)      in
  T.traverse (rem_nf n) (Name.rem n)
and rem_nf_var : Name.t -> nf Debruijn.var -> nf Debruijn.var option = fun n t ->
  let open Option.Operators in
  match t with
  | Debruijn.V (x, t) -> (fun t -> Debruijn.V (x, t)) <$> rem_nf (Name.V n) t
and rem_nf_name : Name.t -> nf Debruijn.name -> nf Debruijn.name option = fun n t ->
  let open Option.Operators in
  match t with
  | Debruijn.N (x, t) -> (fun t -> Debruijn.N (x, t)) <$> rem_nf (Name.N n) t
and rem_rnf : Name.t -> rnf -> rnf option = fun n t ->
  let open Option.Operators in
  match t with
  | Nu (t, t') -> mk_nu <$> rem_nf n t <*> rem_rnf_name n t'
  | Vl t       -> mk_vl <$> rem_vl n t
and rem_rnf_name : Name.t -> rnf Debruijn.name -> rnf Debruijn.name option = fun n t ->
  let open Option.Operators in
  match t with
  | Debruijn.N (x, t) -> (fun t -> Debruijn.N (x, t)) <$> rem_rnf (Name.N n) t
and rem_nf : Name.t -> nf -> nf option = fun n t ->
  let open Option.Operators in
  match t with
  | Fun (t,t')  -> mk_fun <$> rem_nf n t <*> rem_nf n t'
  | Nab (t,t')  -> mk_nab <$> rem_nf n t <*> rem_nf n t'
  | Nam m       -> mk_nam <$> Name.rem n m
  | Unv _ | Nst -> Option.pure t
  | Rnf t       -> mk_rnf <$> rem_rnf n t

let nu_rnf : nf -> rnf Debruijn.name -> rnf = fun t (Debruijn.N (x, t')) ->
  match rem_rnf Name.Z t' with
  | Some t' -> t'
  | None    -> Nu (t, Debruijn.N (x, t'))

let rec to_term_perm : Weaken.t -> Table.perm -> Term.t -> Term.t = fun w p t ->
  match p with
  | Context.Empty        ->
     t
  | Context.Comma (p, _) ->
     to_term_perm (Weaken.shiftv w) p t
  | Context.Ortho (p, n) ->
     let m = Name.(wk w Z) in
     if n = m then
       to_term_perm (Weaken.shiftn w) p t
     else
       to_term_perm (Weaken.shiftn w) (Context.map_right (Name.swp m n) p) (Term.Swp (m, n, t))

let rec to_term_table : Weaken.t -> Table.t -> Term.t -> Term.t = fun w p t ->
  match p with
  | Table.Perm  p -> to_term_perm  w                 p t
  | Table.Comma p -> to_term_table (Weaken.shiftv w) p t
  | Table.Ortho p -> to_term_table (Weaken.shiftn w) p t
  
let rec to_term_nf : (unit, unit) Context.t -> nf -> Term.t = fun c t ->
  match t with
  | Unv l ->
     Term.Unv l
  | Fun (t, t') ->
     Term.Fun  (to_term_nf c t, to_term_nf c t')
  | Nab (t, t') ->
     Term.Nab (to_term_nf c t, to_term_nf c t')
  | Nst ->
     Term.Nst
  | Nam n ->
     Term.Nam n
  | Rnf t ->
     to_term_rnf c t
and to_term_nf_var : (unit, unit) Context.t -> nf Debruijn.var -> Term.t Debruijn.var = fun c t ->
  match t with
  | Debruijn.V (x, t) -> Debruijn.V (x, to_term_nf (Context.comma c ()) t)
and to_term_nf_name : (unit, unit) Context.t -> nf Debruijn.name -> Term.t Debruijn.name = fun c t ->
  match t with
  | Debruijn.N (x, t) -> Debruijn.N (x, to_term_nf (Context.ortho c ()) t)
 
and to_term_rnf : (unit, unit) Context.t -> rnf -> Term.t = fun c t ->
  match t with
  | Nu (t, t') -> Term.Nu (to_term_nf c t, to_term_rnf_name c t')
  | Vl t       -> to_term_vl c t
and to_term_rnf_name : (unit, unit) Context.t -> rnf Debruijn.name -> Term.t Debruijn.name = fun c t ->
  match t with
  | Debruijn.N (x, t) -> Debruijn.N (x, to_term_rnf (Context.ortho c ()) t)

and to_term_vl : (unit, unit) Context.t -> vl -> Term.t = fun c t ->
  match t with
  | Lam t         -> Term.Lam (to_term_nf_var  c t)
  | Alp t         -> Term.Alp (to_term_nf_name c t)
  | Tcn (x,    s) -> Spine.fold (Term.Tcn x)      (fun t t' -> Term.mk_app t (to_term_nf c t')) Term.mk_cnc s
  | Dcn (x, i, s) -> Spine.fold (Term.Dcn (x, i)) (fun t t' -> Term.mk_app t (to_term_nf c t')) Term.mk_cnc s
  | Neu t         -> to_term_ne c t

and to_term_spine : (unit, unit) Context.t -> spine -> Term.spine = fun c ->
  Spine.map (to_term_nf c) Function.id  

and to_term_ne : (unit, unit) Context.t -> ne -> Term.t = fun c t ->
  match t with
  | Var (p, v )                -> to_term_table (Weaken.id c) p (Term.Var v)
  | App (t, t')                -> Term.App (to_term_ne c t, to_term_nf c t')
  | Cnc (t, n )                -> Term.Cnc (to_term_ne c t, n)
  | Rne (x, l, tm, tf, ti, t') -> Term.App (
                                    Term.from_spine
                                      (List.fold_left
                                         (fun t t' -> Term.App (t, to_term_nf c t'))
                                         (Term.App (Term.Rec (x, l), to_term_nf c tm))
                                         tf
                                      )
                                      (to_term_spine c ti)
                                    ,
                                    to_term_ne c t'
                                  )
  | Cmp (n, t)                 -> Term.Cmp (n, to_term_ne c t)

let rec to_term_telescope : 'a1 'a2 'c1 'c2. (unit, unit) Context.t -> ((unit, unit) Context.t -> 'a1 -> 'a2) -> ((unit, unit) Context.t -> 'c1 -> 'c2) -> ('a1, nf, 'c1) Telescope.t -> ('a2, Term.t, 'c2) Telescope.t = fun c f h t ->
  let open Telescope in
  match t with
  | Fn (t, Debruijn.V (x, t')) ->
      mk_fn (f          c t) x (to_term_telescope (Context.comma c ()) f h t')
  | Na (t, Debruijn.N (x, t')) ->
      mk_na (to_term_nf c t) x (to_term_telescope (Context.ortho c ()) f h t')
  | Up t ->
      mk_up (h c t)

let to_term_constr_list : type n. (n, nf Constructor.t) Vec.t -> (n, Term.t Constructor.t) Vec.t = fun xs ->
  Vec.map (to_term_telescope Context.empty (fun c -> Sum.map (to_term_nf c) (to_term_telescope c to_term_nf to_term_spine)) to_term_spine) xs
let to_term_tcn : telescope -> Term.telescope = to_term_telescope Context.empty to_term_nf to_term_nf

let rec to_term_file : file -> Term.file = fun t ->
  match t with
  | File.Defn (t1, t1', t2) -> File.Defn (to_term_nf Context.Empty t1, to_term_nf Context.Empty t1', to_term_file_var t2)
  | File.Data (t, t')       -> File.Data (to_term_tcn t, to_term_file_constr_list t')
  | File.Done               -> File.Done
and to_term_file_var : file Named.Opt.t -> Term.file Named.Opt.t = fun t ->
  match t with
  | Named.Opt.Bound (x, t) -> Named.Opt.Bound (x, to_term_file t)
and to_term_file_constr_list : 'n. ('n, nf Constructor.t, file) Named.Vec.t Named.t -> ('n, Term.t Constructor.t, Term.file) Named.Vec.t Named.t = function
  | Named.Bound (x, Named.Vec.Bound (cs, (xs, t))) ->
      Named.Bound (x, Named.Vec.Bound (to_term_constr_list cs, (xs, to_term_file t)))

module Equiv = struct
  (* Equivalence check *)
  type table =
    | Free
    | Comma of table
    | Ortho of table
    | Swap  of table * nf * nf * (Name.t option)
    (* Separator to mark blocks of nus. *)
    | Marker of table

  let rec wkv_table_entries : Var.t -> table -> table = fun v p ->
    match p with
    | Free                 -> Free
    | Comma   p            -> Comma  (wkv_table_entries (Var.V v) p)
    | Ortho   p            -> Ortho  (wkv_table_entries (Var.N v) p)
    | Swap   (p, t, t', o) -> Swap   (wkv_table_entries (Var.N v) p, wkv_nf v t, wkv_nf v t', Option.map (Name.wkv v) o)
    | Marker p             -> Marker (wkv_table_entries v p)

  let rec wkn_table_entries : Name.t -> table -> table = fun n p ->
    match p with
    | Free                 -> Free
    | Comma   p            -> Comma  (wkn_table_entries (Name.V n) p)
    | Ortho   p            -> Ortho  (wkn_table_entries (Name.N n) p)
    | Swap   (p, t, t', o) -> Swap   (wkn_table_entries (Name.N n) p, wkn_nf n t, wkn_nf n t', Option.map (Name.wkn n) o)
    | Marker p             -> Marker (wkn_table_entries n p)

  let rec count : table -> Name.t -> int Option.t = fun p n ->
    match p, n with
    | Free             , _        -> Option.fail
    | Comma p          , Name.V n -> count p n
    | Swap  _          , Name.Z   -> Option.pure 0
    | Ortho _          , Name.Z   -> Option.fail
    | Ortho p          , Name.N n
    | Swap (p, _, _, _), Name.N n -> count p n
    | Marker p         , _        -> Option.map ((+) 1) (count p n)
    | _ -> failwith "Ill-kinded marker count."

  let rec lookup_left : table -> Name.t -> nf Option.t = fun p n ->
    match p, n with
    | Free             , _        -> Option.fail
    | Comma p          , Name.V n -> Option.map shiftv (lookup_left p n)
    | Swap (_, t, _, _), Name.Z   -> Option.pure t
    | Ortho p          , Name.N n
    | Swap (p, _, _, _), Name.N n -> Option.map shiftn (lookup_left p n)
    | Marker p         , _        -> lookup_left p n
    | _ -> failwith "Ill-kinded marker count."

  let rec lookup_right : table -> Name.t -> nf Option.t = fun p n ->
    match p, n with
    | Free             , _        -> Option.fail
    | Comma p          , Name.V n -> Option.map shiftv (lookup_right p n)
    | Swap (_, _, t, _), Name.Z   -> Option.pure t
    | Ortho p          , Name.N n
    | Swap (p, _, _, _), Name.N n -> Option.map shiftn (lookup_right p n)
    | Marker p         , _        -> lookup_right p n
    | _ -> failwith "Ill-kinded marker count."

  module S = struct
    type t = table
  end
  module M = State.Make (S)
  module Op = Monad.Op (M)
  open Op

  let set : Name.t  -> Name.t -> bool M.t = fun n m p ->
    let rec modify : Name.t  -> Name.t -> table -> table Option.t = fun n m p ->
      match p, n with
      | Free                    , _        -> Option.fail
      | Comma p                 , Name.V n -> modify n m p
      | Swap (p, t, t', None   ), Name.Z   -> Option.pure (Swap (p, t, t', Some m))
      | Swap (_, _, _ , Some m'), Name.Z   -> if m = m' then
                                              Option.pure p
                                            else
                                              Option.fail
      | Ortho p                 , Name.V n -> Option.map (fun p -> Ortho p)            (modify n m p)
      | Swap (p, t, t', o)      , Name.N n -> Option.map (fun p -> Swap (p, t, t', o)) (modify n m p)
      | Marker p         , _               -> Option.map (fun p -> Marker p)           (modify n m p)
      | _ -> failwith "Ill-kinded marker count." in
    match modify n m p with
    | Some p -> (true , p)
    | None   -> (false, p)

  let table_nu : nf -> nf -> unit M.t = fun t t' ->
    M.write (fun p -> Swap (p, shiftn t, shiftn t', None))
  let untable_nu : unit M.t =
    M.write (function Swap (p, _, _, _) -> p | _ -> failwith "Ill-kinded name equivalence table.")
  let table_lam : unit M.t =
    M.write (fun p -> Comma p)
  let untable_lam : unit M.t =
    M.write (function Comma p -> p | _ -> failwith "Ill-kinded name equivalence table.")
  let table_alp : unit M.t =
    M.write (fun p -> Ortho p)
  let untable_alp : unit M.t =
    M.write (function Ortho p -> p | _ -> failwith "Ill-kinded name equivalence table.")
  let table_marker : unit M.t =
    M.write (fun p -> Marker p)
  let untable_marker : unit M.t =
    M.write (function Marker p -> p | _ -> failwith "Ill-kinded name equivalence table.")

  let (&&) : bool M.t -> bool M.t -> bool M.t = fun m m' ->
    (&&) <$> m <*> m'

  let rec equiv_perm : Table.perm -> Table.perm -> bool M.t = fun p p' ->
    match p, p' with
    | Context.Empty       , Context.Empty          -> M.pure true
    | Context.Comma (p, _), Context.Comma (p', _ ) -> equiv_perm p p'
    | Context.Ortho (p, n), Context.Ortho (p', n') -> equiv_name n n' && equiv_perm p p'
    | _                   , _                      -> M.pure false
  and equiv_table : Table.t -> Table.t -> bool M.t = fun t t' ->
    match t, t' with
    | Table.Perm  p, Table.Perm  p' -> equiv_perm p p'
    | Table.Comma t, Table.Comma t' -> equiv_table t t'
    | Table.Ortho t, Table.Ortho t' -> equiv_table t t'
    | _            , _              -> M.pure false
  and equiv_name : Name.t -> Name.t -> bool M.t = fun n n' ->
    M.read >>= fun p ->
    match count p n, count p n' with
    | Some c, Some c' -> M.pure (c = c') && set n n' &&
                         begin match lookup_left p n, lookup_right p n' with
                         | Some t, Some t' -> equiv_nf t t'
                         | _               -> M.pure false
                         end
    | None  , None    -> M.pure (n = n')
    | _               -> M.pure false
  and equiv_ne : ne -> ne -> bool M.t = fun t t' ->
    match t, t' with
    | Var (p , v  ), Var (p', v' ) -> M.pure (v = v') && equiv_table p p'
    | App (t1, t1'), App (t2, t2') -> equiv_ne t1 t2 && equiv_nf t1' t2'
    | Cnc (t , n  ), Cnc (t', n' ) -> equiv_ne t t' && equiv_name n n'
    | Cmp (n , t  ), Cmp (n', t' ) -> equiv_name n n' && equiv_ne t t'
    | _ -> M.pure false
  and equiv_vl : vl -> vl -> bool M.t = fun t t' ->
    match t, t' with
    | Lam (Debruijn.V (_, t)), Lam (Debruijn.V (_, t')) ->
        table_lam     >>
        equiv_nf t t' <*
        untable_lam
    | Alp (Debruijn.N (_, t)), Alp (Debruijn.N (_, t')) ->
        table_alp     >>
        equiv_nf t t' <*
        untable_alp
    | Tcn (x, t), Tcn (x', t') ->
        if x = x' then
          equiv_spine t t'
        else
          M.pure false
    | Dcn (x, i, t), Dcn (x', i', t') ->
        if Stdlib.(&&) (x = x') (i = i') then
          equiv_spine t t'
        else
          M.pure false
    | Neu t, Neu t' ->
        equiv_ne t t'
    | _ -> M.pure false
  and equiv_spine : spine -> spine -> bool M.t = fun t t' ->
    match t, t' with
    | Spine.Comma (t1, t1'), Spine.Comma (t2, t2') ->
        equiv_nf    t1' t2' &&
        equiv_spine t1  t2
    | Spine.Ortho (t1, n1 ), Spine.Ortho (t2, n2 ) ->
        equiv_name  n1 n2 &&
        equiv_spine t1 t2
    | Spine.Empty          , Spine.Empty           ->
        M.pure true
    | _ -> failwith "Internal error: encountered ill-kinded spine during equivalence checking."
  and equiv_rnf : rnf -> rnf -> bool M.t = fun t t' ->
    match t, t' with
    | Nu (t1, Debruijn.N (_, t1')), Nu (t2, Debruijn.N (_, t2')) ->
        table_nu  t1  t2  >>
        equiv_rnf t1' t2' <*
        untable_nu
    | Vl t, Vl t' ->
        table_marker  >>
        equiv_vl t t' <*
        untable_marker
    | _ -> M.pure false
  and equiv_nf : nf -> nf -> bool M.t = fun t t' ->
    match t, t' with
    | Unv l        , Unv l'        -> M.pure (l = l')
    | Fun (t1, t1'), Fun (t2, t2') -> equiv_nf t1 t2 && equiv_nf t1' t2'
    | Nab (t1, t1'), Nab (t2, t2') -> equiv_nf t1 t2 && equiv_nf t1' t2'
    | Nst          , Nst           -> M.pure true
    | Nam n        , Nam n'        -> equiv_name n n'
    | Rnf t        , Rnf t'        -> equiv_rnf t t'
    | _                            -> M.pure false

  let equiv : nf -> nf -> bool = fun t t' ->
    (* TODO: need to take context into account.
         Requires Context.t to distinguish between Alp and Nu.
    *)
    M.run (equiv_nf t t') Free
end

module Print = struct
  let print : (unit, unit) Context.t -> nf -> PPrint.document = fun c t ->
    Term.Print.print (to_term_nf c t)
  let print_file : file -> PPrint.document = fun t ->
    Term.Print.print_file (to_term_file t)
end
