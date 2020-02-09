open Function

module Env = struct
  type delta = Delta.t
  type gamma = (Model.t, Model.t) Context.t
  type rho   = Model.s

  type t = {delta : delta; gamma : gamma; rho : rho}

  let init : t = {delta = Delta.Done; gamma = Context.Empty; rho = Context.Empty}
end
module E = Error.Make (Failure)
module M = Reader_t.Make (Env) (E)
module Op = Monad.Op (M)
open Op

let propagate_error : (Failure.t -> Failure.t) -> 'a M.t -> 'a M.t = fun f m ->
  (fun t -> E.catch_map t E.pure (E.fail % f)) % m


let extend_var : Model.t -> Model.t -> 'a M.t -> 'a M.t = fun d d' ->
  M.local (fun e ->
    let gamma = Context.Comma (
      Context.map Model.shiftv Model.shiftv e.Env.gamma,
      Model.shiftv d
    ) in
    let rho = Context.Comma (
      Model.wkv_s Var.Z e.Env.rho,
      Model.shiftv d'
    ) in
    Env.{e with gamma; rho}
  )

let extend_defn : Binder.t_opt -> Model.t -> Model.t -> 'a M.t -> 'a M.t = fun x d d' ->
  M.local @@ fun e ->
    Env.{e with delta = Delta.mk_defn x d d' e.Env.delta}

let extend_data : type n. Binder.t -> Model.telescope -> (n, Model.constructor) Vec.t -> (Term.level -> Term.t) -> (n, Term.t) Vec.t -> 'a M.t -> 'a M.t = fun x d cs dr dm ->
  M.local @@ fun e ->
  Env.{e with delta = Delta.mk_data x d cs dr dm e.Env.delta}

let shiftn : Model.t -> 'a M.t -> 'a M.t = fun d ->
  M.local (fun e ->
    let gamma = Context.Ortho (
      Context.map Model.shiftn Model.shiftn e.Env.gamma,
      Model.shiftn d
    ) in
    let rho = Context.Ortho (
      Model.wkn_s Name.Z e.Env.rho,
      (Model.shiftn d, Name.Z)
    ) in
    Env.{e with gamma; rho}
  )

let shiftv : 'a. Model.t -> 'a M.t -> 'a M.t = fun d ->
  M.local (fun e ->
    let gamma = Context.Comma (
      Context.map Model.shiftv Model.shiftv e.Env.gamma,
      Model.shiftv d
    ) in
    let rho = Context.Comma (
      Model.wkv_s Var.Z e.Env.rho,
      Model.New (Model.Vl (Model.Up (Model.shiftv d, Model.Var (Table.wkv Var.Z (Table.from_context e.Env.rho), Var.Z))))
    ) in
    Env.{e with gamma; rho}
  )

let m_shiftv : Model.t M.t -> 'a M.t -> 'a M.t = fun m m' ->
  m >>= fun d -> shiftv d m'

let m_shiftn : Model.t M.t -> 'a M.t -> 'a M.t = fun m m' ->
  m >>= fun d -> shiftn d m'

let fail : Failure.t -> 'a M.t = fun m _ ->
  E.fail m

let rho : Model.s M.t =
  (fun e -> e.Env.rho) <$> M.ask

let gamma : (Model.t, Model.t) Context.t M.t =
  (fun e -> e.Env.gamma) <$> M.ask

let delta : Delta.t M.t =
  (fun e -> e.Env.delta) <$> M.ask
                             
let eval : Term.t -> Model.t M.t = fun t ->
  Eval.eval t <$> rho <*> delta

let eval_tcn : Term.telescope -> Model.telescope M.t = fun t ->
  Eval.eval_tcn t <$> rho <*> delta

let eval_dcn : Term.constructor -> Model.constructor M.t = fun t ->
  Eval.eval_dcn t <$> rho <*> delta

let eval_dcn_rec : Term.t Constructor.arg_rec -> Binder.t -> Model.t M.t = fun t x ->
  Model.constructor_to_term_arg x <$> (Eval.eval_dcn_rec t <$> rho <*> delta)

let lookup_var : Var.t -> Model.t M.t = fun v ->
  M.ask >>= fun {Env.gamma; _} ->
  Sum.fold
    M.pure
    (fun _ -> fail (Failure.UnboundVar (gamma, v)))
    (Context.lookup_var gamma v)

let lookup_name : Name.t -> Model.t M.t = fun n ->
  M.ask >>= fun {Env.gamma; _} ->
  Sum.fold
    M.pure
    (fun _ -> fail (Failure.UnboundName (gamma, n)))
    (Context.lookup_name gamma n)

let lookup_def : Binder.t -> Model.t M.t = fun x ->
  M.ask >>= fun {Env.delta; _} ->
  Option.fold
    (fun (d, _) -> M.pure d)
    (fun () -> fail (Failure.UnboundDefn (delta, x)))
    (Delta.lookup_def x delta)

let lookup_tcn : Binder.t -> Model.t M.t = fun x ->
  M.ask >>= fun {Env.delta; _} ->
  Option.fold
    (M.pure % Model.telescope_to_term)
    (fun () -> fail (Failure.UnboundTcn (delta, x)))
    (Delta.lookup_tcn x delta)

let lookup_dcn : Binder.t -> int -> Model.t M.t = fun x i ->
  M.ask >>= fun {Env.delta; _} ->
  Option.fold
    (M.pure % Model.constructor_to_term x)
    (fun () -> fail (Failure.UnboundDcn (delta, x, i)))
    (Delta.lookup_dcn x i delta)

let lookup_elim : Binder.t -> Model.level -> Model.t M.t = fun x l ->
  M.ask >>= fun {Env.delta; _} ->
  Option.fold
    (fun f -> eval (f l))
    (fun () -> fail (Failure.UnboundRec (delta, x)))
    (Delta.lookup_elim x delta)

let equiv : Model.t -> Model.t -> Model.t -> unit M.t = fun dt d d' ->
  M.ask >>= fun {Env.delta; Env.gamma; Env.rho} ->
  let c = Context.map (fun _ -> ()) (fun _ -> ()) gamma in
  if Normal.Equiv.equiv (* TODO nu's in context *) (Readback.rb c dt d delta) (Readback.rb c dt d' delta)
  then
    M.pure ()
  else
    fail (Failure.NotEquiv (delta, gamma, rho, dt, d, d'))

let gen_var : 'a. Model.t -> (Model.t -> 'a M.t) -> 'a M.t = fun d f ->
  shiftv d (
    rho >>= fun r ->
    f @@
      Error.String.catch
        (Context.lookup_var r Var.Z)
        (fun _ -> failwith "Internal error.")
  )

let gen_name : 'a. Model.t -> (Model.t * Name.t -> 'a M.t) -> 'a M.t = fun d f ->
  shiftn d (
    rho >>= fun r ->
    f @@
      Error.String.catch
        (Context.lookup_name r Name.Z)  
        (fun _ -> failwith "Internal error")
  )

let equiv_type : Model.t -> Model.t -> unit M.t = fun d d' ->
  (* The universe level is arbitrary; read-back doesn't care. *)
  equiv Model.unv_syn d d'

let fresh : (Model.t * Name.t) -> Model.t -> Term.t -> unit M.t = fun (dn, n) dt t ->
  let error_type = Failure.NotFreshType (       n, dt) in
  let error_term = Failure.NotFreshTerm (Name.N n, t ) in
  let dt = Model.wkn Name.Z dt                  in
  Model.shiftn <$> eval t >>= fun d ->
  shiftn dn (
    propagate_error
      (function Failure.NotEquiv _ -> error_type | e -> e)
      (equiv_type    (Eval.swp Name.Z (Name.N n) dt) dt) >>
    propagate_error
      (function Failure.NotEquiv _ -> error_term | e -> e)
      (equiv      dt (Eval.swp Name.Z (Name.N n) d ) d)
  )

let nu : Model.t -> Model.t -> Term.t -> Model.t M.t = fun d dt t ->
  fresh (Model.shiftn d, Name.Z) dt t >>= fun () ->
  M.pure (Eval.nu None d dt)

let unv_neg : Model.level -> unit M.t = fun l ->
  if l < 0 then
    fail (Failure.NegUnvLevel l)
  else
    M.pure ()

let app : Model.t -> Model.t -> Model.t M.t = fun d d' ->
  Eval.app d d' <$> delta

let app_tcn : Binder.t_opt * Term.telescope * Model.s -> Model.t -> Model.telescope M.t = fun (_, t, r) d' ->
  Eval.eval_tcn t (Context.Comma (r, d')) <$> delta

let cnc_tcn : Binder.t_opt * Term.telescope * Model.s -> Model.t * Name.t -> Model.telescope M.t = fun (_, t, r) d' ->
  Eval.eval_tcn t (Context.Ortho (r, d')) <$> delta

let cnc : Model.t -> Model.t * Name.t -> Model.t M.t = fun d a ->
  Eval.cnc d a <$> delta
                      
let rec sub_type : Model.t -> Model.t -> unit M.t = fun d d' ->
  match d, d' with
  | Model.Unv l        , Model.Unv l'        -> unv_neg l  >>
                                                unv_neg l' >>
                                                if (l <= l') then
                                                  M.pure ()
                                                else
                                                  fail (Failure.NotSubUnv (l, l'))
  | Model.Nst          , Model.Nst           -> M.pure ()
  | Model.Nst          , Model.Unv l'        -> if l' >= 1 then
                                                  M.pure ()
                                                else
                                                  fail (Failure.NotSubNst l')
  | Model.Fun (d1, d1'), Model.Fun (d2, d2') -> equiv_type d1 d2 >> (* TODO make covariant *)
                                                gen_var d1 @@ fun v ->
                                                sub_type <$> (app (Model.shiftv d1') v) <**> (app (Model.shiftv d2') v)
  | Model.Nab (d1, d1'), Model.Nab (d2, d2') -> equiv_type d1 d2 >>
                                                gen_name d1 @@ fun n ->
                                                sub_type <$> (cnc (Model.shiftn d1') n) <**> (cnc (Model.shiftn d2') n)
  | _                                        -> equiv_type d d'

let super_type : Model.t -> Model.t -> unit M.t = fun d d' ->
  sub_type d' d

let super_unv : Model.level -> Model.t -> unit M.t = fun l d' ->
  sub_type d' (Model.Unv l)

let is_fun : Model.t -> (Model.t * Model.t) M.t = function
  | Model.Fun (d, d') -> M.pure (d, d')
  | d                 -> fail (Failure.NotFun d)

let is_nab : Model.t -> (Model.t * Model.t) M.t = function
  | Model.Nab (d, d') -> M.pure (d, d')
  | d                 -> fail (Failure.NotNab d)

let is_unv : Model.t -> Model.level M.t = function
  | Model.Unv l -> unv_neg l >>
                   M.pure  l 
  | d           -> fail (Failure.NotUnv d)
                              
let is_kind : Model.t -> unit M.t = function
  | Model.Unv l -> unv_neg l
  | Model.Nst   -> M.pure ()
  | d           -> fail (Failure.NotUnv d)

let lub : Model.t -> Model.t -> Model.t M.t = fun d d' ->
  match d, d' with
  | Model.Nst  , Model.Nst    -> M.pure Model.Nst
  | Model.Unv l, Model.Nst
  | Model.Nst  , Model.Unv l  -> M.pure (Model.Unv (max 1 l ))
  | Model.Unv l, Model.Unv l' -> M.pure (Model.Unv (max l l'))
  | Model.Nst  , _
  | Model.Unv _, _            -> fail (Failure.NotUnv d')
  | _                         -> fail (Failure.NotUnv d )

let rec check : Term.t -> Model.t -> unit M.t = fun t d ->
  match t , d with
  | Term.Lam t, Model.Fun (d, d') -> gen_var d @@ fun v ->
                                     app (Model.shiftv d') v >>=
                                     check (Debruijn.var_body t)
  | Term.Lam _, _                 -> fail (Failure.NotFun d)
  | Term.Alp t, Model.Nab (d, d') -> gen_name d @@ fun n ->
                                     cnc (Model.shiftn d') n >>=
                                     check (Debruijn.name_body t)
  | Term.Alp _, _                 -> fail (Failure.NotNab d)
  | Term.Let (t1, t1', t2), _     -> check_type t1 >>
                                     eval t1       >>= fun d1  ->
                                     check t1' d1  >>
                                     eval t1'      >>= fun d1' ->
                                     extend_var d1 d1' @@
                                     check (Debruijn.var_body t2) (Model.shiftv d)
  | Term.Nu (t, t'), _            -> check t Model.Nst >>
                                     eval t            >>= fun z ->
                                     gen_name z        @@  fun n ->
                                     check (Debruijn.name_body t') (Model.shiftn d) >>
                                     fresh n (Model.shiftn d) (Debruijn.name_body t')
  | _                             -> infer t >>= super_type d

and infer : Term.t -> Model.t M.t = fun t ->
  match t with
  | Term.Chk (t, t')          -> check_type t >>
                                 eval t       >>= fun d ->
                                 check t' d   >>
                                 M.pure d
  | Term.Unv k                -> M.pure (Model.Unv (k + 1))
  | Term.Fun (t, Term.Lam t') -> lub
                                 <$>  infer_type t
                                 <**> m_shiftv
                                        (eval t)
                                        (infer (Debruijn.var_body t'))
  | Term.Fun (t, t')          -> print_endline "Unsupported!";
                                 check_type t     >>
                                 infer t'         >>=
                                 is_fun           >>= fun (d1', d2') ->
                                 eval t           >>=
                                 equiv_type d1'   >>
                                 gen_var d1'      @@ fun v ->
                                 app (Model.shiftv d2') v >>=
                                 lub d1'
  | Term.Nab (t, Term.Alp t') -> check t Model.Nst >>
                                 m_shiftn
                                   (eval t)
                                   (infer (Debruijn.name_body t') >>= lub Model.Nst)
  | Term.Nab (t, t')          -> check t Model.Nst >>
                                 infer t'          >>=
                                 is_nab            >>= fun (d1', d2') ->
                                 eval t            >>=
                                 equiv_type d1'    >>
                                 gen_name d1' @@ fun n ->
                                 cnc (Model.shiftn d2') n >>=
                                 lub Model.Nst
  | Term.App (t, t')          -> infer t    >>=
                                 is_fun     >>= fun (d, d') ->
                                 check t' d >>
                                 eval t'    >>= fun v ->
                                 app d' v
  | Term.Cnc (t, n )          -> infer t           >>= fun d        ->
                                 is_nab d          >>= fun (d1, d2) ->
                                 lookup_name n     >>=
                                 sub_type d1       >>
                                 fresh (d1, n) d t >>
                                 cnc d2 (d1, n)
  | Term.Var v                -> lookup_var v
  | Term.Ref x                -> lookup_def x
  | Term.Tcn x                -> lookup_tcn x
  | Term.Dcn (x, i)           -> lookup_dcn x i
  | Term.Rec (x, l)           -> lookup_elim x l
  | Term.Nst                  -> M.pure (Model.Unv 1)
  | Term.Nam n                -> lookup_name n
  | Term.Nu (t, t')           -> check t Model.Nst >>
                                 eval t            >>= fun dn ->
                                 shiftn dn (
                                   infer (Debruijn.name_body t') >>= fun d' ->
                                   nu dn d' (Debruijn.name_body t')
                                 )
  | Term.Swp (n, m, t)        -> lookup_name n    >>= fun dn ->
                                 lookup_name m    >>= fun dm ->
                                 equiv_type dn dm >>= fun () ->
                                 Eval.swp n m <$> infer t
  | Term.Cmp (n, t)           -> lookup_name n >>=
                                 check t       >>
                                 M.pure Prelude.Model.mk_bool
  | Term.Lam _                -> failwith "Lambda abstraction not inferrable."
  | Term.Alp _                -> failwith "Alpha abstraction not inferrable."
  | Term.Let _                -> failwith "Can't infer type of local definition."
and check_type : Term.t -> unit M.t = fun t ->
  infer t >>= is_kind
and infer_type : Term.t -> Model.t M.t = fun t ->
  infer t   >>= fun d ->
  is_kind d >>
  M.pure d
and check_def : 'a 'b. Term.t -> Term.t -> 'a Debruijn.var -> ('a -> 'b M.t) -> 'b M.t = fun t1 t1' t2 f ->
  check_type t1 >>
  eval t1       >>= fun d1  ->
  check t1' d1  >>
  eval t1'      >>= fun d1' ->
  extend_var d1 d1' @@
  f (Debruijn.var_body t2)

let rec check_spine : (Term.t, Name.t) Spine.t -> Model.telescope -> unit M.t = fun t d ->
  match t, d with
  | Spine.Comma (t', t), Model.Telescope.Fn (d, d') ->
      check t d  >>
      eval t     >>=
      app_tcn d' >>=
      check_spine t'
  | Spine.Ortho (t', n), Model.Telescope.Na (d, d') ->
      lookup_name n     >>=
      sub_type d        >>
      cnc_tcn d' (d, n) >>=
      check_spine t'
  | Spine.Empty        , Model.Telescope.Up _       ->
      M.pure ()
  | Spine.Comma _      , Model.Telescope.Na _
  | Spine.Comma _      , Model.Telescope.Up _       ->
      fail @@ Failure.NotTcFn (d, t)
  | Spine.Ortho _      , Model.Telescope.Fn _
  | Spine.Ortho _      , Model.Telescope.Up _       ->
      fail @@ Failure.NotTcNa (d, t)
  | Spine.Empty        , Model.Telescope.Fn _
  | Spine.Empty        , Model.Telescope.Na _       ->
      fail @@ Failure.NotTcUp (d, t)

let rec check_ctx : (Term.t, Term.t) Context.t -> unit M.t = function
  | Context.Empty        -> M.pure ()
  | Context.Comma (c, t) -> check_ctx c >> check_type t      >> M.pure ()
  | Context.Ortho (c, t) -> check_ctx c >> check t Model.Nst >> M.pure ()
  
let rec check_tcn : (Term.t, Term.t, 'a) Telescope.t -> Model.level M.t = fun t ->
  match t with
  | Telescope.Fn (t, Debruijn.V (_, t')) -> check_type t >>
                                            m_shiftv (eval t) (check_tcn t')
  | Telescope.Na (t, Debruijn.N (_, t')) -> check t Model.Nst >>
                                            m_shiftn (eval t) (check_tcn t')
  | Telescope.Up t                       -> infer_type t >>= is_unv

let rec check_dcn : Term.constructor -> Binder.t -> Model.level -> Model.telescope -> unit M.t = fun t x l d ->
  match t with
  | Telescope.Fn (Sum.Inl t, Debruijn.V (_, t')) ->
      infer_type t >>=
      super_unv  l >>
      m_shiftv (eval t) (check_dcn t' x l d)
  | Telescope.Fn (Sum.Inr t, Debruijn.V (_, t')) ->
      check_dcn_rec t x l d >>
      m_shiftv (eval_dcn_rec t x) (check_dcn t' x l d)
  | Telescope.Na (t, Debruijn.N (_, t')) ->
      check t Model.Nst     >>
      super_unv l Model.Nst >>
      m_shiftn (eval t) (check_dcn t' x l d)
  | Telescope.Up t ->
      check_spine t d >>
      M.pure ()

and check_dcn_rec : Term.t Constructor.arg_rec -> Binder.t -> Model.level -> Model.telescope -> unit M.t = fun t x l d ->
  match t with
  | Telescope.Fn (t, Debruijn.V (_, t')) ->
      infer_type t >>=
      super_unv  l >>
      m_shiftv (eval t) (check_dcn_rec t' x l d)
  | Telescope.Na (t, Debruijn.N (_, t')) ->
      check t Model.Nst     >>
      super_unv l Model.Nst >>
      m_shiftn (eval t) (check_dcn_rec t' x l d)
  | Telescope.Up t       ->
      check_spine t d

let check_dcn_list : type n. (n, Term.constructor) Vec.t -> Binder.t -> Model.level -> Model.telescope -> (n, Model.constructor) Vec.t M.t = fun t x l d ->
  let module A = Monad.ToApplicative (M) in
  let module T = Traversable.Vec     (A) in
  T.traverse (fun t -> check_dcn t x l d >> eval_dcn t) t

let rec check_file : Term.file -> unit M.t = function
  | File.Defn (t, t', Named.Opt.Bound (x, f)) ->
      check_type t >>
      eval t       >>= fun d  ->
      check t' d   >>
      eval t'      >>= fun d' ->
      extend_defn x d d' (check_file f)
  | File.Data (t, Named.Bound (x, Named.Vec.Bound (cs, (_, f)))) ->
      check_tcn      t        >>= fun l    ->
      eval_tcn       t        >>= fun d    ->
      check_dcn_list cs x l d >>= fun d_cs ->
      extend_data x d d_cs (fun l -> Term.elim_type x l t cs) (Vec.map Term.method_term cs)
        (check_file f)
  | File.Done ->
     M.pure ()
