open Function

exception App_vl_failure of string * Model.t_vl * Model.t

let rec swp_ne : Name.t -> Name.t -> Model.t_ne -> Model.t_ne = fun a a' d ->
  match d with
  | Model.Var (p, v )               -> Model.Var (Table.swp a a' p, v)
  | Model.App (d, d')               -> Model.App (swp_ne a a' d, swp_nf a a' d')
  | Model.Cnc (d, b )               -> Model.Cnc (swp_ne a a' d, Name.swp a a' b)
  | Model.Rne (x, l, d, dm, di, dt) -> Model.Rne (x, l, swp a a' d, List.map (swp a a') dm, swp_spine a a' di, swp_ne a a' dt)
  | Model.Cmp (b, d)                -> Model.Cmp (Name.swp a a' b , swp_ne   a a' d)

and swp_s :  Name.t -> Name.t -> Model.s -> Model.s = fun a a' ->
  Context.map (swp a a') (Product.map (swp a a') (Name.swp a a'))

and swp : Name.t -> Name.t -> Model.t -> Model.t = fun a b d ->
  match d with
  | Model.Fun (d, d') -> Model.Fun (swp a b d, swp a b d')
  | Model.Nab (d, d') -> Model.Nab (swp a b d, swp a b d')
  | Model.Unv _
  | Model.Nst         -> d
  | Model.Nam (d,k)   -> Model.Nam (swp a b d, Name.swp a b k)
  | Model.New d       -> Model.New (swp_nu a b d)

and swp_vl : Name.t -> Name.t -> Model.t_vl -> Model.t_vl = fun a b d ->
  match d with
  | Model.Cls (x, t, s )         -> Model.Cls (x, t, swp_s  a b s )
  | Model.Alp (x, t, s )         -> Model.Alp (x, t, swp_s  a b s )
  | Model.Tcn (x, d)             -> Model.Tcn (x,    swp_spine a b d)
  | Model.Dcn (x, i, d)          -> Model.Dcn (x, i, swp_spine a b d)
  | Model.Rmo (x, l)             -> Model.Rmo (x, l)
  | Model.Rme (x, l, dm, df)     -> Model.Rme (x, l, swp a b dm, List.map (swp a b) df)
  | Model.Rid (x, l, dm, df, di) -> Model.Rid (x, l, swp a b dm, List.map (swp a b) df, swp_spine a b di)
  | Model.Up  (d, d')            -> Model.Up  (swp a b d, swp_ne a b d')

and swp_spine : Name.t -> Name.t -> (Model.t, Model.t * Name.t) Spine.t -> (Model.t, Model.t * Name.t) Spine.t = fun a b ->
  Spine.map (swp a b) (Product.map (swp a b) (Name.swp a b))

and swp_nu : Name.t -> Name.t -> Model.t_nu -> Model.t_nu = fun a b d ->
  match d with
  | Model.Nu (d, d') -> Model.Nu (swp a b d, swp_nu_name a b d')
  | Model.Vl d       -> Model.Vl (swp_vl a b d)
and swp_nu_name : Name.t -> Name.t -> Model.t_nu Debruijn.name -> Model.t_nu Debruijn.name = fun a b d ->
  match d with
  | Debruijn.N (x, d) -> Debruijn.N (x, swp_nu (Name.N a) (Name.N b) d)

and swp_nf : Name.t -> Name.t -> Model.t_nf -> Model.t_nf = fun a b d ->
  match d with
  | Model.Dwn (d, d') -> Model.Dwn (swp a b d, swp a b d')

let lookup_name : Model.s -> Name.t -> Model.t * Name.t = fun g i ->
  Error.String.catch (Context.lookup_name g i) failwith
                                           
let lookup_var : Model.s -> Var.t -> Model.t = fun r v ->
  Error.String.catch (Context.lookup_var r v) failwith

let lookup_def : Binder.t -> Delta.t -> Model.t = fun x f ->
  Option.fold snd (fun () -> failwith @@ "Definition '" ^ x ^ "' not found in environment") (Delta.lookup_def x f)

let lookup_tcn : Binder.t -> Delta.t -> Model.telescope = fun x f ->
  Option.fold id (fun () -> failwith @@ "Definition '" ^ x ^ "' not found in environment") (Delta.lookup_tcn x f)

let lookup_tcn_length : Binder.t -> Delta.t -> int = fun x f ->
  Option.fold id (fun () -> failwith @@ "Definition '" ^ x ^ "' not found in environment") (Delta.lookup_tcn_length x f)

let lookup_dcn : Binder.t -> int -> Delta.t -> Model.constructor = fun x i f ->
  Option.fold id (fun () -> failwith @@ "Definition '" ^ x ^ "' not found in environment") (Delta.lookup_dcn x i f)

let lookup_dcn_length : Binder.t -> Delta.t -> int = fun x f ->
  Option.fold id (fun () -> failwith @@ "Definition '" ^ x ^ "' not found in environment") (Delta.lookup_dcn_length x f)

let lookup_elim : Binder.t -> Delta.t -> (Model.level -> Term.t) = fun x f ->
  Option.fold id (fun () -> failwith @@ "Definition '" ^ x ^ "' not found in environment") (Delta.lookup_elim x f)

let lookup_method : Binder.t -> int -> Delta.t -> Term.t = fun x i f ->
  Option.fold id (fun () -> failwith @@ "Definition '" ^ x ^ "' not found in environment") (Delta.lookup_method x i f)

let rec nu : Binder.t_opt -> Model.t -> Model.t -> Model.t = fun x d d' ->
  match d' with
  | Model.Unv _
  | Model.Nst                 -> d'
  | Model.Nam (_, Name.Z  )   -> failwith "Freshness violated!"
  | Model.Nam (_, Name.V _)   -> failwith "Ill-kinded name/name."
  | Model.Nam (d1', Name.N a) -> Model.Nam (d1', a)
  | Model.Fun (d1', d2')      -> Model.Fun (nu x d d1', nu x d d2') (* TODO check! Assuming injectivity, ought to be ok. *)
  | Model.Nab (d1', d2')      -> Model.Nab (nu x d d1', nu x d d2')
  | Model.New d'              -> Model.New (Model.Nu (d, Debruijn.N (x, d')))

let rec cmp_atom_vl : Name.t -> Model.t_vl -> Model.t = fun a d ->
  match d with
  | Model.Up (_, d) -> Model.New (Model.Vl (Model.Up (Prelude.Model.mk_bool, Model.Cmp (a, d))))
  | _               -> failwith "Ill-type name comparison."

and cmp_atom_nu : Name.t -> Model.t_nu -> Model.t = fun a d ->
  match d with
  | Model.Nu (d, Debruijn.N (x, d')) -> nu x d (cmp_atom_nu (Name.sn a) d')
  | Model.Vl d                       -> cmp_atom_vl a d

and cmp_atom : Name.t -> Model.t -> Model.t = fun a d ->
  match d with
  | Model.Nam (_, b) -> if a = b then Prelude.Model.mk_true else Prelude.Model.mk_false
  | Model.New d -> cmp_atom_nu a d
  | _ -> failwith "Ill-type name comparison."

let rec app_rid : Binder.t -> int -> Model.t -> Model.t list -> (Model.t, Model.t * Name.t) Spine.t -> Model.t -> Delta.t -> Model.t = fun x l dm df di d' f ->
  if Spine.length di < lookup_tcn_length x f then
    Model.New (Model.Vl (Model.Rid (x, l, dm, df, Spine.mult di (Spine.Comma (Spine.Empty, d')))))
  else
    eval_rec x l dm df di d' f

and app_rme : Binder.t -> int -> Model.t -> Model.t list -> Model.t -> Delta.t -> Model.t = fun x l dm df d' f ->
  if List.length df < lookup_dcn_length x f then
    Model.New (Model.Vl (Model.Rme (x, l, dm, df @ [d'])))
  else
    app_rid x l dm df Spine.Empty d' f

and app_vl : Model.t_vl -> Model.t -> Delta.t -> Model.t = fun d d' f ->
  match d with
  | Model.Cls (_, t, r) ->
      eval t (Context.Comma (r, d')) f
  | Model.Up (Model.Fun (d1, d2), d) ->
      Model.New (Model.Vl (Model.Up (app d2 d' f, Model.App (d, Model.Dwn (d1, d')))))
  | Model.Tcn (x, s) ->
      Model.New (Model.Vl (Model.Tcn (x,    Spine.mult s (Spine.comma Spine.empty d'))))
  | Model.Dcn (x, i, s) ->
      Model.New (Model.Vl (Model.Dcn (x, i, Spine.mult s (Spine.comma Spine.empty d'))))
  | Model.Rmo (x, l) ->
      Model.New (Model.Vl (Model.Rme (x, l, d', [])))
  | Model.Rme (x, l, dm, df) ->
      app_rme x l dm df d' f
  | Model.Rid (x, l, dm, df, di) ->
      app_rid x l dm df di d' f
  | _ -> raise (App_vl_failure ("Not a function abstraction!", d, d'))

and app_nu : Model.t_nu -> Model.t -> Delta.t -> Model.t = fun d d' f ->
  match d with
   | Model.Nu (d1, Debruijn.N (x, d2)) -> nu x d1 (app_nu d2 (Model.shiftn d') f)
   | Model.Vl d                        -> app_vl d d' f

and app : Model.t -> Model.t -> Delta.t -> Model.t = fun d d' ->
  match d with
  | Model.New d -> app_nu d d'
  | _           -> failwith "Not a function abstraction."

and app_spine : Model.t -> (Model.t, Model.t * Name.t) Spine.t -> Delta.t -> Model.t = fun d ds f ->
  match ds with
  | Spine.Comma (ds, d') -> app_spine (app d d' f) ds f
  | Spine.Ortho (ds, n') -> app_spine (cnc d n' f) ds f
  | Spine.Empty          -> d

and app_list : Model.t -> Model.t list -> Delta.t -> Model.t = fun d df f ->
  match df with
  | d' :: df -> app_list (app d d' f) df f
  | []       -> d

and cnc_vl : Model.t_vl -> (Model.t * Name.t) -> Delta.t -> Model.t = fun d a f ->
  match d with
  | Model.Alp (x, t, r) ->
     nu x (fst a) (swp Name.Z (Name.N (snd a)) (eval t (Model.shiftn_s (fst a) r) f))
  | Model.Up (Model.Nab (_, d2), d) ->
     Model.(New (Vl (Up (cnc d2 a f, Cnc (d, snd a)))))
  | Model.Tcn (x, d) ->
      nu None (fst a) (swp Name.Z (Name.N (snd a)) Model.(New (Vl (Tcn (x,    Spine.mult (Model.wkn_s Name.Z d) (Spine.ortho Spine.empty (Model.shiftn (fst a), Name.Z)))))))
  | Model.Dcn (x, i, d) ->
      nu None (fst a) (swp Name.Z (Name.N (snd a)) Model.(New (Vl (Dcn (x, i, Spine.mult (Model.wkn_s Name.Z d) (Spine.ortho Spine.empty (Model.shiftn (fst a), Name.Z)))))))
  | _ -> failwith "Not a name abstraction!"

and cnc_nu : Model.t_nu -> (Model.t * Name.t) -> Delta.t -> Model.t = fun d a f ->
  match d with
  | Model.Nu (d, Debruijn.N (x, d')) -> nu x d (cnc_nu d' (Model.shiftn (fst a), Name.N (snd a)) f)
  | Model.Vl d                       -> cnc_vl d a f

and cnc : Model.t -> (Model.t * Name.t) -> Delta.t -> Model.t = fun d a ->
  match d with
  | Model.New d -> cnc_nu d a
  | _ -> failwith "Not a name abstraction!"

and eval : Term.t -> Model.s -> Delta.t -> Model.t = fun t r f ->
  match t with
  | Term.Unv l                       -> Model.Unv l
  | Term.Nst                         -> Model.Nst
  | Term.Fun (t, t')                 -> Model.Fun (eval t r f, eval t' r f)
  | Term.Nab (t, t')                 -> Model.Nab (eval t r f, eval t' r f)
  | Term.Lam (Debruijn.V (x, t))     -> Model.New (Model.Vl (Model.Cls (x, t, r)))
  | Term.Alp (Debruijn.N (x, t))     -> Model.New (Model.Vl (Model.Alp (x, t, r)))
  | Term.App (t, t')                 -> app (eval t r f) (eval t' r f) f
  | Term.Cnc (t, n)                  -> cnc (eval t r f) (lookup_name r n) f
  | Term.Swp (n, m, t)               -> swp (snd (lookup_name r n)) (snd (lookup_name r m)) (eval t r f)
  | Term.Nu  (t, Debruijn.N (x, t')) -> let d = eval t (*TODO check: Model.wkn_s Name.Z r*) r f in
                                        nu x d (eval t' (Model.shiftn_s d r) f)
  | Term.Cmp (n, t)                  -> cmp_atom (snd (lookup_name r n)) (eval t r f)
  | Term.Var v                       -> lookup_var r v
  | Term.Nam n                       -> let (d, a) = lookup_name r n in
                                        Model.Nam (d, a)
  | Term.Let (_, t1, t2)             -> eval (Debruijn.var_body t2) Model.(comma r (eval t1 r f)) f
  | Term.Ref x                       -> lookup_def x f
  | Term.Tcn x                       -> Model.New (Model.Vl (Model.Tcn (x,    Spine.empty)))
  | Term.Dcn (x, i)                  -> Model.New (Model.Vl (Model.Dcn (x, i, Spine.empty)))
  | Term.Rec (x, l)                  -> Model.New (Model.Vl (Model.Rmo (x, l)))
  | Term.Chk (_, t')                 -> eval t' r f

and eval_rec_vl : string -> int -> Model.t -> Model.t list -> (Model.t, Model.t * Name.t) Spine.t -> Model.t_vl -> Delta.t -> Model.t = fun x l d_motive d_methods d_indices d_target f ->
  match d_target with
  | Model.Dcn (y, i, s) when x = y ->
      let t = lookup_method x i f in
      let e = Model.New (Model.Vl (Model.Rme (x, l, d_motive, d_methods))) in
      let m = List.nth d_methods i in
      let r = Spine.fold (Context.(Comma (Comma (Empty, e), m))) Context.comma Context.ortho s in
      eval t r f
  | Model.Up (_, d_target_ne) ->
      Model.New (Model.Vl (Model.Up (app (app_spine d_motive d_indices f) (Model.New (Model.Vl d_target)) f, Model.Rne (x, l, d_motive, d_methods, d_indices, d_target_ne))))
  | _ -> failwith @@ "Expected a term belonging to data type '" ^ x ^ "'."

and eval_rec_nu : string -> int -> Model.t -> Model.t list -> (Model.t, Model.t * Name.t) Spine.t -> Model.t_nu -> Delta.t -> Model.t = fun x l d_motive d_methods d_indices d f ->
  match d with
  | Model.Nu (d1, Debruijn.N (y, d2)) -> nu y d1 (eval_rec_nu x l (Model.shiftn d_motive) (List.map Model.shiftn d_methods) (Model.wkn_spine Name.Z d_indices) d2 f)
  | Model.Vl d                        -> eval_rec_vl x l d_motive d_methods d_indices d  f

and eval_rec : string -> int -> Model.t -> Model.t list -> (Model.t, Model.t * Name.t) Spine.t -> Model.t -> Delta.t -> Model.t = fun x l d_motive d_methods d_indices d f ->
  match d with
  | Model.New d -> eval_rec_nu x l d_motive d_methods d_indices d f
  | _           -> failwith "eval_rec"

let fresh_var : _ Context.t -> Model.t -> Model.t = fun c d ->
  Model.New (Model.Vl (Model.Up (Model.shiftv d, Model.Var (Table.wkv Var.Z (Table.from_context c), Var.Z))))

let fresh_name : Model.t -> Model.t * Name.t = fun d ->
  Model.shiftn d, Name.Z

let rec eval_telescope : Term.telescope -> Model.s -> Delta.t -> (Model.t, Model.t, Model.t) Telescope.t = fun t r f ->
  match t with
  | Telescope.Fn (t, Debruijn.V (x, t')) ->
      let d  = eval           t  r                                  f in
      let d' = eval_telescope t' (Context.Comma (r, fresh_var r d)) f in
      Telescope.Fn (d, Debruijn.V (x, d'))
  | Telescope.Na (t, Debruijn.N (x, t')) ->
      let d  = eval           t  r                                  f in
      let d' = eval_telescope t' (Context.Ortho (r, fresh_name  d)) f in
      Telescope.Na (d, Debruijn.N (x, d'))      
  | Telescope.Up t                       ->
      let d =  eval           t r                                   f in
      Telescope.Up d

let eval_tcn : Term.telescope -> Model.s -> Delta.t -> Model.telescope = fun t r f ->
  match t with
  | Telescope.Fn (t, Debruijn.V (x, t')) -> Model.Telescope.Fn (eval t r f, (x, t', r))
  | Telescope.Na (t, Debruijn.N (x, t')) -> Model.Telescope.Na (eval t r f, (x, t', r))
  | Telescope.Up t                       -> Model.Telescope.Up (eval t r f)

let app_tcn : Binder.t_opt * Term.telescope * Model.s -> Model.t -> Delta.t -> Model.telescope = fun (_, t, r) d' f ->
  eval_tcn t (Context.Comma (r, d')) f

let cnc_tcn : Binder.t_opt * Term.telescope * Model.s -> Model.t * Name.t -> Delta.t -> Model.telescope = fun (_, t, r) d' f ->
  eval_tcn t (Context.Ortho (r, d')) f

let eval_spine : Term.spine -> Model.s -> Delta.t -> Model.spine = fun t r f ->
  Spine.map (fun t -> eval t r f) (lookup_name r) t

let eval_dcn_rec : Term.t Constructor.arg_rec -> Model.s -> Delta.t -> (Model.t, Model.t, Term.t Constructor.arg_rec, Model.spine) Model.Telescope.t = fun t r f ->
  match t with
  | Telescope.Fn (t, Debruijn.V (x, t')) -> Model.Telescope.Fn (eval t r f, (x, t', r))
  | Telescope.Na (t, Debruijn.N (x, t')) -> Model.Telescope.Na (eval t r f, (x, t', r))
  | Telescope.Up t                       -> Model.Telescope.Up (eval_spine t r f)

let eval_dcn : Term.constructor -> Model.s -> Delta.t -> Model.constructor = fun t r f ->
  match t with
  | Telescope.Fn (Sum.Inl t, Debruijn.V (x, t')) -> Model.Telescope.Fn (Sum.Inl (eval         t r f), (x, t', r))
  | Telescope.Fn (Sum.Inr t, Debruijn.V (x, t')) -> Model.Telescope.Fn (Sum.Inr (eval_dcn_rec t r f), (x, t', r))
  | Telescope.Na (        t, Debruijn.N (x, t')) -> Model.Telescope.Na (         eval         t r f , (x, t', r))
  | Telescope.Up t                               -> Model.Telescope.Up (         eval_spine   t r f)

let app_dcn : Binder.t_opt * Term.constructor * Model.s -> Model.t -> Delta.t -> Model.constructor = fun (_, t, r) d' f ->
  eval_dcn t (Context.Comma (r, d')) f

let app_dcn_rec : Binder.t_opt * Term.t Constructor.arg_rec * Model.s -> Model.t -> Delta.t -> (Model.t, Model.t, Term.t Constructor.arg_rec, Model.spine) Model.Telescope.t = fun (_, t, r) d' f ->
  eval_dcn_rec t (Context.Comma (r, d')) f

let cnc_dcn : Binder.t_opt * Term.constructor * Model.s -> Model.t * Name.t -> Delta.t -> Model.constructor = fun (_, t, r) d' f ->
  eval_dcn t (Context.Ortho (r, d')) f

let cnc_dcn_rec : Binder.t_opt * Term.t Constructor.arg_rec * Model.s -> Model.t * Name.t -> Delta.t -> (Model.t, Model.t, Term.t Constructor.arg_rec, Model.spine) Model.Telescope.t = fun (_, t, r) d' f ->
  eval_dcn_rec t (Context.Ortho (r, d')) f

let eval_dcn_list : type n. (n, Term.constructor) Vec.t -> Model.s -> Delta.t -> (n, Model.constructor) Vec.t = fun cs r f ->
  Vec.map (fun t -> eval_dcn t r f) cs

let rec eval_file : Term.file -> Model.s -> Delta.t -> Model.file = fun t r f ->
  match t with
  | File.Defn (t, t', Named.Opt.Bound (x, tf)) ->
      let d  = eval      t  r f in
      let d' = eval      t' r f in
      let df = eval_file tf r (Delta.mk_defn x d d' f) in
      Model.mk_defn x d d' df
  | File.Data (t, Named.Bound (x, Named.Vec.Bound (cs, (xs, tf)))) ->
      let d  = eval_tcn t r f in
      let dc = eval_dcn_list cs r f in
      let df = eval_file tf r (Delta.mk_data x d dc (fun l -> Term.elim_type x l t cs) (Vec.map Term.method_term cs) f) in
      Model.mk_data x xs d dc df
  | File.Done ->
      Model.Done
