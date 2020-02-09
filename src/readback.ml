module Triple = struct
  type ('a,'b,'c) t = 'a * 'b * 'c

  let map3 f (x,y,z) = (x,y,f z)
end

exception Rb_failure     of string * Model.t    * Model.t

let simple_fun : Model.t -> Model.t -> Model.t = fun t t' ->
  Model.Fun (t, Model.New (Model.Vl (Model.Cls (None, Term.Var (Var.V Var.Z), Context.Comma (Context.Empty, t')))))
let simple_nab : Model.t -> Model.t -> Model.t = fun t t' ->
  Model.Nab (t, Model.New (Model.Vl (Model.Alp (None, Term.Var (Var.N Var.Z), Context.Comma (Context.Empty, t')))))

let rec rb_rid : (unit, unit) Context.t -> Model.t -> (Model.t, Model.t * Name.t) Spine.t -> Model.t_ne -> _ -> (Normal.nf, Name.t) Spine.t -> Delta.t -> Normal.ne = fun c d di dt mk s f ->
  match d, di with
  | Model.Fun (d1, d2), Spine.Comma (d2', d1') -> rb_rid c (Eval.app d2 d1' f) d2' dt mk (Spine.Comma (s, rb c d1 d1' f)) f
  | Model.Nab (_ , d2), Spine.Ortho (d2', n1') -> rb_rid c (Eval.cnc d2 n1' f) d2' dt mk (Spine.Ortho (s, snd n1'))       f
  | _                 , Spine.Empty            -> mk s (rb_ne c dt f)
  | _                                          -> failwith "rb_id"

and rb_rme : (unit, unit) Context.t -> Model.t -> Model.t list -> (Model.t, Model.t * Name.t) Spine.t -> Model.t_ne -> _ -> Normal.nf list -> Delta.t -> Normal.ne = fun c d df di dt mk l f ->  
  match d, df with
  | Model.Fun (d1, d2), d1' :: df -> rb_rme c (Eval.app d2 d1' f) df di dt mk     (l @ [rb c d1 d1' f]) f
  | _                 , []        -> rb_rid c d                 di dt (mk l) Spine.Empty           f
  | _                             -> failwith "rb_rme"

and rb_rmo : (unit, unit) Context.t -> Model.t -> Model.t -> Model.t list -> (Model.t, Model.t * Name.t) Spine.t -> Model.t_ne -> _ -> Delta.t -> Normal.ne = fun c d dm df di dt mk f ->
  match d with
  | Model.Fun (d1, d2) -> rb_rme c (Eval.app d2 dm f) df di dt (mk (rb c d1 dm f)) [] f
  | _                  -> failwith "rb_rmo"

and rb_ne : (unit, unit) Context.t -> Model.t_ne -> Delta.t -> Normal.ne = fun c d f ->
  match d with
  | Model.Var (p, v )               -> Normal.Var (p, v)
  | Model.App (d, d')               -> Normal.App (rb_ne c d f, rb_nf c d' f)
  | Model.Cnc (d, n )               -> Normal.Cnc (rb_ne c d f, n)
  | Model.Rne (x, l, d, dm, di, dt) -> rb_rmo c (Eval.eval (Eval.lookup_elim x f l) Context.Empty f) d dm di dt (Normal.mk_rne x l) f
  | Model.Cmp (n, d)                -> Normal.Cmp (n, rb_ne c d f)

and rb_tcn_spine : (unit, unit) Context.t -> Model.telescope -> (Model.t, Model.t * Name.t) Spine.t -> Delta.t -> (Normal.nf, Name.t) Spine.t = fun c d d' f ->
  match d, d' with
  | Model.Telescope.Fn (d1, d2), Spine.Comma (d2', d1') -> Spine.Comma (rb_tcn_spine c (Eval.app_tcn d2 d1' f) d2' f, rb c d1 d1' f)
  | Model.Telescope.Na (_ , d2), Spine.Ortho (d2', n1') -> Spine.Ortho (rb_tcn_spine c (Eval.cnc_tcn d2 n1' f) d2' f, snd n1')
  | Model.Telescope.Up _       , Spine.Empty            -> Spine.Empty
  | _ -> failwith "Internal error: encountered ill-typed spine during read-back."

and rb_dcn_spine_rec : Binder.t -> (unit, unit) Context.t -> (Model.t, Model.t, Term.t Constructor.arg_rec, Model.spine) Model.Telescope.t -> Model.t -> Delta.t -> Normal.nf = fun x c d d' f ->
  match d with
  | Model.Telescope.Fn (d1, ((y,_,_) as d2)) ->
      let v = Eval.fresh_var c d1 in                                                               (*TODO shift? *)
      Normal.Rnf (Normal.Vl (Normal.Lam (Debruijn.V (y, rb_dcn_spine_rec x (Context.comma c ()) (Eval.app_dcn_rec (Triple.map3 (Model.wkv_spine Var.Z) d2) v f) (Eval.app (Model.shiftv d') v f) f))))
  | Model.Telescope.Na (d1, ((y,_,_) as d2)) ->
      let n = Eval.fresh_name d1 in
      Normal.Rnf (Normal.Vl (Normal.Alp (Debruijn.N (y, rb_dcn_spine_rec x (Context.ortho c ()) (Eval.cnc_dcn_rec (Triple.map3 (Model.wkn_spine Name.Z) d2) n f) (Eval.cnc (Model.shiftn d') n f) f))))
  | Model.Telescope.Up d     -> rb c (Model.New (Model.Vl (Model.Tcn (x, d)))) d' f (*failwith "TODO Normal.Rnf (Normal.Vl (rb_vl c d' f))"*)

and rb_dcn_spine : Binder.t -> (unit, unit) Context.t -> Model.constructor -> (Model.t, Model.t * Name.t) Spine.t -> Delta.t -> (Normal.nf, Name.t) Spine.t = fun x c d d' f ->
  match d, d' with
  | Model.Telescope.Fn (Sum.Inl d1, d2), Spine.Comma (d2', d1') -> Spine.Comma (rb_dcn_spine x c (Eval.app_dcn d2 d1' f) d2' f, rb c d1 d1' f)
  | Model.Telescope.Fn (Sum.Inr d1, d2), Spine.Comma (d2', d1') -> Spine.Comma (rb_dcn_spine x c (Eval.app_dcn d2 d1' f) d2' f, rb_dcn_spine_rec x c d1 d1' f)
  | Model.Telescope.Na (        _ , d2), Spine.Ortho (d2', n1') -> Spine.Ortho (rb_dcn_spine x c (Eval.cnc_dcn d2 n1' f) d2' f, snd n1')
  | Model.Telescope.Up _               , Spine.Empty            -> Spine.Empty
  | _ -> failwith "TODO"

and rb_vl : (unit, unit) Context.t -> Model.t_vl -> Delta.t -> Normal.vl = fun c d f ->
  match d with
  | Model.Up  (_, d)    -> Normal.Neu (rb_ne c d f)
  | Model.Tcn (x,    d) -> Normal.Tcn (x,    rb_tcn_spine   c (Eval.lookup_tcn x   f) d f)
  | Model.Dcn (x, i, d) -> Normal.Dcn (x, i, rb_dcn_spine x c (Eval.lookup_dcn x i f) d f)
  | Model.Rmo _
  | Model.Rme _
  | Model.Rid _
  | Model.Alp _
  | Model.Cls _         -> failwith "Encountered ill-typed value during readback."

and rb_nu : (unit, unit) Context.t -> Model.t_nu -> Delta.t -> Normal.rnf = fun c d f ->
  match d with
  | Model.Nu (d, d') -> Normal.nu_rnf (rb c Model.Nst d f) (rb_nu_name c d' f)
  | Model.Vl d       -> Normal.Vl (rb_vl c d f)
and rb_nu_name : (unit, unit) Context.t -> Model.t_nu Debruijn.name -> Delta.t -> Normal.rnf Debruijn.name = fun c d f ->
  match d with
  | Debruijn.N (x, d) -> Debruijn.N (x, rb_nu (Context.ortho c ()) d f)

and rb : (unit, unit) Context.t -> Model.t -> Model.t -> Delta.t -> Normal.nf = fun c d d' f ->
  match d, d' with
  | Model.Fun (d1, d2), _ ->
      let v = Eval.fresh_var c d1 in
      Normal.Rnf (Normal.Vl (Normal.Lam (Debruijn.V (None, rb (Context.comma c ()) (Eval.app (Model.shiftv d2) v f) (Eval.app (Model.shiftv d') v f) f))))
  | Model.Nab (d1, d2), _ ->
      let n = Eval.fresh_name d1 in
      Normal.Rnf (Normal.Vl (Normal.Alp (Debruijn.N (None, rb (Context.ortho c ()) (Eval.cnc (Model.shiftn d2) n f) (Eval.cnc (Model.shiftn d') n f) f))))
  | Model.Unv _, Model.Unv l ->
      Normal.Unv l
  | Model.Unv _, Model.Nst ->
      Normal.Nst
  (* d2' might live in Nst but that's ok because all inhabitants of Nst are neutral. *)
  | Model.Unv _, Model.Fun (d1', d2') ->
      let a = (simple_fun d1' Model.unv_syn) in
      Normal.Fun (rb c d d1' f, rb c a d2' f)
  | Model.Unv _, Model.Nab (d1', d2') ->
      let a = (simple_nab d1' Model.unv_syn) in
      Normal.Nab (rb c d d1' f, rb c a d2' f)
  | _, Model.Nam (_, a) ->
      Normal.Nam a
  | _, Model.New d' ->
      Normal.Rnf (rb_nu c d' f)
  | _ -> raise (Rb_failure ("Encountered ill-typed value during readback.", d, d'))
and rb_nf : (unit, unit) Context.t -> Model.t_nf -> Delta.t -> Normal.nf = fun c d ->
  match d with
  | Model.Dwn (d, d') -> rb c d d'
  
let rec eval_context : (Term.t, Term.t) Context.t -> Delta.t -> Model.s = fun g f ->
  match g with
  | Context.Empty ->
      Context.Empty
  | Context.Comma (g, t) ->
      let r = Model.wkv_s Var.Z (eval_context g f) in
      Context.Comma (r, Model.New (Model.Vl (Model.Up (Eval.eval t r f, Model.Var (Table.wkv Var.Z (Table.from_context g), Var.Z)))))
  | Context.Ortho (g, t) ->
      let r = Model.wkn_s Name.Z (eval_context g f) in
      Context.Ortho (r, (Eval.eval t r f, Name.Z))

let rec rb_dcn : Binder.t -> (unit, unit) Context.t -> Model.telescope -> Model.constructor -> Delta.t -> Normal.constructor = fun x c d t f ->
  match t with
  | Model.Telescope.Fn (Sum.Inl t, ((y,_,_) as t')) ->
      let v = Eval.fresh_var c t in
      Telescope.mk_fn (Sum.Inl (rb c Model.unv_syn t f)) y (rb_dcn x (Context.comma c ()) d (Eval.app_dcn (Triple.map3 (Model.wkv_spine Var.Z) t') v f) f)
  | Model.Telescope.Fn (Sum.Inr t, ((y,_,_) as t')) ->
      let v = Eval.fresh_var c (Model.constructor_to_term_arg x t) in
      Telescope.mk_fn (Sum.Inr (rb_dcn_rec c d t f)) y (rb_dcn x (Context.comma c ()) d (Eval.app_dcn (Triple.map3 (Model.wkv_spine Var.Z) t') v f) f)
  | Model.Telescope.Na (        t, ((y,_,_) as t')) ->
      let n = Eval.fresh_name t in
      Telescope.mk_na (rb c Model.Nst t f) y (rb_dcn x (Context.ortho c ()) d (Eval.cnc_dcn (Triple.map3 (Model.wkn_spine Name.Z) t') n f) f)
  | Model.Telescope.Up t                            -> Telescope.mk_up (rb_tcn_spine c d t f)

and rb_dcn_rec : (unit, unit) Context.t -> Model.telescope -> (Model.t, Model.t, Term.t Constructor.arg_rec, Model.spine) Model.Telescope.t -> Delta.t -> Normal.nf Constructor.arg_rec = fun c d t f ->
  match t with
   | Model.Telescope.Fn (t, ((x,_,_) as t')) -> Telescope.mk_fn (rb c Model.unv_syn t f) x (rb_dcn_rec (Context.comma c ()) d (Eval.app_dcn_rec t' (Eval.fresh_var c t) f) f)
   | Model.Telescope.Na (t, ((x,_,_) as t')) -> Telescope.mk_na (rb c Model.Nst     t f) x (rb_dcn_rec (Context.ortho c ()) d (Eval.cnc_dcn_rec t' (Eval.fresh_name t) f) f)
   | Model.Telescope.Up t                    -> Telescope.mk_up (rb_tcn_spine c d t f)

let rec rb_tcn : (unit, unit) Context.t -> Model.telescope -> Delta.t -> Normal.telescope = fun c t f ->
  match t with
  | Model.Telescope.Fn (t, ((x,_,_) as t')) -> Telescope.mk_fn (rb c Model.unv_syn t f) x (rb_tcn (Context.comma c ()) (Eval.app_tcn t' (Eval.fresh_var c t) f) f)
  | Model.Telescope.Na (t, ((x,_,_) as t')) -> Telescope.mk_fn (rb c Model.Nst     t f) x (rb_tcn (Context.ortho c ()) (Eval.cnc_tcn t' (Eval.fresh_name  t) f) f)
  | Model.Telescope.Up t                    -> Telescope.mk_up (rb c Model.unv_syn t f)

let rec rb_file : Model.file -> Delta.t -> Normal.file = fun t f ->
  match t with
  | Model.Defn (d, d', Named.Opt.Bound (x, t)) ->
      let n  = rb Context.empty Model.unv_syn d  f in
      let n' = rb Context.empty d             d' f in
      File.mk_defn x n n' (rb_file t (Delta.mk_defn x d d' f))
  | Model.Data (dc, Named.Bound (x, Named.Vec.Bound (d_cs, (xs, t)))) ->
      let nc   = rb_tcn Context.empty dc f in
      let tc   = Normal.to_term_tcn nc in
      let n_cs = Vec.map (fun c -> rb_dcn x Context.Empty dc c f) d_cs in
      let t_cs = Normal.to_term_constr_list n_cs in
      File.mk_data x xs nc n_cs (rb_file t (Delta.mk_data x dc d_cs (fun l -> Term.elim_type x l tc t_cs) (Vec.map Term.method_term t_cs) f))
  | Model.Done ->
     File.Done
