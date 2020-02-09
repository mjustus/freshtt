module Raw = struct
  let prepend_bool : Raw.file -> Raw.file = fun f ->
    let x  = "Bool" in
    let t  = Raw.Up (Raw.Unv 0) in
    let xs = Vec.(Cons ("true"            , Cons ("false"           , Nil))) in
    let cs = Vec.(Cons (Raw.Up Spine.Empty, Cons (Raw.Up Spine.Empty, Nil))) in
    Raw.Data (t, Named.Bound (x, Named.Vec.Bound (cs, (xs, f))))

  let mk_bool  : Raw.t = Raw.Idt "Bool"
  let mk_true  : Raw.t = Raw.Idt "true"
  let mk_false : Raw.t = Raw.Idt "false"
end

module Term = struct
  let prepend_bool : Term.file -> Term.file = fun f ->
    let x  = "Bool" in
    let t  = Telescope.Up (Term.Unv 0) in
    let xs = Vec.(Cons ("true"                  , Cons ("false"                 , Nil))) in
    let cs = Vec.(Cons (Telescope.Up Spine.Empty, Cons (Telescope.Up Spine.Empty, Nil))) in
    File.mk_data x xs t cs f

  let mk_bool  : Term.t = Term.Tcn "Bool"
  let mk_true  : Term.t = Term.Dcn ("Bool", 0)
  let mk_false : Term.t = Term.Dcn ("Bool", 1)
end

module Model = struct

  let mk_bool  : Model.t = Model.New (Model.Vl (Model.Tcn ("Bool"   , Spine.Empty)))
  let mk_true  : Model.t = Model.New (Model.Vl (Model.Dcn ("Bool", 0, Spine.Empty)))
  let mk_false : Model.t = Model.New (Model.Vl (Model.Dcn ("Bool", 1, Spine.Empty)))
end
