type t =
  | NotFreshType of Name.t * Model.t
  | NotFreshTerm of Name.t * Term.t
  | NotEquiv     of Delta.t * (Model.t, Model.t) Context.t * Model.s * Model.t * Model.t * Model.t
  | NotSubType   of Model.t * Model.t
  | NotFun       of Model.t
  | NotNab       of Model.t
  | NotTcFun     of Model.t * (Term.t, Name.t) Spine.t
  | NotTcFn      of Model.telescope * (Term.t, Name.t) Spine.t
  | NotTcNab     of Model.t * (Term.t, Name.t) Spine.t
  | NotTcNa      of Model.telescope * (Term.t, Name.t) Spine.t
  | NotTcUp      of Model.telescope * (Term.t, Name.t) Spine.t
  | NotUnv       of Model.t
  | NegUnvLevel  of Model.level
  | NotSubUnv    of Model.level * Model.level
  | NotSubNst    of Model.level
  | UnboundVar   of (Model.t, Model.t) Context.t * Var.t
  | UnboundName  of (Model.t, Model.t) Context.t * Name.t
  | UnboundDefn  of Delta.t * Binder.t
  | UnboundTcn   of Delta.t * Binder.t
  | UnboundDcn   of Delta.t * Binder.t * int
  | UnboundRec   of Delta.t * Binder.t

let to_code : t -> Failure_code.t = fun t ->
  let open Failure_code in
  match t with
  | NotFreshType _ -> NOT_FRESH_TYPE
  | NotFreshTerm _ -> NOT_FRESH_TERM
  | NotEquiv     _ -> NOT_EQUIV
  | NotSubType   _ -> NOT_SUB_TYPE
  | NotFun       _ -> NOT_FUN
  | NotNab       _ -> NOT_NAB
  | NotUnv       _ -> NOT_UNV
  | NegUnvLevel  _ -> NEG_UNV_LEVEL
  | NotSubUnv    _ -> NOT_SUB_UNV
  | UnboundVar   _ -> UNBOUND_VAR
  | UnboundName  _ -> UNBOUND_NAME
  | UnboundRec   _ -> UNBOUND_REC
  | UnboundTcn   _ -> UNBOUND_TCN
  | _              -> failwith "TODO code"

let to_string : t -> string = fun t ->
  Failure_code.to_string (to_code t)
