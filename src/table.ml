type perm = (unit, Name.t) Context.t

type t =
  | Perm  of perm
  | Comma of t
  | Ortho of t

let perm : perm -> t = fun p -> Perm p
let comma : t -> t = fun p -> Comma p
let ortho : t -> t = fun p -> Ortho p

let rec map : (Name.t -> Name.t) -> t -> t = fun f t ->
  match t with
  | Perm  p -> Perm  (Context.map_right f p)
  | Comma t -> Comma (map f t)
  | Ortho t -> Ortho (map f t)

let swp : Name.t -> Name.t -> t -> t = fun n n' ->
  map (Name.swp n n')

let wkn_entries : Name.t -> t -> t = fun n ->
  map (Name.wkn n)

let wkv_entries : Var.t -> t -> t = fun v ->
  map (Name.wkv v)

let rec wkn_columns : Name.t -> Name.t -> perm -> perm = fun n m p ->
  match n, p with
  | Name.Z  , _                    -> Context.Ortho (p, m)
  | Name.N n, Context.Ortho (p, k) -> Context.Ortho (wkn_columns n m p, k)
  | Name.V n, Context.Comma (p, k) -> Context.Comma (wkn_columns n m p, k)
  | _ -> failwith "Ill-kinded name/permutation."

let rec wkv_columns : Var.t -> perm -> perm = fun v p ->
  match v, p with
  | Var.Z  , _                    -> Context.Comma (p, ())
  | Var.N v, Context.Ortho (p, k) -> Context.Ortho (wkv_columns v p, k)
  | Var.V v, Context.Comma (p, k) -> Context.Comma (wkv_columns v p, k)
  | _ -> failwith "Ill-kinded name/permutation."

let rec wkn_cut : Name.t -> Name.t -> t -> t = fun n m t ->
  match n, t with
  | Name.Z  , _       -> Ortho t
  | _       , Perm  p -> Perm  (wkn_columns n m p)
  | Name.V n, Comma t -> Comma (wkn_cut n m t)
  | Name.N n, Ortho t -> Ortho (wkn_cut n m t)
  | _ -> failwith "Ill-kinded permutation weakening."
                                             
let rec wkv_cut : Var.t -> t -> t = fun v t ->
  match v, t with
  | Var.Z  , _       -> Comma t
  | _      , Perm p  -> Perm  (wkv_columns v p)
  | Var.V v, Comma t -> Comma (wkv_cut v t)
  | Var.N v, Ortho t -> Ortho (wkv_cut v t)
  | _ -> failwith "Ill-kinded permutation weakening."

let wkn : Name.t -> t -> t = fun n t ->
  wkn_cut n n (wkn_entries n t)

let wkv : Var.t -> t -> t = fun v t ->
  wkv_cut v (wkv_entries v t)

let rec perm_from_context : ('a, 'b) Context.t -> perm = fun c ->
  match c with
  | Context.Empty   ->
     Context.Empty
  | Context.Comma (c, _) ->
     let p = perm_from_context c in
     Context.Comma (Context.map_right (Name.wkv Var.Z ) p, ()    )
  | Context.Ortho (c, _) ->
     let p = perm_from_context c in
     Context.Ortho (Context.map_right (Name.wkn Name.Z) p, Name.Z)

let from_context : ('a, 'b) Context.t -> t = fun c ->
  Perm (perm_from_context c)

open Option.Operators

let rec rem_entries : Name.t -> t -> t option = fun n t ->
  match t with
  | Perm  p -> perm  <$> Context.map_option_right (Name.rem n) p
  | Comma t -> comma <$> rem_entries n t
  | Ortho t -> ortho <$> rem_entries n t

let rec rem_columns : Name.t -> Name.t -> perm -> perm option = fun n m p ->
  match n, p with
  | Name.Z, Context.Ortho (p, k) ->
     if k = m then
       Option.pure p
     else
       Option.fail
  | Name.N n, Context.Ortho (p, k) ->
     Context.ortho <$> rem_columns n m p <*> Option.pure k
  | Name.V n, Context.Comma (p, k) ->
     Context.comma <$> rem_columns n m p <*> Option.pure k
  | _, Context.Empty -> failwith "Hit empty permutation table!"
  | _ -> failwith "Ill-kinded name/permutation."

let rec rem_cut : Name.t -> Name.t -> t -> t option = fun n m t ->
  match n, t with
  | Name.Z  , Ortho t -> Option.pure t
  | _       , Perm  p -> perm  <$> rem_columns n m p
  | Name.V n, Comma t -> comma <$> rem_cut n m t
  | Name.N n, Ortho t -> ortho <$> rem_cut n m t
  | _ -> failwith "Ill-kinded name/variable."
  
let rem : Name.t -> t -> t option = fun n p ->
  rem_cut n n p >>= rem_entries n
