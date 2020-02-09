include Var_base

let sv : t -> t = fun t -> V t
let sn : t -> t = fun t -> N t

let rec count : t -> int = function
  | Z   -> 0
  | V t -> count t + 1
  | N t -> count t

(*
let rec make_wk : Context.t -> t -> Weaken.t = fun c v ->
  match c, v with
  | Context.Times c, Z   -> Weaken.Wv (Weaken.id c)
  | Context.Times c, V v -> Weaken.Wv (make_wk c v)
  | Context.Star  c, N v -> Weaken.Wn (make_wk c v)
  | Context.Empty  , _   -> failwith "Context impossibly small."
  | _                    -> failwith "Context or variable ill-kinded."
 *)

let rec wk : Weaken.t -> t -> t = fun w v ->
  match w, v with
  | Weaken.V  _, Z   -> Z
  | Weaken.V  w, V v -> V (wk w v)
  | Weaken.N  w, N v -> N (wk w v)
  | Weaken.Wv w, _   -> V (wk w v)
  | Weaken.Wn w, _   -> N (wk w v)
  | _                -> failwith "Ill-kinded variable weakening."

let rec wkn : Name_base.t -> t -> t = fun n v ->
  match n, v with
  | Name_base.Z  , _   -> N v
  | Name_base.N n, N v -> N (wkn n v)
  | Name_base.V _, Z   -> Z
  | Name_base.V n, V v -> V (wkn n v)
  | _ -> failwith "Ill-kinded name/variable."

let rec wkv : t -> t -> t = fun v w ->
  match v, w with
  | Z  , _   -> V w
  | V _, Z   -> Z
  | V v, V w -> V (wkv v w)
  | N v, N w -> N (wkv v w)
  | _ -> failwith "Ill-kinded variable/name."
                  
let rec rem : Name_base.t -> t -> t = fun n v ->
  match n, v with
  | Name_base.Z  , N v -> v
  | Name_base.V _, Z   -> Z
  | Name_base.N n, N v -> N (rem n v)
  | Name_base.V n, V v -> V (rem n v)
  | Name_base.Z  , Z
  | Name_base.Z  , V _
  | Name_base.V _, N _
  | Name_base.N _, Z
  | Name_base.N _, V _ -> failwith "Encountered kind mismatched name/variable."
