include Name_base

let sv : t -> t = fun t -> V t
let sn : t -> t = fun t -> N t

let rec count : t -> int = function
  | Z   -> 0
  | N t -> count t + 1
  | V t -> count t

let rec wk : Weaken.t -> t -> t = fun w n ->
  match w, n with
  | Weaken.N  _, Z   -> Z
  | Weaken.N  w, N n -> N (wk w n)
  | Weaken.V  w, V n -> V (wk w n)
  | Weaken.Wn w, _   -> N (wk w n)
  | Weaken.Wv w, _   -> V (wk w n)
  | _                -> failwith "Ill-kinded name weakening."

let rec wkn : t -> t -> t = fun n m ->
  match n, m with
  | Z  , _   -> N m
  | N _, Z   -> Z
  | N n, N m -> N (wkn n m)
  | V n, V m -> V (wkn n m)
  | _ -> failwith "Ill-kinded name/name."

let rec wkv : Var_base.t -> t -> t = fun v n ->
  match v, n with
  | Var_base.Z  , _   -> V n
  | Var_base.N _, Z   -> Z
  | Var_base.N v, N n -> N (wkv v n)
  | Var_base.V v, V n -> V (wkv v n)
  | _ -> failwith "Ill-kinded variable/name."


let swp : t -> t -> t -> t = fun n n' m ->
  if n = m then
    n'
  else if n' = m then
    n
  else
    m

open Option.Operators

let rec rem : t -> t -> t option = fun n m ->
  match n, m with
  | Z  , Z   -> Option.fail
  | Z  , N m -> Option.pure m
  | N _, Z   -> Option.pure Z
  | N n, N m -> sn <$> rem n m
  | V n, V m -> sv <$> rem n m
  | _ -> failwith "Encountered kind mismatched names."
