type 'a name = N of Binder.t_opt * 'a
let name_bind : Binder.t_opt -> 'a -> 'a name = fun n a -> N (n, a)
let name_unbind : 'a name -> Binder.t_opt * 'a = function N (n, a) -> (n, a)
let name_body : 'a name -> 'a = function N (_, a) -> a

type 'a var  = V of Binder.t_opt * 'a
let var_bind : Binder.t_opt -> 'a -> 'a var = fun v a -> V (v, a)
let var_unbind : 'a var -> Binder.t_opt * 'a = function V (v, a) -> (v, a)
let var_body : 'a var -> 'a = function V (_, a) -> a
