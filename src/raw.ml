open Function

type 'a binder = 'a Named.Mult_opt.t

type ('a, 'b) telescope =
  | Pi of 'a * (('a, 'b) telescope) binder
  (* name abstraction *)
  | Na of 'a * (('a, 'b) telescope) binder
  | Up of 'b
type t =
  (* telescope of type/name abstractions *)
  | Abs of (t, t) telescope
  | Unv of int
  | Nst
  | Lam of t binder
  | Alp of t binder
  | App of t * t
  | Cnc of t * string
  | Swp of string * string * t
  | Nu  of t * t binder
  | Cmp of string * t
  (* name, variable, file-wide definition, or type/data constructor *)
  | Idt of string
  | Rec of string * int
  (* let binding *)
  | Let of t * t * t binder
  (* type annotation: first argument is the type, second the term *)
  | Chk of t * t

type constr = (t, (t, string) Spine.t) telescope
                                      
type file =
  | Defn of t * t * file Named.Opt.t
  | Data : (t, t) telescope * ((_, constr, file) Named.Vec.t) Named.t -> file
  | Done

let mk_let : t -> t -> t binder -> t = fun t t' t'' -> Let (t, t', t'')
let mk_unv : int -> t = fun l -> Unv l
let mk_pi : 'a -> Binder.t_nlist_opt -> ('a, 'b) telescope -> ('a, 'b) telescope = fun t xs t' -> Pi (t, Named.Mult_opt.Bound (xs, t'))
let mk_na : 'a -> Binder.t_nlist_opt -> ('a, 'b) telescope -> ('a, 'b) telescope = fun t xs t' -> Na (t, Named.Mult_opt.Bound (xs, t'))
let mk_up : 'b -> ('a, 'b) telescope = fun t -> Up t
let mk_abs : ('a, 'b) telescope -> t = fun t -> Abs t
let mk_lam : t binder -> t = fun t -> Lam t
let mk_alp : t binder -> t = fun t -> Alp t
let mk_app : t -> t -> t = fun t t' -> App (t, t')
let mk_cnc : t -> string -> t = fun t n -> Cnc (t, n)
let mk_swp : string -> string -> t -> t = fun n n' t -> Swp (n, n', t)
let mk_nu  : t -> t binder -> t = fun t t' -> Nu (t, t')
let mk_cmp : string -> t -> t = fun n t -> Cmp (n, t)
let mk_idt : string -> t = fun x -> Idt x
let mk_chk : t -> t -> t = fun t t' -> Chk (t, t')

let mk_defn : t -> t -> file Named.Opt.t -> file = fun t1 t1' t -> Defn (t1, t1', t)
let mk_data : (t, t) telescope -> (_, constr, file) Named.Vec.t Named.t -> file = fun t cs -> Data (t, cs)

let rec compress : t -> t = fun t ->
  match t with
  | Abs t -> Abs (compress_abs t)
  | Unv _ | Nst | Idt _ | Rec _ -> t
  | Lam t -> Lam (compress_lam t)
  | Alp t -> Alp (compress_alp t)
  | App (t, t') -> App (compress t, compress t')
  | Cnc (t, n) -> Cnc (compress t, n)
  | Swp (n, n', t) -> Swp (n, n', compress t)
  | Nu (t, t') -> Nu (compress t, compress_binder t')
  | Cmp (n, t) -> Cmp (n, compress t)
  | Let (t1, t1', Named.Mult_opt.Bound (xs, t2)) -> Let (compress t1, compress t1', Named.Mult_opt.Bound (xs, compress t2))
  | Chk (t, t') -> Chk (compress t, compress t')
and compress_lam : t binder  -> t binder = function
  | Named.Mult_opt.Bound (xs, Lam t) ->
      begin match compress_lam t with
      | Named.Mult_opt.Bound (ys, t) ->
          Named.Mult_opt.Bound (N_list.concat xs ys, t)
      end
  | t -> compress_binder t
and compress_alp : t binder  -> t binder = function
  | Named.Mult_opt.Bound (xs, Alp t) ->
      begin match compress_alp t with
      | Named.Mult_opt.Bound (ys, t) ->
          Named.Mult_opt.Bound (N_list.concat xs ys, t)
      end
  | t -> compress_binder t
and compress_binder : t binder -> t binder = function
  | Named.Mult_opt.Bound (xs, t) ->
      Named.Mult_opt.Bound (xs, compress t)
and compress_abs : (t, t) telescope -> (t, t) telescope = function
  | Pi (t, t') -> Pi (compress t, compress_abs_binder t')
  | Na (t, t') -> Na (compress t, compress_abs_binder t')
  | Up (Abs t) -> compress_abs t
  | Up t       -> Up (compress t)
and compress_abs_binder : (t, t) telescope binder -> (t, t) telescope binder = function
  | Named.Mult_opt.Bound (xs, t) ->
      Named.Mult_opt.Bound (xs, compress_abs t)

let rec compress_file : file -> file = function
  | Defn (t1, t2, Named.Opt.Bound (v, t')) ->
      Defn (compress t1, compress t2, Named.Opt.Bound (v, compress_file t'))
  | Data (t, Named.Bound (x, Named.Vec.Bound (cs, (xs, t')))) ->
      Data (compress_abs t, Named.Bound (x, Named.Vec.Bound (Vec.map id cs, (xs, compress_file t'))))
  | Done  -> Done
  
module Print = struct
  let (^^) = PPrint.(^^)
  let (^/^) = PPrint.(^/^)
  let (^//^) = PPrint.(^//^)
  let (!^) = PPrint.(!^)

  let infix_colon_paren x y =
    ((PPrint.lparen ^^ x) ^//^ (PPrint.colon ^^ PPrint.space ^^ y)) ^^ PPrint.rparen

  let infix_colon_bracket x y =
    ((PPrint.lbracket ^^ x) ^//^ (PPrint.colon ^^ PPrint.space ^^ y)) ^^ PPrint.rbracket

  type context =
    | None
    | AppLeft | AppRight
    | ChkLeft | ChkRight
    | AtLeft
    | Swp
    | SPiLeft | SPiRight
    | SNaLeft | SNaRight
    | CmpTest
    | Other

  let rec need_parens : context -> t -> bool = fun c t ->
    match t with
    | Chk _ ->
        begin match c with
        | None -> false
        | _ -> true
        end
    | Idt _ -> false
    | Unv   _ ->
        begin match c with
        | AppRight -> true
        |  _ -> false
        end
    | Abs (Pi _) ->
        begin match c with
        | AppLeft | AppRight | AtLeft | SPiLeft | SNaRight -> true
        | _ -> false
        end
    | Abs (Na _) ->
        begin match c with
        | AppLeft | AppRight -> true
        | _ -> false
        end
    | Abs (Up t) ->
        need_parens c t
    | App _ ->
        begin match c with
        | AppRight -> true
        |  _ -> false
        end
    | Rec _ ->
        begin match c with
        | AppRight -> true
        |  _ -> false
        end
    | Lam   _ ->
        begin match c with
        | AppLeft | AppRight -> true
        | _ -> false
        end
    | Nst -> false
    | Swp _ ->
        begin match c with
        | Swp | AppLeft | AppRight -> true
        | _ ->false
        end
    | Alp _ ->
        begin match c with
        | AppLeft | AppRight | AtLeft -> true
        | _ -> false
        end
    | Nu _ ->
        begin match c with
        | AppLeft | AppRight | AtLeft | CmpTest -> true
        | _ -> false
        end
    | Cnc _ ->
        begin match c with
        | AppLeft | AppRight -> true
        | _ -> false
        end
    | Let _ ->
       begin match c with
       | AppLeft | AppRight | ChkLeft | AtLeft | SPiLeft | CmpTest -> true
       | _ -> false
       end
    | Cmp _ ->
       begin match c with
       | AppLeft | AppRight | AtLeft | SPiLeft -> true
       | _ -> false
       end       

  let arrow : PPrint.document = !^ "→"

  let print_idt = function Some x -> !^ x | None -> PPrint.underscore

  let print_bound : Binder.t_nlist_opt -> PPrint.document = fun b ->
    PPrint.group (N_list.fold_map print_idt (^/^) b)

  let print_bound_comma : Binder.t_nlist_opt -> PPrint.document =
    N_list.fold_map print_idt (fun d d' -> d ^/^ PPrint.comma ^//^ d')

  let rec print : t -> PPrint.document = fun t ->
    match t with
    | Unv i ->
        !^ "U" ^^ PPrint.space ^^ !^ (string_of_int i)
    | Nst  -> !^ "N"
    | Rec (x, i) -> !^ "elim" ^//^ !^ x  ^//^ !^ (string_of_int i)
    | Abs (Pi (t, Named.Mult_opt.Bound (N_list.Last None, Up t'))) ->
        PPrint.group (print_ctx SPiLeft t ^//^ arrow)
        ^//^ print_ctx SPiRight t'
    | Abs (Na (t, Named.Mult_opt.Bound (N_list.Last None, Up t'))) ->
        PPrint.brackets (print_ctx SNaLeft t)
        ^^ print_ctx SNaRight t'
    | Abs t -> print_telescope (print_ctx Other) t PPrint.group
    | Lam (Named.Mult_opt.Bound (xs, t')) ->
        PPrint.group (
          !^ "λ"
          ^^  print_bound xs
          ^^  PPrint.dot
        )
        ^//^ print_ctx Other t'
    | Alp (Named.Mult_opt.Bound (xs, t')) ->
        ( !^ "α"
          ^^  print_bound xs
          ^^  PPrint.dot
        )
        ^//^ print_ctx Other t'
    | App (t, t') -> (print_ctx AppLeft t) ^//^ (print_ctx AppRight t')
    | Cnc (t, n ) -> PPrint.infix 2 1 PPrint.at (print_ctx AtLeft t) (!^ n)
    | Idt s -> !^ s
    | Swp (n,m,t) ->
        !^ "swap" ^/^ !^ n ^/^ !^ m ^/^ !^ "in" ^/^ print_ctx Swp t
    | Nu (t, Named.Mult_opt.Bound (xs, t')) ->
        ( !^ "ν"
          ^^  print_bound xs
          ^^  PPrint.space
          ^^  PPrint.colon
          ^/^  print_ctx Other t
          ^^  PPrint.dot
        )
        ^//^ print_ctx Other t'
    | Cmp (n, t) ->
       PPrint.group (!^ n ^//^ PPrint.equals ^//^ print_ctx CmpTest t)
    | Let (t1, t1', Named.Mult_opt.Bound (xs, t2)) ->
       (PPrint.group (
           !^ "let" ^//^ print_bound xs
           ^//^ PPrint.colon ^//^ print_ctx Other t1
           ^//^ PPrint.equals
         )
         ^//^ print_ctx Other t1'
         ^//^ !^ "in"
       )
       ^/^ print_ctx Other t2
    | Chk (t,t') ->
        let infix_wrap x y = x ^//^ ((!^ "::") ^^ PPrint.space ^^ y) in
        infix_wrap (print_ctx ChkLeft t') (print_ctx ChkRight t)

  and print_ctx : context -> t -> PPrint.document = fun c t ->
    if need_parens c t then
      PPrint.parens (print t)
    else
      print t
  and print_telescope : 'a. ('a -> PPrint.document) -> (t, 'a) telescope -> (PPrint.document -> PPrint.document) -> PPrint.document = fun f t acc ->
    match t with
    | Pi (t, Named.Mult_opt.Bound (xs, Up t')) ->
        PPrint.group (acc (infix_colon_paren (print_bound_comma xs) (print_ctx Other t) ^//^ arrow))
        ^//^ f t'
    | Pi (t, Named.Mult_opt.Bound (xs, t')) ->
        print_telescope f t' (fun d -> acc (infix_colon_paren (print_bound_comma xs) (print_ctx Other t) ^/^ d))
    | Na (t, Named.Mult_opt.Bound (xs, Up t')) ->
        PPrint.group (acc (infix_colon_bracket (print_bound_comma xs) (print_ctx Other t) ^//^ arrow))
        ^//^ f t'
    | Na (t, Named.Mult_opt.Bound (xs, t')) ->
        print_telescope f t' (fun d -> acc (infix_colon_bracket (print_bound_comma xs) (print_ctx Other t)) ^/^ d)
    | Up t -> f t

  let print_decl : Binder.t_opt -> t -> t -> PPrint.document = fun x t t' ->
    PPrint.group ((print_idt x ^//^ PPrint.colon) ^//^ print t)
    ^//^ PPrint.equals ^//^ print t'

  let print_spine : Binder.t -> (t, string) Spine.t -> PPrint.document = fun x s ->
    print_ctx Other @@ Spine.fold (fun t -> t) (fun f t t' -> f (mk_app t' t)) (fun f n t' -> f (mk_cnc t' n)) s (Idt x)
  
  let print_constr : Binder.t -> Binder.t -> constr -> PPrint.document = fun x y t ->
    PPrint.hardline ^^ PPrint.bar ^//^ !^ y ^//^ PPrint.colon ^//^ print_telescope (print_spine x) t PPrint.group

  let print_data : 'n. Binder.t -> (t, t) telescope -> ('n, Binder.t) Vec.t -> ('n, constr) Vec.t -> PPrint.document = fun x t xs cs ->
    PPrint.group (
      !^ "data"
      ^//^ !^ x
      ^//^ PPrint.colon
      ^//^ print_telescope (print_ctx Other) t PPrint.group
    )
    ^^ PPrint.nest 2 (
         PPrint.group (
           Vec.fold2 PPrint.empty (fun y c t -> print_constr x y c ^^ t) xs cs
         )
       )

  let rec print_file : file -> PPrint.document = fun t ->
    match t with
    | Defn (t, t', Named.Opt.Bound (x, Done)) ->
        print_decl x t t'
    | Defn (t, t', Named.Opt.Bound (x, f)) ->
        print_decl x t t' ^/^ PPrint.semi
        ^/^ print_file f
    | Data (t, Named.Bound (x, Named.Vec.Bound (cs, (xs, Done)))) ->
       print_data x t xs cs
    | Data (t, Named.Bound (x, Named.Vec.Bound (cs, (xs, f)))) ->
       print_data x t xs cs ^/^ PPrint.semi
        ^/^ print_file f
    | Done -> PPrint.empty
end
