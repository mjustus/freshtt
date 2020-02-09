let print d =
  PPrint.ToChannel.pretty 1. 78 stdout d;
  print_newline ()

let to_term : Raw.file -> Term.file = fun t ->
  Error.String.catch_map
    (Term.from_raw_file t Term.Env.init)
    (fun t -> t)
    failwith

exception Debug of Failure.t

let type_check : Term.file -> unit = fun t ->
  Check.E.catch_map
    (Check.check_file t Check.Env.init)
    (fun () -> print_endline "Success!")
    (fun e  -> raise (Debug e))

let validate_test : Test.flag -> Term.file -> unit = fun f t ->
  let success =
    match f with
    | Test.Success   -> fun () -> print_endline "Success!"
    | Test.Failure _ -> fun () -> failwith "Expected failure but type checking was successful."
  in
  let failure =
    match f with
    | Test.Success   -> fun e -> failwith ("Type checking failed: " ^ Failure.to_string e)
    | Test.Failure c -> fun e -> if c = Failure.to_code e then
                                   print_endline "Failure as expected"
                                 else
                                   failwith ("Type checking failed for the wrong reason. Expected " ^ Failure_code.to_string c ^ " but got " ^ Failure.to_string e ^ " instead.")
  in 
  Check.E.catch_map
    (Check.check_file t Check.Env.init)
    success
    failure

module Config = struct
  type print = {
    raw    : bool;
    term   : bool;
    normal : bool
  }

  type config = {
    print  : print;
    check  : bool;
    normal : bool;
  }

  type t = {
    config : config;
    files  : string list
  }

  type print_soup = Raw | Term | Normal
  let to_print : print_soup list -> print = fun xs -> {
    raw    = List.mem Raw    xs;
    term   = List.mem Term   xs;
    normal = List.mem Normal xs
  }

  let to_data print check normal files : t =
    {config = {print; check; normal}; files}
end


module Cmd = struct
  open Cmdliner

  let print =
    let doc = "Pretty-print internal representation of the input program." in
    Arg.(value & opt (list (enum ["raw", Config.Raw; "term", Config.Term; "normal", Config.Normal])) [] & info ["p"; "print"] ~doc)

  let normal =
    let enable =
      let doc = "Fully normalise." in
      true, Arg.info ["n"; "normal"] ~doc
    in
    Arg.(last & vflag_all [false] [enable])

  let check =
    let disable =
      let doc = "Skip type checking." in
      false, Arg.info ["no-check"] ~doc
    in
    Arg.(last & vflag_all [true] [disable])

  let files = Arg.(non_empty & pos_all file [] & info [] ~docv:"FILE")

  let term =
    let doc = "A dependently typed language with name abstraction." in
    Term.(
      pure Config.to_data
      $ (pure Config.to_print $ print)
      $ check
      $ normal
      $ files
    ),
    Term.info "freshtt" ~version:"0.1" ~doc
end

let (%>) : 'a 'b 'c. ('a -> 'b) -> ('b -> 'c) -> 'a -> 'c = fun f g x ->
  g (f x)

let pass_through : 'a. ('a -> unit) -> 'a -> 'a = fun f a ->
  f a; a

open Config

let () : unit =
  let guard : 'a. bool -> ('a -> unit) -> 'a -> 'a = function
    | true  -> pass_through
    | false -> fun _ a -> a in
  let pipeline : Config.config -> string -> unit = fun c file ->
    Read.from_file file
    |> Product.map2 Prelude.Raw.prepend_bool
    |> guard c.print.raw  (snd %> Raw.Print.print_file  %> print)
    |> Product.map2 to_term
    |> guard c.print.term (snd %> Term.Print.print_file %> print)
    |> guard c.check (Product.fold validate_test)
    |> guard c.normal (fun (_, t) ->
         let r = Readback.rb_file (Eval.eval_file t Context.Empty Delta.Done) Delta.Done in
         if c.print.normal then
           print (Normal.Print.print_file r)
       )
    |> fun _ -> ()
  in
  let iter : Config.t -> unit = fun t ->
    List.iter (pipeline t.config) t.files in
  let open Cmdliner in
  match Term.eval Cmd.term with
  | `Ok t ->
      let () = iter t in
      exit 0
  | _     ->
      exit 1
