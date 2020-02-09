let open_close_in : (string -> in_channel -> 'a) -> string -> 'a = fun f file_name ->
  let channel = open_in file_name   in
  let result  = f file_name channel in
  let ()      = close_in channel    in
  result

let from_channel : string -> in_channel -> Test.flag * Raw.file = fun file_name channel ->
  let initial = Lexing.{
    pos_fname = file_name
  ; pos_lnum  = 1
  ; pos_bol   = 0
  ; pos_cnum  = 0
  } in
  try
    Parser.MenhirInterpreter.loop_handle
      Function.id
      Parser.MenhirInterpreter.(function
        | HandlingError env ->
            begin match Lazy.force (stack env) with
            | MenhirLib.General.Cons (Parser.MenhirInterpreter.Element (l, _, s, e), _) ->
                failwith (
                  Printf.sprintf "state: %d, line: %d, column: %d-%d\n"
                    (number l)
                    s.Lexing.pos_lnum
                    (s.Lexing.pos_cnum - s.Lexing.pos_bol)
                    (e.Lexing.pos_cnum - e.Lexing.pos_bol)
                )
            | _ -> failwith "Parser is feeling unwell!"
            end
        | _ -> failwith "Parser is feeling unwell!"
      )
      (Lexer.test_supplier file_name channel)
      (Parser.Incremental.test initial)
  with Parser_error.Parse_error (_, s, e) ->
    failwith (
        "Parser: "
        ^ string_of_int s.Lexing.pos_lnum ^ " : "
        ^ string_of_int s.Lexing.pos_bol  ^ "; "
        ^ string_of_int e.Lexing.pos_lnum ^ " : "
        ^ string_of_int e.Lexing.pos_bol
      )

let from_file : string -> Test.flag * Raw.file =
  open_close_in from_channel
