open Parser

let newline = [%sedlex.regexp? "\r\n" | '\r' | '\n' ]

let rec token : Sedlexing.lexbuf -> Parser.token = fun buffer ->
  let arrow    = [%sedlex.regexp? 0x2192] in
  let alpha    = [%sedlex.regexp? 0x03B1] in
  let nu       = [%sedlex.regexp? 0x03BD] in
  let lambda   = [%sedlex.regexp? 0x03BB] in
  let number   = [%sedlex.regexp? Plus xml_digit] in
  let comment  = [%sedlex.regexp? "--", Star (Compl ('\r' | '\n')) , newline] in
  let reserved = [%sedlex.regexp? lambda | '|' | '\\' | '.' | ',' | ':' | alpha | '!'  | nu | '?' | '(' | ')' | '['  | ']'  | ';' | '='  | '@'  | '_' | arrow] in
  let id       = [%sedlex.regexp? Plus (Compl (white_space | reserved))] in
  match%sedlex buffer with
  | comment     -> token buffer
  | "{-"        -> comment buffer; token buffer
  | 'N'         -> NAMESORT
  | 'U'         -> UNIVERSE
  | "elim"      -> REC
  | "swap"      -> SWAP
  | "in"        -> IN
  | "let"       -> LET
  | "data"      -> DATA
(*
  | "if"        -> IF
  | "then"      -> THEN
  | "else"      -> ELSE
  | "return"    -> RETURN
*)
  | number      -> INTEGER (int_of_string (Sedlexing.Utf8.lexeme buffer))
  | lambda
  | '\\'        -> BACKSLASH
  | '|'         -> BAR
  | '.'         -> DOT
  | ','         -> COMMA
  | "::"        -> COLON_COLON
  | ':'         -> COLON
  | alpha
  | '!'         -> BANG
  | nu
  | '?'         -> QUESTIONMARK
  | '('         -> LPAREN
  | ')'         -> RPAREN
  | '['         -> LBRACKET
  | ']'         -> RBRACKET
  | ';'         -> SEMICOLON
  | arrow
  | "->"        -> ARROW
  | '='         -> EQUALS
  | '@'         -> AT
  | '_'         -> UNDERSCORE
  | newline     -> token buffer
  | white_space -> token buffer
  | id          -> IDENT (Sedlexing.Utf8.lexeme buffer)
  | eof         -> EOF
  | _           ->
     let (count, offset) = Sedlexing.loc buffer in
     failwith (
         "Unexpected character '" ^ Sedlexing.Utf8.lexeme buffer
         ^ "' in line "           ^ string_of_int count
         ^ ", character "         ^ string_of_int offset ^ "."
     )

and comment : Sedlexing.lexbuf -> unit = fun buffer ->
  match%sedlex buffer with
  | "{-"    -> comment buffer; comment buffer
  | "-}"    -> ()
  | eof     -> failwith "Forgot to terminate comment?"
  | any     -> comment buffer
  | _       -> failwith "Bug in comment lexer."

let rec failure_code : Sedlexing.lexbuf -> Failure_code.t = fun buffer ->
  match%sedlex buffer with
  | "NOT_FRESH_TYPE" -> Failure_code.NOT_FRESH_TYPE
  | "NOT_FRESH_TERM" -> Failure_code.NOT_FRESH_TERM
  | "NOT_EQUIV"      -> Failure_code.NOT_EQUIV
  | "NOT_SUB_TYPE"   -> Failure_code.NOT_SUB_TYPE
  | "NOT_FUN"        -> Failure_code.NOT_FUN
  | "NOT_NAB"        -> Failure_code.NOT_NAB
  | "NOT_UNV"        -> Failure_code.NOT_UNV
  | "NEG_UNV_LEVEL"  -> Failure_code.NEG_UNV_LEVEL
  | "NOT_SUB_UNV"    -> Failure_code.NOT_SUB_UNV
  | "UNBOUND_VAR"    -> Failure_code.UNBOUND_VAR
  | "UNBOUND_NAME"   -> Failure_code.UNBOUND_NAME
  | "UNBOUND_TCN"    -> Failure_code.UNBOUND_TCN
  | newline          -> failure_code buffer
  | white_space      -> failure_code buffer
  | _                -> failwith "Expected a failure code."

let test : Sedlexing.lexbuf -> Parser.token = fun buffer ->
  match%sedlex buffer with
  | "SUCCESS" -> SUCCESS
  | "FAILURE" -> FAILURE (failure_code buffer)
  | _         -> token buffer

let test_supplier : string -> in_channel -> (unit -> Parser.token * Lexing.position * Lexing.position) = fun file_name channel ->
  let buffer = Sedlexing.Utf8.from_channel channel in
  let ()     = Sedlexing.set_filename buffer file_name in
  fun () ->
    let token = test buffer in
    let startp, endp = Sedlexing.lexing_positions buffer in
    token, startp, endp
