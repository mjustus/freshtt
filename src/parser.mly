%{
open Raw
%}

%token UNIVERSE NAMESORT
%token BACKSLASH
%token BANG
%token QUESTIONMARK
%token DOT
%token LPAREN
%token RPAREN
%token LBRACKET
%token RBRACKET
%token SEMICOLON
%token COLON
%token COLON_COLON
%token COMMA
%token EQUALS
%token ARROW
%token AT
%token SWAP
%token IN
%token UNDERSCORE
%token LET
%token REC

%token SUCCESS
%token <Failure_code.t> FAILURE

/* %token IF THEN ELSE RETURN */
%token DATA BAR

%token EOF
%token <string> IDENT
%token <int> INTEGER


%start file
%type <Raw.file> file

%start test
%type <Test.flag * Raw.file> test
%%

let compose(f, g) == ~=f; ~=g; {fun x -> f (g x)}

let nlist_compose (f) :=
  | ~=compose(f, nlist_compose(f)); <>
  | ~=f; <>

let list_compose (f) :=
  | ~ = compose(f, nlist_compose(f)); <>
  | {Function.id}

let nlist (X) :=
  | ~=X; ~=nlist(X); <N_list.More>
  | ~=X; <N_list.Last>

let nlist_sep (s, X) :=
  | ~=X; s; ~=nlist_sep(s, X); <N_list.More>
  | ~=X; <N_list.Last>
                               
file :
    decls EOF { $1 }

test :
    test_flag file { ($1, $2) }
  | file { (Test.Success, $1) }

test_flag :
    SUCCESS { Test.Success }
  | FAILURE { Test.Failure $1 }

term_annot :
    term_annot COLON_COLON term_let { Chk ($3, $1) }
  | term_let { $1 }

constr_list :
  | BAR IDENT COLON dc_type constr_list { ($2 , $4) :: $5 }
  |  { [] }
      
decl :
    ident_opt COLON term_annot EQUALS term_annot { fun f -> Defn ($3, $5, Named.Opt.Bound ($1, f)) }
  | DATA IDENT COLON tc_type constr_list
      {fun f ->
         let name = $2 in
         let (Hidden vs) = Vec.from_list $5 in
         let xs, cs = Vec.unzip vs in
         let cs =
           Vec.map (fun (n, c) ->
               if n = name then
                 c
               else
                 failwith ("Data constructor of type `" ^ name ^ "` but ends in `" ^ n ^ "`.")
             ) cs
         in
         Data ($4, (Named.Bound (name, Named.Vec.Bound (cs, (xs, f)))))
      }

decls :
  | decl SEMICOLON decls { $1 $3 }
  | decl { $1 Done }
  | { Done }

term_let :
    LET ident_list COLON term_let EQUALS term_let IN term_let
      { Let ($4, $6, Named.Mult_opt.Bound ($2, $8)) }
  | SWAP IDENT IDENT IN term_let { Swp ($2, $3, $5) }
/*
  | IF IDENT EQUALS term_let RETURN term_let THEN term_let ELSE term_let
      { Cmp ($2, $4) }
*/
  | term_cmp { $1 }

term_cmp :
    EQUALS IDENT term_pi
      { Cmp ($2, $3) }
  | term_pi
      { $1 }

term_pi :
    telescope ARROW term_let
      { Abs ($1 (Up $3)) }
  | term_na ARROW term_let
      { Abs (Pi ($1, Named.Mult_opt.Bound (N_list.Last None, Up $3))) }
  | term_lam { $1 }

telescope_segment :
    LPAREN ident_comma_list COLON term_pi RPAREN
      { mk_pi $4 $2 }
  | LBRACKET ident_comma_list COLON term_pi RBRACKET
      { mk_na $4 $2 }

let telescope == nlist_compose(telescope_segment)

dc_telescope_segment :
    LPAREN ident_comma_list COLON term_pi RPAREN
      { mk_pi $4 $2 }
  | LBRACKET ident_comma_list COLON term_pi RBRACKET
      { mk_na $4 $2 }

let dc_telescope == nlist_compose (dc_telescope_segment)

dc_type :
  | dc_telescope ARROW dc_type { fst $3, $1 (snd $3) }
  | tc_applied { fst $1, Up (snd $1 Spine.Empty) }

tc_args :
  | tc_args    term_atom { fun t -> $1 (Spine.comma t $2) }
  | tc_args AT IDENT { fun t -> $1 (Spine.ortho t $3) }
  | {fun t -> t}
      
tc_applied :
  | IDENT tc_args { $1, $2 }

tc_type :
  | telescope ARROW tc_type { $1 $3 }
  | term_atom { Up $1 }

term_lam :
    BACKSLASH ident_list DOT term_let { Lam (Named.Mult_opt.Bound ($2, $4)) }
  | BANG ident_list DOT term_let { Alp (Named.Mult_opt.Bound ($2, $4)) }
  | QUESTIONMARK ident_list COLON term_annot DOT term_let { Nu ($4, Named.Mult_opt.Bound ($2, $6)) }
  | term_na { $1 }

term_na :
    LBRACKET term_annot RBRACKET term_na
      { Abs (Na ($2, Named.Mult_opt.Bound (N_list.Last None, Up $4))) }
  | term_spine { $1 }

term_spine :
    term_spine term_atom { App ($1, $2) }
  | term_spine AT IDENT { Cnc ($1, $3) }
  | term_atom { $1 }

term_atom :
    UNIVERSE INTEGER { Unv ($2) } 
  | NAMESORT { Nst }
  | IDENT { Idt $1 }
  | REC IDENT INTEGER { Rec ($2, $3) }
  | LPAREN term_annot RPAREN { $2 }

let ident_opt :=
  | UNDERSCORE; {None}
  | ~ = IDENT; <Some>

let ident_list == nlist(ident_opt)
let ident_comma_list == nlist_sep(COMMA, ident_opt)
