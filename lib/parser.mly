%{
open Utils
%}

%token <int> NUM
%token <string> VAR
%token TRUE
%token FALSE
%token ASSERT
%token LET
%token REC
%token EQ
%token IN
%token COLON
%token LPAREN
%token RPAREN
%token IF
%token THEN
%token ELSE
%token FUN
%token ARROW

%token ADD
%token SUB
%token MUL
%token DIV
%token MOD
%token LT
%token LTE
%token GT
%token GTE
%token NEQ
%token AND
%token OR

%token INT
%token BOOL
%token UNIT

%token EOF

%right OR
%right AND
%left LT LTE GT GTE EQ NEQ
%left ADD SUB
%left MUL DIV MOD
%right ARROW

%start <Utils.prog> prog

%%

prog:
  | lets=toplet*; EOF { lets }

toplet:
  | LET; is_rec=REC?; name=VAR; args=arg*; COLON; ty=ty; EQ; binding=expr
    {
      let is_rec = Option.is_some is_rec in
      {is_rec;name;args;ty;binding}
    }

arg:
  | LPAREN; x=VAR; COLON; ty=ty; RPAREN { x, ty }

ty:
  | INT { IntTy }
  | BOOL { BoolTy }
  | UNIT { UnitTy }
  | t1=ty; ARROW; t2=ty { FunTy (t1, t2) }
  | LPAREN; ty=ty; RPAREN { ty }

expr:
  | LET; is_rec=REC?; name=VAR; args=arg*; COLON; ty=ty; EQ; binding=expr; IN; body=expr
    {
      let is_rec = Option.is_some is_rec in
      SLet {is_rec;name;args;ty;binding;body}
    }
  | IF; e1=expr; THEN; e2=expr; ELSE; e3=expr { SIf (e1, e2, e3) }
  | FUN; args=arg+; ARROW; body=expr { SFun {args;body} }
  | e = expr2 { e }

%inline bop:
  | ADD { Add }
  | SUB { Sub }
  | MUL { Mul }
  | DIV { Div }
  | MOD { Mod }
  | LT { Lt }
  | LTE { Lte }
  | GT { Gt }
  | GTE { Gte }
  | EQ { Eq }
  | NEQ { Neq }
  | AND { And }
  | OR { Or }

expr2:
  | e1=expr2; op=bop; e2=expr2 { SBop (op, e1, e2) }
  | ASSERT; e=expr3 { SAssert e }
  | es=expr3+ { SApp es }

expr3:
  | LPAREN; RPAREN { SUnit }
  | TRUE { SBool true }
  | FALSE { SBool false }
  | n = NUM { SNum n }
  | x = VAR { SVar x }
  | LPAREN; e = expr; RPAREN { e }