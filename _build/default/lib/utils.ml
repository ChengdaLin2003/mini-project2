type ty =
  | IntTy
  | BoolTy
  | UnitTy
  | FunTy of ty * ty

let string_of_ty =
  let rec go ty =
    match ty with
    | IntTy -> "int"
    | BoolTy -> "bool"
    | UnitTy -> "unit"
    | FunTy (t1, t2) -> go' t1 ^ " -> " ^ go t2
  and go' ty =
    match ty with
    | IntTy -> "int"
    | BoolTy -> "bool"
    | UnitTy -> "unit"
    | FunTy (t1, t2)-> "(" ^ go (FunTy (t1, t2)) ^ ")"
  in go

type bop =
  | Add | Sub | Mul | Div | Mod
  | Lt | Lte | Gt | Gte | Eq | Neq
  | And | Or

let string_of_bop op =
  let go op =
    match op with
    | Add -> "+"
    | Sub -> "-"
    | Mul -> "*"
    | Div -> "/"
    | Mod -> "mod"
    | Lt -> "<"
    | Lte -> "<="
    | Gt -> ">"
    | Gte -> ">="
    | Eq -> "="
    | Neq -> "<>"
    | And -> "&&"
    | Or -> "||"
  in "(" ^ go op ^ ")"

type sfexpr =
  | SUnit
  | SBool of bool
  | SNum of int
  | SVar of string
  | SFun of {
      args : (string * ty) list;
      body : sfexpr;
    }
  | SApp of sfexpr list
  | SLet of {
      is_rec : bool;
      name : string;
      args : (string * ty) list;
      ty : ty;
      binding : sfexpr;
      body : sfexpr;
    }
  | SIf of sfexpr * sfexpr * sfexpr
  | SBop of bop * sfexpr * sfexpr
  | SAssert of sfexpr

type toplet =
  {
    is_rec : bool;
    name : string;
    args : (string * ty) list;
    ty : ty;
    binding : sfexpr;
  }

type prog = toplet list

type expr =
  | Unit
  | Bool of bool
  | Num of int
  | Var of string
  | If of expr * expr * expr
  | Bop of bop * expr * expr
  | Fun of string * ty * expr
  | App of expr * expr
  | Let of {
      is_rec : bool;
      name : string;
      ty : ty;
      binding : expr;
      body : expr;
    }
  | Assert of expr

module Env = Map.Make(String)

type value =
  | VUnit
  | VBool of bool
  | VNum of int
  | VClos of {
      arg: string;
      body: expr;
      env : dyn_env;
      name: string option
    }

and dyn_env = value Env.t

let string_of_value = function
  | VUnit -> "()"
  | VBool true -> "true"
  | VBool false -> "false"
  | VNum n -> string_of_int n
  | VClos _ -> "<fun>"

type error =
  | ParseErr
  | UnknownVar of string
  | IfTyErr of ty * ty
  | IfCondTyErr of ty
  | OpTyErrL of bop * ty * ty
  | OpTyErrR of bop * ty * ty
  | FunArgTyErr of ty * ty
  | FunAppTyErr of ty
  | LetTyErr of ty * ty
  | LetRecErr of string
  | AssertTyErr of ty

let string_of_error = function
  | ParseErr -> "parse error"
  | UnknownVar x -> "Unbound value " ^ x
  | IfTyErr (then_ty, else_ty) ->
     String.concat " "
       [
         "else-case of if-expression has type";
         string_of_ty else_ty;
         "but an expression was expected of type";
         string_of_ty then_ty;
       ]
  | IfCondTyErr ty ->
     String.concat " "
       [
         "condition of if-expression has type";
         string_of_ty ty;
         "but an expression was expected of type bool";
       ]
  | OpTyErrL (op, t1, t2) ->
     String.concat " "
       [
         "left argument of operator";
         string_of_bop op;
         "has type";
         string_of_ty t2;
         "but an expression was expected of type";
         string_of_ty t1;
       ]
  | OpTyErrR (op, t1, t2) ->
     String.concat " "
       [
         "right argument of operator";
         string_of_bop op;
         "has type";
         string_of_ty t2;
         "but an expression was expected of type";
         string_of_ty t1;
       ]
  | FunArgTyErr (t1, t2) ->
     String.concat " "
       [
         "argument of function has type";
         string_of_ty t2;
         "but an expression was expected of type";
         string_of_ty t1;
       ]
  | FunAppTyErr ty ->
     String.concat " "
       [
         "an expression of type";
         string_of_ty ty;
         "is not a function; it cannot be applied";
       ]
  | LetTyErr (expected, actual) ->
     String.concat " "
       [
         "let-defined value has type";
         string_of_ty actual;
         "but an expression was expected of type";
         string_of_ty expected;
       ]
  | LetRecErr name ->
     String.concat " "
       [ "the recursive binding of"
       ; name
       ; "must have an argument"
       ]
  | AssertTyErr ty ->
     String.concat " "
       [
         "argument of assert has type";
         string_of_ty ty;
         "but an expression was expected of type bool";
       ]