open Utils
module Env = Utils.Env

exception DivByZero = Division_by_zero
exception AssertFail

(******************************************************************
 * 重新导出 ty / error / sfexpr / toplet / prog / expr / value 类型，
 * 让构造器在 Interp2 中也可见
 ******************************************************************)

type ty = Utils.ty =
  | IntTy
  | BoolTy
  | UnitTy
  | FunTy of ty * ty

type error = Utils.error =
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

type bop = Utils.bop =
  | Add | Sub | Mul | Div | Mod
  | Lt | Lte | Gt | Gte | Eq | Neq
  | And | Or

type sfexpr = Utils.sfexpr =
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

type toplet = Utils.toplet =
  {
    is_rec : bool;
    name : string;
    args : (string * ty) list;
    ty : ty;
    binding : sfexpr;
  }

type prog = Utils.prog

type expr = Utils.expr =
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

(* 重新导出 value / dyn_env，使 grader 可以写 expr -> value *)
type value = Utils.value =
  | VUnit
  | VBool of bool
  | VNum of int
  | VClos of {
      arg  : string;
      body : expr;
      env  : dyn_env;
      name : string option;
    }

and dyn_env = value Env.t

(******************************************************************
 * parse : string -> prog option
 ******************************************************************)

let parse (s : string) : prog option =
  (* 成功解析 -> Some prog；任何异常 -> None *)
  try
    let lexbuf = Lexing.from_string s in
    let p = Parser.prog Lexer.read lexbuf in
    Some p
  with _ ->
    None

(******************************************************************
 * 把 Utils 里的打印函数转发出来给 main/test 用
 ******************************************************************)

let string_of_value (v : value) : string =
  Utils.string_of_value v

let string_of_error (e : error) : string =
  Utils.string_of_error e

(******************************************************************
 * Helper: 构造函数类型 t1 -> t2 -> ... -> tk -> ret_ty
 ******************************************************************)

let rec fun_ty_of_args (args : (string * ty) list) (ret_ty : ty) : ty =
  match args with
  | [] -> ret_ty
  | (_, t) :: tl ->
      FunTy (t, fun_ty_of_args tl ret_ty)

(******************************************************************
 * Helper: 柯里化多参数函数体
 *   (x1:t1) ... (xk:tk) 和 已经 desugar 的 body_e
 *   => Fun(x1,t1, Fun(x2,t2, ... body_e))
 ******************************************************************)

let rec curry_fun (args : (string * ty) list) (body_e : expr) : expr =
  match args with
  | [] -> body_e
  | (x, ty) :: tl ->
      Fun (x, ty, curry_fun tl body_e)

(******************************************************************
 * Helper: 把 f a1 a2 a3 ... 左结合成 ((f a1) a2) a3 ...
 ******************************************************************)

let rec chain_app (f : expr) (args : expr list) : expr =
  match args with
  | [] -> f
  | a :: tl -> chain_app (App (f, a)) tl

(******************************************************************
 * desugar_sf : sfexpr -> expr
 ******************************************************************)

let rec desugar_sf (e : sfexpr) : expr =
  match e with
  | SUnit        -> Unit
  | SBool b      -> Bool b
  | SNum n       -> Num n
  | SVar x       -> Var x

  | SFun { args; body } ->
      let body_e = desugar_sf body in
      curry_fun args body_e

  | SApp lst ->
      (match lst with
       | [] -> failwith "desugar_sf: empty SApp"
       | f :: args ->
           let f_e = desugar_sf f in
           let args_e = List.map desugar_sf args in
           chain_app f_e args_e)

  | SIf (c, t, f) ->
      let c_e = desugar_sf c in
      let t_e = desugar_sf t in
      let f_e = desugar_sf f in
      If (c_e, t_e, f_e)

  | SBop (op, e1, e2) ->
      let e1' = desugar_sf e1 in
      let e2' = desugar_sf e2 in
      Bop (op, e1', e2')

  | SAssert e1 ->
      let e1' = desugar_sf e1 in
      Assert e1'

  | SLet { is_rec; name; args; ty; binding; body } ->
      let binding_e = curry_fun args (desugar_sf binding) in
      let fun_ty = fun_ty_of_args args ty in
      let body_e = desugar_sf body in
      Let { is_rec; name; ty = fun_ty; binding = binding_e; body = body_e }

(******************************************************************
 * desugar_toplet : toplet 和 continuation k -> expr
 ******************************************************************)

let desugar_toplet (t : toplet) (k : expr) : expr =
  let { is_rec; name; args; ty; binding } = t in
  let binding_e = curry_fun args (desugar_sf binding) in
  let fun_ty = fun_ty_of_args args ty in
  Let { is_rec; name; ty = fun_ty; binding = binding_e; body = k }

(******************************************************************
 * 真正的 desugar : prog -> expr
 ******************************************************************)

let desugar (p : prog) : expr =
  match p with
  | [] -> Unit
  | _  ->
      let last_name = (List.hd (List.rev p)).name in
      let ret = Var last_name in
      List.fold_right desugar_toplet p ret

(******************************************************************
 * 类型检查：expr -> (ty, error) result
 ******************************************************************)

type ty_env = ty Env.t

let empty_env : ty_env = Env.empty

let lookup (env : ty_env) (x : string) : (ty, error) result =
  match Env.find_opt x env with
  | Some t -> Ok t
  | None -> Error (UnknownVar x)

let rec type_of_with (env : ty_env) (e : expr) : (ty, error) result =
  match e with
  | Unit -> Ok UnitTy
  | Bool _ -> Ok BoolTy
  | Num _ -> Ok IntTy
  | Var x -> lookup env x

  | If (c, t, f) ->
      begin
        match type_of_with env c with
        | Error e -> Error e
        | Ok tc ->
            if tc <> BoolTy then Error (IfCondTyErr tc)
            else
              match type_of_with env t, type_of_with env f with
              | Error e, _ | _, Error e -> Error e
              | Ok tt, Ok tf ->
                  if tt = tf then Ok tt
                  else Error (IfTyErr (tt, tf))
      end

  | Bop (op, e1, e2) ->
      begin
        match type_of_with env e1 with
        | Error e -> Error e
        | Ok t1 ->
            match type_of_with env e2 with
            | Error e -> Error e
            | Ok t2 ->
                begin match op with
                | Add | Sub | Mul | Div | Mod ->
                    if t1 <> IntTy then Error (OpTyErrL (op, IntTy, t1))
                    else if t2 <> IntTy then Error (OpTyErrR (op, IntTy, t2))
                    else Ok IntTy
                | Lt | Lte | Gt | Gte ->
                    if t1 <> IntTy then Error (OpTyErrL (op, IntTy, t1))
                    else if t2 <> IntTy then Error (OpTyErrR (op, IntTy, t2))
                    else Ok BoolTy
                | And | Or ->
                    if t1 <> BoolTy then Error (OpTyErrL (op, BoolTy, t1))
                    else if t2 <> BoolTy then Error (OpTyErrR (op, BoolTy, t2))
                    else Ok BoolTy
                | Eq | Neq ->
                    if t1 <> t2 then Error (OpTyErrR (op, t1, t2))
                    else Ok BoolTy
                end
      end

  | Fun (x, arg_ty, body) ->
      let env' = Env.add x arg_ty env in
      begin
        match type_of_with env' body with
        | Ok body_ty -> Ok (FunTy (arg_ty, body_ty))
        | Error e -> Error e
      end

  | App (e1, e2) ->
      begin
        match type_of_with env e1 with
        | Error e -> Error e
        | Ok tfun ->
            begin match tfun with
            | FunTy (arg_ty, res_ty) ->
                begin
                  match type_of_with env e2 with
                  | Error e -> Error e
                  | Ok targ ->
                      if targ = arg_ty then Ok res_ty
                      else Error (FunArgTyErr (arg_ty, targ))
                end
            | _ -> Error (FunAppTyErr tfun)
            end
      end

  | Let { is_rec; name; ty = annot_ty; binding; body } ->
      if not is_rec then
        begin
          match type_of_with env binding with
          | Error e -> Error e
          | Ok t_binding ->
              if t_binding <> annot_ty
              then Error (LetTyErr (annot_ty, t_binding))
              else
                let env' = Env.add name annot_ty env in
                type_of_with env' body
        end
      else
        begin
          match binding with
          | Fun (_, _, _) ->
              let env_for_binding = Env.add name annot_ty env in
              begin
                match type_of_with env_for_binding binding with
                | Error e -> Error e
                | Ok t_binding ->
                    if t_binding <> annot_ty
                    then Error (LetTyErr (annot_ty, t_binding))
                    else
                      let env' = Env.add name annot_ty env in
                      type_of_with env' body
              end
          | _ -> Error (LetRecErr name)
        end

  | Assert e1 ->
      begin
        match type_of_with env e1 with
        | Error e -> Error e
        | Ok t ->
            if t <> BoolTy then Error (AssertTyErr t)
            else Ok UnitTy
      end

let type_of (e : expr) : (ty, error) result =
  type_of_with empty_env e

(* -------------------- Evaluation -------------------- *)

(* Extract an int from a value. Well-typed programs guarantee
   that these helpers are only called on the right kind of value. *)
let int_of_value (v : value) : int =
  match v with
  | VNum n -> n
  | _ -> failwith "internal error: expected int"

let bool_of_value (v : value) : bool =
  match v with
  | VBool b -> b
  | _ -> failwith "internal error: expected bool"

(* Big-step evaluator with an explicit dynamic environment. *)
let rec eval_with (env : dyn_env) (e : expr) : value =
  match e with
  | Unit -> VUnit
  | Bool b -> VBool b
  | Num n -> VNum n
  | Var x ->
      (* In well-typed programs every variable must be bound. *)
      (try Env.find x env with Not_found ->
         failwith ("internal error: unbound variable " ^ x))

  | If (c, t, f) ->
      let vc = eval_with env c in
      if bool_of_value vc
      then eval_with env t
      else eval_with env f

  | Fun (x, _arg_ty, body) ->
      VClos { arg = x; body; env; name = None }

  | App (e1, e2) ->
      let vf = eval_with env e1 in
      let va = eval_with env e2 in
      (match vf with
       | VClos clos ->
           let env' = Env.add clos.arg va clos.env in
           eval_with env' clos.body
       | _ ->
           failwith "internal error: attempting to apply non-function")

  | Let { is_rec = _; name; ty = _annot_ty; binding; body } ->
      (* At runtime, we treat let and let rec the same: evaluate the binding
         once, then extend the environment. The type checker has already
         enforced the additional constraints for let rec. *)
      let v_binding = eval_with env binding in
      let env' = Env.add name v_binding env in
      eval_with env' body

  | Assert e1 ->
      let v = eval_with env e1 in
      if bool_of_value v
      then VUnit
      else raise AssertFail

  | Bop (op, e1, e2) ->
      match op with
      (* Short-circuit boolean operators. *)
      | And ->
          let v1 = eval_with env e1 in
          (match v1 with
           | VBool false -> VBool false
           | VBool true ->
               let v2 = eval_with env e2 in
               VBool (bool_of_value v2)
           | _ -> failwith "internal error: expected bool for &&")
      | Or  ->
          let v1 = eval_with env e1 in
          (match v1 with
           | VBool true -> VBool true
           | VBool false ->
               let v2 = eval_with env e2 in
               VBool (bool_of_value v2)
           | _ -> failwith "internal error: expected bool for ||")

      (* Arithmetic on integers. *)
      | Add | Sub | Mul | Div | Mod ->
          let v1 = eval_with env e1 in
          let v2 = eval_with env e2 in
          let n1 = int_of_value v1 in
          let n2 = int_of_value v2 in
          (match op with
           | Add -> VNum (n1 + n2)
           | Sub -> VNum (n1 - n2)
           | Mul -> VNum (n1 * n2)
           | Div ->
               if n2 = 0 then raise DivByZero else VNum (n1 / n2)
           | Mod ->
               if n2 = 0 then raise DivByZero else VNum (n1 mod n2)
           | _ -> assert false)

      (* Numeric comparisons. *)
      | Lt | Lte | Gt | Gte ->
          let v1 = eval_with env e1 in
          let v2 = eval_with env e2 in
          let n1 = int_of_value v1 in
          let n2 = int_of_value v2 in
          let b =
            match op with
            | Lt  -> n1 <  n2
            | Lte -> n1 <= n2
            | Gt  -> n1 >  n2
            | Gte -> n1 >= n2
            | _ -> assert false
          in
          VBool b

      (* Equality / inequality: defined on base values (unit, bool, int). *)
      | Eq | Neq ->
          let v1 = eval_with env e1 in
          let v2 = eval_with env e2 in
          let equal =
            match v1, v2 with
            | VUnit, VUnit -> true
            | VBool b1, VBool b2 -> b1 = b2
            | VNum n1, VNum n2 -> n1 = n2
            | _ ->
                (* Other cases (e.g., functions) are not intended to occur
                   in well-typed student programs. *)
                failwith "internal error: equality on unsupported values"
          in
          VBool (if op = Eq then equal else not equal)

(* Entry point used by the grader. *)
let eval (e : expr) : value =
  eval_with Env.empty e

let interp (s : string) : (value, error) result =
  match parse s with
  | None -> Error ParseErr
  | Some p ->
      let e = desugar p in
      match type_of e with
      | Error e -> Error e
      | Ok _ ->
          (* On well-typed programs, evaluation should not raise any
             of the static-error variants; DivByZero / AssertFail are
             raised as OCaml exceptions instead, as required. *)
          Ok (eval e)