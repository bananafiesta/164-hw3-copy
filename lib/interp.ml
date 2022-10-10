open Printf
open S_exp

(** A [value] is the runtime value of an expression.  *)
type value
  = Num of int
  | Bool of bool

type environment =
  value Symtab.symtab

let top_env : environment =
  Symtab.empty
    |> Symtab.add "true" (Bool true)
    |> Symtab.add "false" (Bool false)

(** [display_value v] returns a string representation of the runtime value
    [v]. *)
let display_value : value -> string =
  fun v ->
    begin match v with
      | Num x ->
          sprintf "%d" x

      | Bool b ->
          if b then
            "true"
          else
            "false"
    end






(** [interp_unary_primitive prim arg] tries to evaluate the primitive operation
    named by [prim] on the argument [arg]. If the operation is ill-typed, or if
    [prim] does not refer to a valid primitive operation, it returns [None]. *)
let interp_unary_primitive : string -> value -> value option =
  fun prim arg ->
    begin match (prim, arg) with
      | ("add1", Num x) ->
          Some (Num (x + 1))

      | ("sub1", Num x) ->
          Some (Num (x - 1))

      | ("zero?", Num 0) ->
          Some (Bool true)

      | ("zero?", _) ->
          Some (Bool false)

      | ("num?", Num _) ->
          Some (Bool true)

      | ("num?", _) ->
          Some (Bool false)

      | ("not", Bool false) ->
          Some (Bool true)

      | ("not", _) ->
          Some (Bool false)

      | _ ->
          None
    end

(** [interp_binary_primitive prim arg1 arg2] tries to evaluate the primitive
    operation named by [prim] on the arguments [arg1] and [arg2]. If the
    operation is ill-typed, or if [prim] does not refer to a valid primitive
    operation, it returns [None]. *)
let interp_binary_primitive : string -> value -> value -> value option =
  fun prim arg1 arg2 ->
    begin match (prim, arg1, arg2) with
      | ("+", Num x1, Num x2) ->
          Some (Num (x1 + x2))

      | ("-", Num x1, Num x2) ->
          Some (Num (x1 - x2))

      | ("=", Num x1, Num x2) ->
          Some (Bool (x1 = x2))

      | ("<", Num x1, Num x2) ->
          Some (Bool (x1 < x2))

      | ("*", Num x1, Num x2) ->
          Some (Num (x1 * x2))

      (* | ("/", Num x1, Num 0) ->
          None *)

      | ("/", Num x1, Num x2) ->
          Some (Num (x1 / x2))

      | _ ->
          None
    end

(** [interp_expr e] tries to evaluate the s-expression [e], producing a
    value. If [e] isn't a valid expression, it raises an error. *)
let rec interp_expr : environment -> s_exp -> value =
  fun env e ->
    begin match e with
      | Num x ->
          Num x

      | Sym var ->
          begin match Symtab.find_opt var env with
            | Some value ->
                value

            | None ->
                raise (Error.Stuck e)
          end

      | Lst [Sym "let"; Lst [Lst [Sym var; exp]]; body] ->
          let env =
            env
              |> Symtab.add var (interp_expr env exp)
          in
          interp_expr env body
      
      | Lst [Sym "let"; Lst bindings; body] ->
        (
        let rec let_helper : environment -> environment -> s_exp list -> environment =
          fun reference current_env current_list ->
            begin match current_list with
              [] -> 
                current_env
        
              (* cases where it matches *)
              | head :: [] ->
                (
                begin match head with
                  Lst [Sym var; exp] -> 
                    (Symtab.add var (interp_expr reference exp) current_env)
                  | _ -> raise (Error.Stuck e)
                end
                )
        
              | head :: rest ->
                (
                begin match head with
                  Lst [Sym var; exp] ->
                    (let_helper reference (Symtab.add var (interp_expr reference exp) current_env) rest)
                  | _ -> raise (Error.Stuck e)

                end
                )
                (* let env = Symtab.add var (interp_expr reference exp)
                in var *)
              (* | _ -> 
                raise (Error.Stuck e) *)
                
            end
        in 
          (
          let bound_env = let_helper env env bindings
          in
          
            interp_expr bound_env body
          
          )
        )

      | Lst (Sym "case" :: scrutinee_exp :: rest) ->
        (
        let scrutinee = 
          interp_expr env scrutinee_exp
        in
        let rec case_helper : int -> s_exp list -> value =
          fun target cases ->
            begin match cases with
              head :: [] -> 
                (
                begin match head with
                  Lst [Num _; exp] ->
                    interp_expr env exp
                  | _ -> raise (Error.Stuck e)
                end
                )
              | head :: tail -> 
                (
                begin match head with
                Lst [Num x; exp] ->
                  if (x = target) then
                    (interp_expr env exp)
                  else
                    (case_helper target tail)
                | _ ->
                  raise (Error.Stuck e)
                end
                )
              | [] -> 
                raise (Error.Stuck e)
            end
        in
        let rec case_checker: s_exp list -> value =
          fun cases ->
            begin match cases with
              head :: [] -> 
                (
                begin match head with
                  Lst [Num _; _] ->
                    Bool true
                  | _ -> raise (Error.Stuck e)
                end
                )
              | head :: tail -> 
                (
                begin match head with
                Lst [Num _; _] ->
                  case_checker tail
                | _ ->
                  raise (Error.Stuck head)
                end
                )
              | [] -> 
                raise (Error.Stuck e)
            end
        in
          begin match scrutinee with
            Num x -> 
              (* continue execution *)
              let _ = case_checker rest
              in
              case_helper x rest
            | _ -> raise (Error.Stuck e)
          end

        )
            

      | Lst [Sym "if"; test_exp; then_exp; else_exp] ->
          if interp_expr env test_exp <> Bool false then
            interp_expr env then_exp
          else
            interp_expr env else_exp

      | Lst [Sym "and"; exp1; exp2] ->
          let x =
            interp_expr env exp1
          in
          (
          if x = Bool false then
            x
          else
            interp_expr env exp2
            )

      | Lst [Sym "or"; exp1; exp2] ->
          let x = interp_expr env exp1
          in
          (
            if x <> Bool false then
              x
            else
              interp_expr env exp2
          )


      | Lst [Sym f; arg] ->
          begin match interp_unary_primitive f (interp_expr env arg) with
            | Some v ->
                v

            | None ->
                raise (Error.Stuck e)
          end

      | Lst [Sym f; arg1; arg2] ->
          begin match
            interp_binary_primitive
              f
              (interp_expr env arg1)
              (interp_expr env arg2)
          with
            | Some v ->
                v

            | None ->
                raise (Error.Stuck e)
          end

      | _ ->
          raise (Error.Stuck e)
    end

(** [interp e] evaluates the s-expression [e] using [interp_expr], then formats
    the result as a string. *)
let interp : s_exp -> string =
  fun e ->
    e
      |> interp_expr top_env
      |> display_value

