open Asm.Directive
open S_exp
open Util

(** Constants used for tagging values at runtime. *)

let num_shift = 2

let num_mask = 0b11

let num_tag = 0b00

let bool_shift = 7

let bool_mask = 0b1111111

let bool_tag = 0b0011111

type symtab =
  int Symtab.symtab

(** [operand_of_num x] returns the runtime representation of the number [x] as
    an operand for instructions. *)
let operand_of_num : int -> operand =
  fun x ->
    Imm ((x lsl num_shift) lor num_tag)

(** [operand_of_bool b] returns the runtime representation of the boolean [b] as
    an operand for instructions. *)
let operand_of_bool : bool -> operand =
  fun b ->
    Imm (((if b then 1 else 0) lsl bool_shift) lor bool_tag)

let zf_to_bool =
  [ Mov (Reg Rax, Imm 0)
  ; Setz (Reg Rax)
  ; Shl (Reg Rax, Imm bool_shift)
  ; Or (Reg Rax, Imm bool_tag)
  ]

let setl_bool =
  [ Mov (Reg Rax, Imm 0)
  ; Setl (Reg Rax)
  ; Shl (Reg Rax, Imm bool_shift)
  ; Or (Reg Rax, Imm bool_tag)
  ]

let stack_address : int -> operand =
  fun index ->
    MemOffset (Imm index, Reg Rsp)

let rec stack_index_helper : string list -> int -> int list =
  fun var_list stack_index ->
    begin match var_list with
    [] -> []
    | _ :: rest ->
      [stack_index]
      @ stack_index_helper rest (stack_index - 8)
    end

let rec stack_index_counter : string list -> int -> int =
  fun var_list stack_index->
    begin match var_list with
    [] -> 
      stack_index
    | _ :: rest ->
      stack_index_counter rest (stack_index - 8)
    end



(** [compile_primitive stack_index e prim] produces x86-64 instructions for the
     primitive operation named by [prim] given a stack index of [stack_index];
     if [prim] isn't a valid operation, it raises an error using the
     s-expression [e]. *)
let compile_primitive : int -> s_exp -> string -> directive list =
  fun stack_index e prim ->
    begin match prim with
      | "add1" ->
          [ Add (Reg Rax, operand_of_num 1)
          ]

      | "sub1" ->
          [ Sub (Reg Rax, operand_of_num 1)
          ]

      | "zero?" ->
          [ Cmp (Reg Rax, operand_of_num 0)
          ]
          @ zf_to_bool

      | "num?" ->
          [ And (Reg Rax, Imm num_mask)
          ; Cmp (Reg Rax, Imm num_tag)
          ]
          @ zf_to_bool

      | "not" ->
          [ Cmp (Reg Rax, operand_of_bool false)
          ]
          @ zf_to_bool

      | "+" ->
          [ Add (Reg Rax, stack_address stack_index)
          ]

      | "-" ->
          [ Mov (Reg R8, Reg Rax)
          ; Mov (Reg Rax, stack_address stack_index)
          ; Sub (Reg Rax, Reg R8)
          ]

      | "=" ->
          [ Cmp (stack_address stack_index, Reg Rax)
          ]
          @ zf_to_bool

      | "<" ->
          [ Cmp (stack_address stack_index, Reg Rax)
          ]
          @ setl_bool

      | "*" ->
          [ 
            (* Sar (Reg Rax, Imm num_shift) *)
          (* ;  *)
          Mov (Reg R8, stack_address stack_index)
          (* ; Sar (Reg R8, Imm num_shift) *)
          ; Mul (stack_address stack_index)
          (* ; Shl (Reg Rax, Imm num_shift) *)
          ; Sar (Reg Rax, Imm num_shift)
          ]

      | "/" ->
          [ Mov (Reg R8, Reg Rax)
          ; Mov (Reg Rax, stack_address stack_index)
          ; Cqo
          ; Div (Reg R8)
          ; Shl (Reg Rax, Imm num_shift)
          ]

      | _ ->
          raise (Error.Stuck e)
    end

(** [compile_expr tab stack_index e] produces x86-64 instructions for the
    expression [e] given a symtab of [tab] and stack index of [stack_index]. *)
let rec compile_expr : symtab -> int -> s_exp -> directive list =
  fun tab stack_index e ->
    begin match e with
      | Num x ->
          [ Mov (Reg Rax, operand_of_num x)
          ]

      | Sym "true" ->
          [ Mov (Reg Rax, operand_of_bool true)
          ]

      | Sym "false" ->
          [ Mov (Reg Rax, operand_of_bool false)
          ]

      | Sym var when Symtab.mem var tab ->
          [ Mov (Reg Rax, stack_address (Symtab.find var tab))
          ]

      | Lst [Sym "if"; test_expr; then_expr; else_expr] ->
          let else_label =
            gensym "else"
          in
          let continue_label =
            gensym "continue"
          in
          compile_expr tab stack_index test_expr
            @ [Cmp (Reg Rax, operand_of_bool false)]
            @ [Je else_label]
            @ compile_expr tab stack_index then_expr
            @ [Jmp continue_label]
            @ [Label else_label]
            @ compile_expr tab stack_index else_expr
            @ [Label continue_label]

      | Lst [Sym "let"; Lst [Lst [Sym var; exp]]; body] ->
          compile_expr tab stack_index exp
            @ [Mov (stack_address stack_index, Reg Rax)]
            @ compile_expr
                (Symtab.add var stack_index tab)
                (stack_index - 8)
                body

      | Lst [Sym "let"; Lst bindings; body] ->
          let bindings_pairs = get_bindings bindings
          in
          let vars, _ = List.split bindings_pairs
          in
          (* let val_directives = List.map (compile_expr tab stack_index) exps
          in *)
          let indices = (stack_index_helper vars stack_index)
          in
          let env = List.fold_right2 Symtab.add (List.rev vars) (List.rev indices)tab
          in
          (* let env = List.fold
          in  *)
          (
          let rec let_helper : symtab -> s_exp list -> int -> directive list =
            fun reference current_list s_index ->
              begin match current_list with
                [] -> []
                | head :: [] ->
                  (
                    begin match head with
                      Lst [Sym _; exp] ->
                        compile_expr reference s_index exp
                        @ [Mov (stack_address s_index, Reg Rax)]
                      | _ -> raise (Error.Stuck e)
                    end
                  )
                | head :: rest ->
                  (
                    begin match head with
                      Lst [Sym _; exp] ->
                        compile_expr reference s_index exp
                        @ [Mov (stack_address s_index, Reg Rax)]
                        @ let_helper reference rest (s_index - 8)
                      | _ -> raise (Error.Stuck e)
                    end
                  )

              end
          in
          let_helper tab bindings stack_index
          @ compile_expr env (stack_index_counter vars stack_index) body
          )
      
      | Lst (Sym "case" :: scrutinee_exp :: rest) ->
        let rec min_case_finder : s_exp list -> int -> int = 
          fun remaining current_min ->
            begin match remaining with
              head :: rest -> 
                (
                begin match head with
                  Lst [Num x; _] ->
                    if (x < current_min) then 
                      (min_case_finder rest x)
                    else
                      (min_case_finder rest current_min)
                  | _ -> 
                    raise (Error.Stuck e)
                end
                )
              | [] ->
                current_min
            end
        in
        []


      | Lst [Sym f; arg]->
          compile_expr tab stack_index arg
            @ compile_primitive stack_index e f

      | Lst [Sym "and"; exp1; exp2] ->
          let else_label =
            gensym "else"
          in
          let continue_label =
            gensym "continue"
          in
          compile_expr tab stack_index exp1
          (* if rax == false *)
            @ [Cmp (Reg Rax, operand_of_bool false)]
            @ [Je else_label]

            (* Else *)
            @ compile_expr tab stack_index exp2
            @ [Jmp continue_label]

            (* Then *)
            @ [Label else_label]
            @ [Mov (Reg Rax, operand_of_bool false)]

            @ [Label continue_label]

      | Lst [Sym "or"; exp1; exp2] ->
          let else_label =
            gensym "else"
          in
          let continue_label =
            gensym "continue"
          in
          compile_expr tab stack_index exp1
            @ [Cmp (Reg Rax, operand_of_bool false)]
            @ [Je else_label]
            (* @ compile_expr tab stack_index exp2 *)
            @ [Jmp continue_label]
            @ [Label else_label]
            @ compile_expr tab stack_index exp2
            @ [Label continue_label]

      | Lst [Sym f; arg1; arg2] ->
          compile_expr tab stack_index arg1
            @ [Mov (stack_address stack_index, Reg Rax)]
            @ compile_expr tab (stack_index - 8) arg2
            @ compile_primitive stack_index e f

      | _ ->
          raise (Error.Stuck e)
    end

(** [compile e] produces x86-64 instructions, including frontmatter, for the
    expression [e]. *)
let compile : s_exp -> directive list =
  fun e ->
    [ Global "lisp_entry"
    ; Section "text"
    ; Label "lisp_entry"
    ]
    @ compile_expr Symtab.empty (-8) e
    @ [Ret]
