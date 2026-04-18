/-

Lecture 20 : Trees

-/


namespace l20

set_option tactic.customEliminators false

notation "ℕ" => Nat -- \bn
open Nat

-- "x * (y + 2)""
-- "x * y + 2"


inductive Expr : Type
| const : ℕ → Expr
| var : String → Expr
| plus : Expr → Expr → Expr
| times : Expr → Expr → Expr

open Expr -- Expr.const ==> const

def e1 : Expr
:= times (var "x") (plus (var "y") (const 2))

def e2 : Expr
:= plus (times (var "x") (var "y")) (const 2)

def x : ℕ := 3
def y : ℕ := 5

#eval x * (y + 2)
#eval x * y + 2

#eval e1
#eval e2

def Env : Type
:= String → ℕ -- undefined = 0

def eval : Expr → Env → ℕ
| var x , env => env x
| const n , env => n
| plus l r , env => (eval l env) + (eval r env)
| times l r , env => (eval l env) * (eval r env)

def env0 : Env
| "x" => 3
| "y" => 5
| _ => 0

#eval eval e1 env0
#eval eval e2 env0

inductive Instr : Type
| pushC : ℕ → Instr
| pushV : String → Instr
| add : Instr
| mult : Instr

open Instr

abbrev Code : Type
:= List Instr

def Stack : Type
:= List ℕ

--run means to execute Code on Stack with Env
def run : Code → Stack → Env → ℕ
| [] , [n] , env => n
| pushC n :: c , s, env =>
    run c (n::s) env
| pushV x :: c , s , env =>
    run c (env x :: s) env
| add :: c , m :: n :: s, env =>
    run c ((n + m) :: s) env
| mult :: c , m :: n :: s, env =>
    run c ((n * m) :: s) env
| _ , _ , _ => 0

def c1 : Code
:= [pushV "x", pushV "y",pushC 2, add, mult]

#eval run c1 [] env0

def c2 : Code
:= [pushV "x", pushV "y",mult, pushC 2,add]

#eval run c2 [] env0

--compile means to translate high level Expr to low level Code
def compile : Expr → Code
| const n => [ pushC n]
| var x => [ pushV x]
| plus l r => compile l ++ compile r ++ [add]
| times l r => compile l ++ compile r ++ [mult]

#eval run (compile e1) [] env0

#eval run (compile e2) [] env0

theorem compile_ok : ∀ e : Expr, ∀ env : Env,
  run (compile e) [] env = eval e env := sorry






end l20
