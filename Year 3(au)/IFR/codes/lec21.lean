/-

Lecture 21 : Trees

-/


namespace l21

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

-- denotational semantics
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

-- def compile : Expr → Code
-- | const n => [ pushC n]
-- | var x => [ pushV x]
-- | plus l r => compile l ++ compile r ++ [add]
-- | times l r => compile l ++ compile r ++ [mult]

-- continuation passing compiler

def compile_aux : Expr → Code → Code
| const n , c => pushC n :: c
| var x, c => pushV x :: c
| plus l r , c =>
    compile_aux l (compile_aux r (add :: c))
| times l r , c =>
    compile_aux l (compile_aux r (mult :: c))

def compile : Expr → Code
| e => compile_aux e []

#eval run (compile e1) [] env0

#eval run (compile e2) [] env0

theorem compile_aux_ok :
  ∀ e : Expr,∀ c : Code,∀ s : Stack, ∀ env : Env,
  run (compile_aux e c) s env
  = run c (eval e env :: s) env := by
  intro e
  induction e with
  | const n =>
      intros c s env
      dsimp [compile_aux,run,eval]
  | var x =>
      intros c s env
      dsimp [compile_aux,run,eval]
  | plus l r ihl ihr =>
      intros c s env
      calc run (compile_aux (plus l r) c) s env
        = run (compile_aux l (compile_aux r (add::c))) s env := by rfl
        _ = run (compile_aux r (add::c))
              (eval l env :: s) env := by rw [ihl]
        _ = run (add::c)
              (eval r env :: eval l env :: s) env := by rw [ihr]
        _ = run c ((eval l env + eval r env) :: s) env
          := by rfl
        _ = run c (eval (plus l r) env :: s) env := by rfl
  | times l r ihl ihr =>
    intros c s env
    calc run (compile_aux (times l r) c) s env
        = run (compile_aux l (compile_aux r (mult::c))) s env := by rfl
        _ = run (compile_aux r (mult::c))
              (eval l env :: s) env := by rw [ihl]
        _ = run (mult::c)
              (eval r env :: eval l env :: s) env := by rw [ihr]
        _ = run c ((eval l env * eval r env) :: s) env
          := by rfl
        _ = run c (eval (times l r) env :: s) env := by rfl

theorem compile_ok : ∀ e : Expr, ∀ env : Env,
   run (compile e) [] env = eval e env := by
   intro e env
   calc
    run (compile e) [] env
    = run (compile_aux e []) [] env := by rfl
    _ = run [] (eval e env::[]) env :=
      by rw [compile_aux_ok]
    _ = eval e env := by rfl


-- Goedel's theorem
-- complete ⊢ P or ⊢ ¬ P
-- Goedel sentences ¬ ⊢ G, ¬ ⊢ ¬ G
-- 1st incompleteness arithmetic
-- 2nd you can prove its own consistency in arithmetic




end l21
