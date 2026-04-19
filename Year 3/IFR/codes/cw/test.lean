/-
Lean class test for COMP2065
(Introduction to Formal Reasoning)

Replace all the "sorry"s below by Lean proofs
using only the tactics introduced in the
lectures and only in the way they were taught.

You have 50 minutes time.
-/
set_option linter.unusedVariables false
namespace test
open Classical

variable (P Q R : Prop)
variable {A : Type}
variable (PP QQ : A → Prop)

theorem raa : ¬¬P → P := by
  intro nnp
  have pnp : P ∨ ¬P := by
    apply em
  cases pnp with
  | inl p => exact p
  | inr np =>
    have f : False := by
      apply nnp
      exact np
    cases f

open Nat
def max : Nat → Nat → Nat
| zero, n => n
| (succ m), zero => succ m
| (succ m), (succ n) => succ (max m n)

#eval (max 4 7)

theorem add_assoc : ∀ l m n : Nat , (l + m) + n = l + (m + n) := by
  intro l m n
  induction n with
  | zero => rfl
  | succ n' ih =>
    calc
      l + m + (n' + 1)
      _ = l + m + n' + 1 := by rfl
      _= l + (m + n') + 1 := by rw [ih]

open List

def addlist : Nat → List Nat → List Nat
| n, [] => []
| n, (m :: ms) => (m + n) :: addlist n  ms

#eval addlist 3 [1,2,3]

/- --- Do not change or delete anything above this line --- -/


theorem e01 : (P ∨ Q) ∨ R  → P ∨ (Q ∨ R) := by
  intro h
  cases h with
  | inl hq =>
    cases hq with
    | inl p =>
      left
      exact p
    | inr q =>
      right
      left
      exact q
  | inr r =>
    right
    right
    exact r

theorem e02 : Q ∧ P  → P ∧ Q := by
  intro h
  cases h with
  | intro q p =>
    constructor
    . exact p
    . exact q

theorem e03 : P → (¬ Q → ¬ P) → Q := by
  intro p h
  have qnq : Q ∨ ¬ Q := by
    exact em Q
  cases qnq with
  | inl q =>
    exact q
  | inr nq =>
    have np : ¬ P := by
      exact h nq
    have f : False := by
      apply np
      exact p
    cases f

theorem e04 : P → (True ↔ P) := by
  intro p
  constructor
  . intro t
    exact p
  . intro p'
    constructor

theorem e05 : (∃ x : A, PP x)
  → (∀ x : A, False) → P := by
  intro h1
  intro h2
  cases h1 with
  | intro a ppa =>
    have f : False := by
      exact h2 a
    cases f

theorem e06 : ∀ x : A,
  PP x ↔ (∃ y : A, x = y ∧ PP y) := by
  intro x
  constructor
  . intro ppx
    apply Exists.intro x
    constructor
    . rfl
    . exact ppx
  . intro h
    cases h with
    | intro y h1 =>
      cases h1 with
      | intro xy ppy =>
        rw[xy]
        exact ppy

theorem e07 : ∀ x : Bool,
  x = !! x := by
  intro x
  cases x with
  | false =>
    rfl
  | true =>
    rfl

theorem e08 : ∀ m : Nat, max m m = m := by
  intro m
  induction m with
  | zero =>
    rfl
  | succ m ih =>
    calc max (m + 1) (m + 1)
      = succ (max m m) := by rfl
    _ = succ m := by rw[ih]
    _ = m + 1 := by rfl


theorem e09 : ∀ ms : List Nat , addlist 0 ms = ms := by
  intro ms
  induction ms with
  | nil =>
    rfl
  | cons m ms ih =>
    rw[addlist]
    calc (m + 0) :: addlist 0 ms
      = (m + 0) :: ms := by rw[ih]
    _ = m :: ms := by rfl

theorem e10 : ∀ m n : Nat, ∀ ms : List Nat,
  addlist m (addlist n ms) = addlist (n + m) ms := by
  intro m n
  intro ms
  induction ms with
  | nil =>
    rfl
  | cons k ks ih =>
    dsimp[addlist]
    calc (k + n + m) :: addlist m (addlist n ks)
      = (k + n + m) :: addlist (n + m) ks := by rw[ih]
    _ = (k + (n + m)) :: addlist (n + m) ks := by rw[add_assoc]

-- /Do not change/remove below --
end test
