def implb : bool → bool → bool
|  true false => false
|  _ _ => true

open Nat
theorem inj (m n : Nat) : succ m = succ n → m = n := by
    intro h
    cases h
    rfl
open Classical

theorem h1 : ¬(P ∧ Q) → ¬ P ∨ ¬ Q := by
  intro h
  cases em P with
  | inl p =>
    cases em Q with
    | inl q =>
      have f : False := by
        apply h
        constructor
        exact p
        exact q
      cases f
    | inr nq =>
      right
      exact nq
  | inr np =>
    left
    exact np

theorem h2 {P Q} : ¬ P ∨ ¬ Q → ¬ (P ∧ Q) := by
  intro h
  cases h with
  | inl np =>
    intro h1
    apply np
    cases h1 with
    | intro p q =>
      exact p
  | inr nq =>
    intro h1
    apply nq
    cases h1 with
    | intro p q =>
      exact q


theorem h4 {P} : P → ¬¬ P := by
    intro p
    intro np
    apply np
    exact p

theorem h5 : ¬¬ P → P := by
    intro h
    cases em P with
    | inl p =>
      exact p
    | inr np =>
      have f : False := by
        apply h
        exact np
      cases f

theorem h6 : (P → Q)  → ¬ P ∨ Q := by
  intro h
  cases em P with
  | inl p =>
    right
    exact h p
  | inr np =>
    left
    exact np

theorem h7 : ¬ P ∨ Q → (P → Q) := by
  intro h
  intro p
  cases em Q with
  | inl q =>
    exact q
  | inr nq =>
    cases h with
    | inl np =>
      have f : False := by
        apply np
        exact p
      cases f
    | inr q =>
      exact q

theorem h8 : ¬ (P ∨ Q) → ¬P ∨ ¬Q := by
  intro h
  constructor
  . intro p
    apply h
    left
    exact p



theorem h9 : ¬ P ∨ ¬ Q → ¬ (P ∨ Q) := by
  intro h
  sorry

inductive List (a : Type ) : Type
| nil : List a
| cons : a → List a → List a

def tree2list : Tree → List
| leaf n => [n]
| node l r => tree2list l ++ tree2list r
