/- COMP2065 (IFR) - Tutorial 7 -/

namespace tutorial7

set_option pp.fieldNotation false

/- Ordering -/

inductive ℕ : Type
| zero : ℕ
| succ : ℕ → ℕ
open ℕ

def add : ℕ → ℕ → ℕ
| m  , zero     => m
| m  , succ n => succ (add m n)

def LE : ℕ → ℕ → Prop
| m , n => ∃ k : ℕ , add k m = n

theorem le_refl : ∀ n : ℕ, LE n n := by
  intro n
  induction n with
  | zero =>
    dsimp[LE]
    exists zero
  | succ n ih =>
    cases ih with
    | intro k h =>
      dsimp[LE]
      exists zero
      dsimp[add]
      cases k with
      | zero =>
        rw[h]
      | succ k' =>
        sorry




theorem le_succ : ∀ m n : ℕ, LE m n → LE (succ m) (succ n) := by
  intro m n
  intro h
  cases h with
  | intro k h1 =>
  sorry

/- Decidaibility -/

def ineq : ℕ → ℕ → Bool :=
  sorry

theorem ineq_irefl : ∀ m : ℕ, ineq m m = false := by
  sorry

theorem add_inj : ∀ m n : ℕ, succ m = succ n → m = n := by
  intro m n succ_m_eq_succ_n
  cases succ_m_eq_succ_n
  rfl

theorem ineq_sound : ∀ m n, ineq m n = true → m ≠ n := by
  sorry

theorem ineq_complete : ∀ m n, m ≠ n → ineq m n = true := by
  sorry
