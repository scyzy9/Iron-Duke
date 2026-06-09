/-

Lecture 15 : Decidability

-/
namespace l15

set_option tactic.customEliminators false
notation "ℕ" => Nat -- \bn
open Nat

-- decidability
-- m n : ℕ
-- m = n : Prop

def eq_ℕ : ℕ → ℕ → Bool
| zero , zero => true
| zero , succ _ => false
| succ _ , zero => false
| succ m , succ n => eq_ℕ m n

#eval eq_ℕ 3 4
#eval eq_ℕ 3 3

-- to show that eq_ℕ decides = on ℕ
-- ∀ m n : ℕ, m = n ↔ eq_ℕ m n = true
-- (P ↔ Q) → ¬ P ↔ ¬ Q
-- b ≠ true → b = false
-- ∀ m n : ℕ, m ≠ n ↔ eq_ℕ m n = false

def eq_ℕ_mafia : ℕ → ℕ → Bool
| _ , _ => true

def eq_ℕ_cia : ℕ → ℕ → Bool
| _ , _ => false

theorem refl_eq_ℕ : ∀ n : ℕ, eq_ℕ n n = true := by
intro n
induction n with
| zero =>
    rfl
| succ m ih =>
    calc
      eq_ℕ (succ m) (succ m)
        = eq_ℕ m m := by rfl
      _ = true := by assumption

theorem Eq2eq : ∀ m n : ℕ, m = n → eq_ℕ m n = true := by
  intro m n mn
  calc
    eq_ℕ m n =
       eq_ℕ m m := by rw [mn]
    _= true := by rw [refl_eq_ℕ]

theorem eq2Eq : ∀ m n : ℕ, eq_ℕ m n = true → m = n := by
intro m
induction m with
| zero =>
  intro n mn
  cases n with
  | zero =>
     rfl
  | succ n =>
     --dsimp [eq_ℕ] at mn
     cases mn
| succ m ih =>
    intro n mn
    cases n with
    | zero =>
        cases mn
    | succ n =>
        have h : m = n := by
         apply ih
         calc
          eq_ℕ m n
          = eq_ℕ (succ m) (succ n) := by rfl
          _ = true := by rw [mn]
        rw [h]


theorem dec_eq_ℕ : ∀ m n : ℕ, m = n ↔ eq_ℕ m n = true := by
intro m n
constructor
. apply Eq2eq
. apply eq2Eq

-- equality on natural numbers is decidable

def Eq0 : ℕ → Prop
| n => n=0

def eq0 : ℕ → Bool
| zero => true
| succ _ => false

-- Eq0 n ↔ eq0 n = true

-- are there undecidable predicates (or relations)
-- Halt : ℕ → Prop
-- Halt p : program p halts, doesn't loop

def ExTrue : (ℕ → Bool) → Prop
| f => ∃ n : ℕ, f n = true

-- StopsN : ℕ → ℕ → Bool
-- Stopsℕ p n = program p halts after n steps
-- Halt p = ExTrue (StopsN p)

end l15
