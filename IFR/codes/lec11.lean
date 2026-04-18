
namespace NatDef

--Peano Arithmetic
inductive Nat : Type
| zero : Nat
| succ : Nat → Nat

open Nat

#check zero
#check succ zero
#check succ (succ zero)

end NatDef

#check 8 -- succ (succ (succ ......))

notation "ℕ" => Nat

open Nat

#eval succ 7

def double : ℕ → ℕ
| zero => zero
| succ n => succ (succ (double n))

#eval double 8

-- def bad : ℕ → ℕ
-- | zero => zero
-- | succ n => bad (succ n)

def half : ℕ → ℕ
| zero => zero
| succ zero => zero
| succ (succ n) => succ (half n)
--half succ (succ 14) = succ (half 14)

def half_aux : ℕ → ℕ → ℕ
| zero , n => n
| succ zero , n => n
| succ (succ m) , n => half_aux m (succ n)

def half_ite : ℕ → ℕ
| n => half_aux n zero


#eval half (double 2025)

theorem half_double : ∀ n : ℕ, half (double n) = n := by
  intro n
  induction n with
  | zero =>
    rfl
  | succ n ih =>
    dsimp [half,double]
    rw[ih]

theorem half_double_alt : ∀ n : ℕ, half (double n) = n := by
  intro n
  induction n with
  | zero =>
    rfl
  | succ n ih =>
    calc
      half (double (succ n))
      = half (succ (succ (double n))) := by rfl
      _ = succ (half (double n)) := by rfl
      _ = succ n := by rw[ih]


-- zero is not the succ of any number
theorem peano5 : ∀ n : ℕ, succ n ≠ zero := by
  intro n h
  cases h

-- if the successors of two numbers agree, the two numbers are the same.
def prd : ℕ → ℕ
| zero => zero
| succ m => m

theorem peano6 : ∀ n m : ℕ, succ n = succ m → n = m := by
  intro n m
  intro h
  change (prd (succ n)) = m
  rw [h]
  rfl

theorem peano6_alt : ∀ n m : ℕ, succ n = succ m → n = m := by
  intro n m h
  cases h
  rfl
