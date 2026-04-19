/-
COMP2065-IFR Exercise 05
(Natural numbers)

Exercise 05 (Natural numbers)

The goal is to complete the proof that the natural
numbers with addition and multiplication form a
semiring. I include the proof the addition forms a
commutative monoid (which we have done in the lecture.

It may be advisable not to prove the theorems in
the order I list them! Also you will need to prove
some lemmas (auxilliary theorems).
-/

namespace mult_monoid

open Nat

-- We know that (ℕ, +) is a commutative monoid:

theorem add_rneutr : ∀ n : Nat, n + 0 = n := by
  intro n
  rfl

theorem add_lneutr : ∀ n : Nat, 0 + n  = n := by
  intro n
  induction n with
  | zero => rfl
  | succ n' ih =>
    calc
      0+(n' + 1) = 0 + n' + 1 := by rfl
      _ = (0 + n') + 1 := by rfl
      _ = n' + 1 := by rw [ih]

theorem add_assoc : ∀ l m n : Nat , (l + m) + n = l + (m + n) := by
  intro l m n
  induction n with
  | zero => rfl
  | succ n' ih =>
    calc
      l + m + (n' + 1) = l + m + n' + 1 := by rfl
      _ = l + (m + n') + 1 := by rw [ih]

theorem add_succ_lem : ∀ m n : Nat, (succ m) + n = succ (m + n) := by
  intro m n
  induction n with
  | zero => rfl
  | succ n' ih =>
    calc
      (succ m) + (n' + 1) = (succ m) + n' + 1 := by rfl
      _ = (succ (m + n')) + 1 := by rw [ih]
      _ = succ ((m + n') + 1) := by rfl

theorem add_comm : ∀ m n : Nat , m + n = n + m := by
  intro m n
  induction m with
  | zero => apply add_lneutr
  | succ m' ih =>
    calc
      (succ m') + n = succ (m' + n) := by apply add_succ_lem
      _ = succ (n + m') := by rw [ih]
      _ = n + (succ m') := by rfl

-- Now we will consider multiplication:
#eval 2 * 3 = 6

/- --- Do not add/change anything above this line  -/

-- Your task is to show that it is a commutative semiring, i.e.

-- 1 acts as an identity for multiplication
theorem mult_rneutr : ∀ n : Nat, n * 1 = n := by
  intro n
  have h1 : n * 1 = n * 0 + n := rfl
  have h0 : n * 0 = 0 := rfl
  rw[h1]
  rw[h0]
  rw[add_lneutr]

theorem mult_lneutr : ∀ n : Nat, 1 * n = n := by
  intro n
  induction n with
  | zero =>
    rfl
  | succ n ih =>
    calc 1 * (succ n)
      = 1 * n + 1 := rfl
    _ = n + 1 := by rw[ih]


-- Anything multiplied by 0 is 0
theorem mult_zero_r : ∀ n : Nat , n * 0 = 0 := by
  intro n
  rfl

theorem mult_zero_l : ∀ n : Nat , 0 * n = 0 := by
  intro n
  induction n with
  | zero =>
    rfl
  | succ n ih =>
    calc 0 * (succ n)
      = 0 * n + 0 := by rfl
    _ = 0 := by rw[ih]

-- Multiplication distributes over addition
theorem mult_distr_r :  ∀ l m n : Nat , l * (m + n) = l * m + l * n := by
  intro l m n
  induction n with
  | zero =>
    calc l * (m + 0)
      = l * m := rfl
      _ = l * m + 0 := rfl
      _ = l * m + l * 0 := rfl
  | succ n ih =>
    calc l * (m + succ n)
      = l * succ (m + n) := by rfl
      _ = l * (m + n) + l := by rfl
      _ = (l * m + l * n) + l := by rw [ih]
      _ = l * m + (l * n + l) := by rw [add_assoc]
      _ = l * m + l * succ n := by rfl

theorem mult_distr_l :  ∀ l m n : Nat , (m + n) * l = m * l + n * l := by
  intro l m n
  induction l with
  | zero =>
    calc (m + n) * 0 = m * 0 + n * 0 := by rfl
  | succ l ih =>
  calc (m + n) * succ l
  = (m + n) * l + (m + n) := by rfl
  _ = (m * l + n * l) + (m + n) := by rw [ih]
  _ = m * l + (n * l + (m + n)) := by rw [add_assoc]
  _ = m * l + ((n * l + m) + n) := by rw [add_assoc]
  _ = m * l + ((m + n * l) + n) := by
    have h_comm : n * l + m = m + n * l := add_comm (n * l) m
    rw [h_comm]
  _ = m * l + (m + (n * l + n)) := by rw [add_assoc]
  _ = (m * l + m) + (n * l + n) := by rw [← add_assoc]
  _ = m * succ l + (n * l + n) := by rfl
  _ = m * succ l + n * succ l := by rfl

-- Multiplication is associative
theorem mult_assoc : ∀ l m n : Nat , (l * m) * n = l * (m * n) := by
  intro l m n
  induction n with
  | zero =>
    calc l * m * 0 = 0 := by rw[mult_zero_r]
    _ = l * 0 := by rw [mult_zero_r]
  | succ n ih =>
    calc (l * m) * n.succ = (l * m) * n + (l * m) := by rfl
    _ = l * (m * n) + l * m := by rw[ih]
    _ = l * (m * n + m) := by rw[mult_distr_r]
    _ = l * (m * (succ n)) := by rfl

-- And also commutative
theorem succ_mult : ∀ m n : Nat , (succ m) * n = m * n + n := by
  intro m n
  induction n with
  | zero =>
    calc (succ m) * 0 = 0 := by rw[mult_zero_r]
    _ = 0 + 0 := by rfl
    _ = m * 0 + 0 := by rw[mult_zero_r]
  | succ n ih =>
    calc m.succ * n.succ
    _ = m.succ * n + m.succ := by rfl
    _ = (m * n + n) + (m.succ) := by rw [ih]
    _ = (m * n) + (n + (m.succ)) := by rw [add_assoc]
    _ = m * n + (m.succ + n) := by rw [add_comm n m.succ]
    _ = m * n + (succ (m + n)) := by rw[add_succ_lem]
    _ = m * n + (m + succ n) := by rfl
    _ = (m * n + m) + succ n := by rw[←add_assoc]
    _ = m * n.succ + n.succ := by rfl

theorem mult_comm :  ∀ m n : Nat , m * n = n * m := by
  intro m n
  induction n with
  | zero =>
    calc m * 0 = 0 := by rw [mult_zero_r]
    _ = 0 * m := by rw [mult_zero_l]
  | succ n ih =>
    calc m * n.succ = m * n + m := by rfl
    _ = n * m + m := by rw [ih]
    _ = n.succ * m := by rw [←succ_mult]

/- --- Do not add/change anything below this line --- -/
end mult_monoid
