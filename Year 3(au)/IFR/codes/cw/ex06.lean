/-
COMP2065-IFR Exercise 06 (100)
(Less or equal (≤))

Exercise 06

The goal is to prove some properties of ≤ on the natural numbers:

6a) ≤ is antisymmetric (50%)
6b) ≤ is decidable (50%)

-/

namespace ex06

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

-- from the lecture : definition of ≤ .
def LE : Nat → Nat → Prop
| m , n => ∃ k : Nat , k + m = n

infix:50 (priority := 1001) " ≤ " => LE
/-
If you get an error update your lean or use:
local notation x ≤ y := le x y
-/

-- end of lecture material

/- --- Do not add/change anything above this line --- -/


/- 6a) Prove that ≤ is antisymmetric. (50%)
  Hint: it may be a good idea to prove some lemmas.-/

-- theorem anti_sym_LE : ∀ x y : Nat , x ≤ y → y ≤ x → x = y := by

theorem add_left_cancel : ∀ a b c : Nat, a + b = a + c → b = c := by
  intro a b c h
  induction a with
  | zero =>
    have b' : 0 + b = b := by rw[add_lneutr]
    rw[b'] at h
    have c' : 0 + c = c := by rw[add_lneutr]
    rw[c'] at h
    assumption
  | succ a ih =>
      have h1 : succ a + b = succ (a + b) := by rw[add_succ_lem]
      have h2 : succ a + c = succ (a + c) := by rw[add_succ_lem]

      have h' : succ (a + b) = succ (a + c) := by
        calc succ (a + b)
        = succ a + b := by rw [← h1]
        _ = succ a + c := h
        _ = succ (a + c) := h2
      injection h' with hab

      exact ih hab

theorem anti_sym_LE : ∀ x y : Nat, x ≤ y → y ≤ x → x = y := by
  intro x y hxy hyx
  cases hxy with
  | intro k hk =>
    cases hyx with
    | intro j hj =>
      have h : x + (k + j) = x + 0 := by
        calc x + (k + j)
          = (x + k) + j := by rw [add_assoc]
          _ = y + j := by
            have kx' : k + x = x + k := by rw [add_comm]
            rw[←kx']
            rw[hk]
          _ = x := by
            have yj' : y + j = j + y := by rw [add_comm]
            rw[yj']
            assumption
          _ = x + 0 := by rfl
      have hkj : k + j = 0 := add_left_cancel x (k + j) 0 h
      cases k with
      | zero =>
        calc x = x + 0 := by rfl
          _ = y := by
            have x0 : x + 0 = 0 + x := by rw[add_comm]
            rw[x0]
            assumption
      | succ k' =>
        have k'j : succ k' + j = 0 := hkj
        have k'j' : succ (k' + j) = 0 := by
          rw [add_succ_lem] at k'j
          assumption
        cases k'j'

/-
6b) Show that ≤ is decidable, by defining a function returning
a boolean (10%).

You should define leb in such a way that you can prove
  ∀ m n : Nat, m ≤ n ↔ leb m n = tt
-/

def LE_ℕ : Nat → Nat → Bool
| 0 , _ => true
| succ _ , 0 => false
| succ m , succ n => LE_ℕ m n

/- Now, show that leb computes ≤, i.e. that
 your definition of leb satisfies its specification. (40%) -/






theorem ih_right : ∀ m n : Nat , LE_ℕ m n = true → m ≤ n := by
  intro m
  induction m with
  | zero =>
    intro n h1
    apply Exists.intro n
    rfl
  | succ m ih =>
    intro n h1
    cases n with
    | zero =>
      cases h1
    | succ n =>
      have h2 : m ≤ n := by
        apply ih
        assumption
      cases h2 with
      | intro k kmn =>
        apply Exists.intro k
        calc k + (m + 1)
          = k + m + 1 := by rw[add_assoc]
        _ = n + 1 := by rw[kmn]

theorem ih_left : ∀ m n : Nat , m ≤ n → LE_ℕ m n = true := by
  intro m
  induction m with
  | zero =>
    intro n h1
    dsimp[LE_ℕ]
  | succ m ih =>
    intro n h1
    cases n with
    | zero =>
      cases h1 with
      | intro k h2 =>
        cases h2
    | succ n =>
      change LE_ℕ m n = true
      apply ih
      cases h1 with
      | intro k h2 =>
        apply Exists.intro k
        injection h2

theorem dec_LE_ℕ :∀ m n : Nat, m ≤ n ↔ LE_ℕ m n = true := by
  intro m n
  constructor
  . apply ih_left
  . apply ih_right

/- --- Do not add/change anything below this line --- -/
end ex06
