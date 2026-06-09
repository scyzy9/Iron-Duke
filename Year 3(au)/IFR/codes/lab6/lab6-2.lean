/- COMP2065 (IFR) - Tutorial 6 -/

namespace tutorial6

set_option pp.fieldNotation false

/- Natural numbers -/

inductive ℕ : Type
| zero : ℕ
| succ : ℕ → ℕ
open ℕ

/- 0 : zero -/
/- 1 : succ zero -/
/- 2 : succ (succ zero) -/
/- ... -/

/- Functions are defined by induction -/

def double : ℕ → ℕ
| zero => zero
| succ n => succ (succ (double n))

def add : ℕ → ℕ → ℕ
| m , zero => m
| m , succ n => succ (add m n)

/- Reasoning about computations (without dsimp) -/

theorem add_runit : ∀ n : ℕ, add n zero = n := by
  intro n
  calc
    add n zero
    _ = n := by rfl

theorem add_lunit : ∀ n : ℕ, add zero n = n := by
  intro n
  induction n with
  | zero =>
    calc
      add zero zero
      _ = zero := by rfl
  | succ n ih =>
    calc
      add zero (succ n)
      _ = succ (add zero n) := by rfl
      _ = succ n := by rw [ih]

/- ex0: prove this lemma -/
theorem add_succ_is_succ_add : ∀ m n : ℕ , add (succ m) n = succ (add m n) := by
  intro m n
  induction n with
  | zero =>
    dsimp [add]
  | succ n ih =>
    dsimp [add]
    rw[ih]

theorem add_succ_is_succ_add_alt : ∀ m n : ℕ , add (succ m) n = succ (add m n) := by
  intro m n
  induction n with
  | zero =>
    rfl
  | succ n ih =>
    calc add m.succ n.succ
    = succ (add m.succ n) := by rfl
    _ = succ (succ (add m n)) := by rw[ih]


/- ex1: define addition by induction over the first variable -/
def add' : ℕ → ℕ → ℕ
| zero , n => n
| succ m , n => succ (add' m n)

/- ex2: prove two definitions of additions are equivalent -/
theorem add_is_add' : ∀ m n : ℕ, add m n = add' m n := by
  intro m n
  induction m with
  | zero =>
    calc add zero n
    = n := by rw[add_lunit]
  | succ m ih =>
    calc add m.succ n
    = succ (add m n) := by rw[add_succ_is_succ_add]
    _ = succ (add' m n) := by rw[ih]


/- ex3: prove this lemma -/
theorem double_is_add : ∀ n : ℕ, double n = add n n := by
  intro n
  induction n with
  | zero =>
    rfl
  | succ n ih =>
    calc double (succ n)
    = succ (succ (double n)) := by rfl
    _ = succ (succ (add n n)) := by rw[ih]
    _ = succ (add n.succ n) := by rw[add_succ_is_succ_add]


def isEven : ℕ → Prop
| zero => True
| succ zero => False
| succ (succ n) => isEven n

/- ex4: prove this lemma -/
theorem double_is_even : ∀ n : ℕ, isEven (double n) := by
  intro n
  induction n with
  | zero =>
    dsimp [double,isEven]
  | succ n ih =>
    change isEven (succ (succ (double n)))
    change isEven (double n)
    assumption

/- Integer -/

inductive ℤ : Type
| nat : ℕ → ℤ  /- 0, 1, 2, 3, ... -/
| neg : ℕ → ℤ  /- -1, -2, -3, ...-/
open ℤ

/- ex5: define double for ℤ -/
def doubleℤ : ℤ → ℤ
| ℤ.nat n => ℤ.nat (double n)
| ℤ.neg n => ℤ.neg (double n)

/- ex6: define succesor for ℤ -/
def succℤ : ℤ → ℤ := by sorry

/- ex7: prove this lemma -/
theorem double_succ_is_succ_succ_double : ∀ z : ℤ, doubleℤ (succℤ z) = succℤ (succℤ (doubleℤ z)) := by
  sorry
