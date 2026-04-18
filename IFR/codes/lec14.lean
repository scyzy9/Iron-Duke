/-

Lecture 14 : Natural numbers

-/
namespace l14

set_option tactic.customEliminators false

notation "ℕ" => Nat -- \bn
open Nat

def add : ℕ → ℕ → ℕ
| m  , zero     => m
| m  , (succ n) => succ (add m n)

notation:65 (priority := 1001) m:65 "+" n:66 => add m n

-- m^m = exp m n

theorem add_rneutr : ∀ n : ℕ, n + 0 = n := by
intro n
rfl

theorem add_lneutr : ∀ n : ℕ, 0 + n = n := by
intro n
induction n with
| zero => rfl
| succ m ih =>
    calc (0 + succ m)
      = succ (0 + m) := by rfl
      _ = succ m := by rw [ih]

theorem add_assoc :
  ∀ l m n : ℕ , (l + m) + n = l + (m + n) := by
intro l m n
induction n with
| zero =>
    calc  (l + m) + 0
            = l + m := by rfl
          _ = l + (m + 0) := by rfl
| succ n ih =>
    calc (l + m) + (succ n)
        = succ ((l + m) + n) := by rfl
      _ = succ (l + (m + n)) := by rw [ih]
      _ = l + (succ (m + n)) := by rfl
      _ = l + (m + (succ n)) := by rfl

theorem addsucc : ∀ l m : ℕ,
    (succ l) + m = succ (l + m) := by
    intro l m
    induction m with
    | zero => rfl
    | succ m ih =>
        calc
          (succ l) + (succ m)
            = succ (succ l + m) := by rfl
          _ = succ (succ (l + m)) := by rw [ih]
          _ = succ (l + (succ m)) := by rfl

theorem add_comm :
∀ l m : ℕ, l + m = m + l := by
intro l m
induction m with
| zero =>
    calc l + 0
           = l := by rfl
         _ = 0 + l := by rw [add_lneutr]
| succ m ih =>
    calc l + (succ m)
         = succ (l + m) := by rfl
       _ = succ (m + l) := by rw [ih]
       _ = (succ m) + l := by rw [← addsucc]

----

example : ∀ l m n : ℕ, l + m + n = n + m + l := by
  intro l m n
  calc (l+m)+n
      = n + (l + m) := by rw [add_comm]
    _ = n + (m + l) := by simp only [add_comm]
    _ = (n+m)+l := by rw [← add_assoc]

----

-- ≤ : ℕ → ℕ → Prop
-- what kind of order ?

-- reflexive
-- ∀ l : ℕ , l ≤ l
-- transitive
-- ∀ l m n : ℕ, l ≤ m → m ≤ n → l ≤ n
-- antisymmetric
-- ∀ l m : ℕ , l ≤ m → m ≤ l → l = m
-- partial order
-- < : total order

def LE : ℕ → ℕ → Prop
| l , m => ∃ k : ℕ , k + l = m

infix:50 (priority := 1001) " ≤ " => LE

example : 1 ≤ 2 := by
  exists 1

example : ¬ (2 ≤ 1) := by
  intro h
  cases h with
  | intro k p =>
      cases p

theorem refl_LE : ∀ l : ℕ , l ≤ l := by
  intro l
  dsimp [LE]
  exists 0
  rw [add_lneutr]

theorem trans_LE :∀ l m n : ℕ, l ≤ m → m ≤ n → l ≤ n := by
  intro l m n lm mn
  cases lm with
  | intro j jlm =>
  cases mn with
  | intro k kmn =>
  exists k + j
  calc
    (k+j)+l
      = k + (j + l) := by rw [add_assoc]
    _ = k + m := by rw [jlm]
    _ = n := by assumption

theorem antisym_LE : ∀ l m : ℕ , l ≤ m → m ≤ l → l = m := by
  intro l m lm ml
  cases lm with
  | intro k klm =>
  cases ml with
  | intro j jml =>
  sorry


def LT : ℕ → ℕ → Prop
| m , n => succ m ≤ n

-- anti-reflexive
-- ∀ n : ℕ, ¬ (n < n)
-- transitive
-- ∀ l m n : ℕ, l < m → m < n → l < n
-- strongly antisymmetric
-- ∀ l m : ℕ , l < m → m < l → False
-- ∀ l m : ℕ , ¬ (l < m ∧ m < l)
-- well-founded
-- well orders

-- decidability

end l14
