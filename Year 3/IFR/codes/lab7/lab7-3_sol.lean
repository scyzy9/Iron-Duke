/-
Introduction to Formal Reasoning (Comp 2065)
Tutorial 07: The Natural Numbers II (order and decidability)
Date: 20 Nov 2025
TA: Aref Mohammadzadeh
You can download tutorial files from moodle `Tutorials -> Aref`.
-/


/- ## Part1 : Order on Natural Numbers:-/

namespace tutorial07
abbrev ℕ := Nat
open Nat

def LE : ℕ → ℕ → Prop
| m , n => ∃ k : ℕ , k + m = n

infix:50 (priority := 1001) " ≤ " => LE

/- Lemmas for this tutorial: -/
axiom add_zero : ∀ n : ℕ, zero + n = n
axiom add_succ : ∀ m n : ℕ , succ m + n = succ ( m + n)
axiom add_assoc : ∀ k m n : ℕ, (k + m) + n = k + (m + n)
axiom bad_eq : ∀ k n,  k + (succ n) = n → False
axiom succ_inj : ∀ m n, succ m = succ n → m = n

-----------------------

theorem ex01 : ∀ n : ℕ, n ≤ n := by
  intro n
  apply Exists.intro zero
  rw [add_zero]

theorem ex02 : ∀ n : ℕ, zero ≤ n := by
  intro n
  apply Exists.intro n
  rfl

theorem ex03 : ¬ ∃ n : ℕ, ∀ m : ℕ, m ≤ n := by
  intro pn₀
  cases pn₀ with
  | intro n₀ hn₀ =>
    have false : succ n₀ ≤ n₀ := by apply hn₀
    cases false with
    | intro k kfalse =>
      apply bad_eq  k n₀
      exact kfalse


theorem ex04 : ∀ m n : ℕ, m ≤ n → m ≤ (succ n) := by
  intro m n mn
  cases mn with
  | intro k kmn =>
    apply Exists.intro (succ k)
    calc
      succ k + m
      _ = succ (k + m) := by rw [add_succ]
      _ = succ n := by rw [kmn]


/- ## Part2: Decidaibility -/
-- Let's first review the decidability of equality in ℕ:

def eq_ℕ : ℕ → ℕ → Bool
| zero , zero => true
| zero , succ _ => false
| succ _ , zero => false
| succ m , succ n => eq_ℕ m n

theorem refl_eq_ℕ : ∀ n : ℕ, eq_ℕ n n = true := by
intro n
induction n with
| zero => rfl
| succ n ih => calc
    eq_ℕ (succ n) (succ n)
    _ = eq_ℕ n n := by rfl
    _ = true := by rw [ih]

theorem equal_to_eq : ∀ m n : ℕ, m = n → eq_ℕ m n = true := by
intro m n mn
calc
  eq_ℕ m n
  _ = eq_ℕ m m := by rw [mn]
  _ = true := by rw [refl_eq_ℕ]



theorem eq_to_equal : ∀ m n : ℕ, eq_ℕ m n = true → m = n := by
intro m
induction m with
| zero =>
    intro n mn
    cases n with
    | zero => rfl
    | succ n' => cases mn
| succ m' ih =>
    intro n mn
    cases n with
    | zero => cases mn
    | succ n' =>
        have h : m' = n' := by
          apply ih
          simp only [eq_ℕ] at mn
          rw [mn]
        rw [h]

-----------------


-- Now let's prove that inequaliy is decidable:

/- ex05 : First define a function that decides inequalities of m : ℕ and n : ℕ  -/
def inequ : ℕ → ℕ → Bool
| zero , zero => false
| zero , succ _ => true
| succ _ , zero => true
| succ m , succ n => inequ m n


-- Let's review the tactic `change` in the next excersice
theorem ex06_inequ_irefl : ∀ m : ℕ, inequ m m = false := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
  change  inequ m m = false -- or dsimp [inequ] , or simp only [inequ]
  exact ih



theorem ex07_inequ2neq : ∀ m n, inequ m n = true → m ≠ n := by
  intro m
  induction m with
  | zero =>
    intro n p
    cases n with
    | zero => cases p
    | succ n =>
      intro t ; cases t
  | succ m ih =>
    intro n inequ_sm_n
    cases n with
    | zero =>
      intro q ; cases q
    | succ n =>
      have m_neq_n : m ≠ n := by
        apply ih
        change inequ m.succ n.succ = true
        exact inequ_sm_n
      intro s
      apply m_neq_n
      apply succ_inj
      assumption


theorem ex08_neq2inequ : ∀ m n, m ≠ n → inequ m n = true := by
  intro m
  induction m with
  | zero =>
    intro n hn
    cases n with
    | zero =>
      have f : False := by
        apply hn
        rfl
      cases f
    | succ n => rfl
  | succ m ih =>
    intro n sm_neq_n
    cases n with
    | zero => rfl
    | succ n =>
      have mn : m ≠ n := by
        intro m_eq_n
        apply sm_neq_n
        rw [m_eq_n]
      have inequ_m_n : inequ m n = true := by
        apply ih
        assumption
      dsimp [inequ]
      assumption
