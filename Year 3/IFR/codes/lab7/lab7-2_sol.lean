/- COMP2065 (IFR) - Tutorial 7 -/

namespace tutorial7

set_option pp.fieldNotation false

/- Ordering -/

inductive ℕ : Type
| zero : ℕ
| succ : ℕ → ℕ
open ℕ

def add : ℕ → ℕ → ℕ
| m , zero => m
| m , succ n => succ (add m n)

def LE : ℕ → ℕ → Prop
| m , n => ∃ k : ℕ , add k m = n

/- Maybe you want to use these lemmas -/
axiom add_zero : ∀ n : ℕ, add zero n = n
axiom add_succ : ∀ m n : ℕ , add (succ m) n = succ (add m n)
axiom add_assoc : ∀ k m n : ℕ, add (add k m) n = add k (add m n)

/- ex0 : LE is reflexive -/
theorem le_refl : ∀ n : ℕ, LE n n := by
  intro n
  apply Exists.intro zero
  calc
    add zero n
    _ = n := by rw [add_zero]

/- ex1 : LE is transitive -/
theorem le_trans : ∀ k m n : ℕ, LE k m → LE m n → LE k n := by
  intro k m n le_k_m le_m_n
  cases le_k_m with
  | intro l add_l_k_eq_m =>
    cases le_m_n with
    | intro r add_r_m_eq_n =>
      apply Exists.intro (add r l)
      calc
        add (add r l) k
        _ = add r (add l k) := by rw [add_assoc]
        _ = add r m := by rw [add_l_k_eq_m]
        _ = n := by rw [add_r_m_eq_n]

/- ex2 : prove this lemma -/
theorem le_zero : ∀ n : ℕ, LE zero n := by
  intro n
  apply Exists.intro n
  calc
    add n zero
    _ = n := by rfl

/- ex3 : prove this lemma -/
theorem le_succ : ∀ m n : ℕ, LE m n → LE (succ m) (succ n) := by
  intro m n le_m_n
  cases le_m_n with
  | intro k add_k_m_eq_n =>
    apply Exists.intro k
    calc
      add k (succ m)
      _ = succ (add k m) := by rfl
      _ = succ n := by rw [add_k_m_eq_n]


/- Decidaibility -/

def eq_ℕ : ℕ → ℕ → Bool
| zero , zero => true
| zero , succ _ => false
| succ _ , zero => false
| succ m , succ n => eq_ℕ m n

theorem refl_eq_ℕ : ∀ n : ℕ, eq_ℕ n n = true := by
  intro n
  induction n with
  | zero =>
    rfl
  | succ n ih =>
    calc eq_ℕ (succ n) (succ n)
    _ = eq_ℕ n n := by rfl
    _ = true := by rw [ih]

theorem equal2eq : ∀ m n : ℕ, m = n → eq_ℕ m n = true := by
  intro m n mn
  calc eq_ℕ m n
  _ = eq_ℕ m m := by rw [mn]
  _ = true := by rw [refl_eq_ℕ]

theorem eq2equal : ∀ m n : ℕ, eq_ℕ m n = true → m = n := by
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
          calc
            eq_ℕ m' n'
            _ = eq_ℕ (succ m') (succ n') := by rfl
            _ = true := by rw [mn]
        rw [h]

/- ex4 : prove the injectivity of succ without using 'injection' and 'change' -/
theorem succ_inj : ∀ m n, succ m = succ n → m = n := by
  intro m n h
  have eq_succ_m_succ_n : eq_ℕ (succ m) (succ n) = true := by
    apply equal2eq
    assumption
  have eq_m_n : eq_ℕ m n = true := by
    calc
      eq_ℕ m n
      _ = eq_ℕ (succ m) (succ n) := by rfl
      _ = true := by rw [eq_succ_m_succ_n]
  apply eq2equal
  assumption

/- ex5 : define a function that decides inequalities of ℕ -/
def ineq : ℕ → ℕ → Bool
| zero , zero => false
| zero , succ _ => true
| succ _ , zero => true
| succ m , succ n => ineq m n

/- ex6 : inequality is irefexive -/
theorem ineq_irefl : ∀ m : ℕ, ineq m m = false := by
  intro m
  induction m with
  | zero =>
    calc
      ineq zero zero
      _ = false := by rfl
  | succ m ih =>
    calc
      ineq (succ m) (succ m)
      _ = ineq m m := by rfl
      _ = false := by rw [ih]

/- ex7 : prove the soundness of inequality -/
theorem ineq_sound : ∀ m n, ineq m n = true → m ≠ n := by
  intro m
  induction m with
  | zero =>
    intro n ineq_zero_n
    cases n with
    | zero =>
      cases ineq_zero_n
    | succ n =>
      intro zero_eq_succ_n
      dsimp[ineq] at ineq_zero_n
      cases zero_eq_succ_n
  | succ m ih =>
    intro n ineq_succ_m_n
    cases n with
    | zero =>
      intro succ_m_eq_zero
      cases succ_m_eq_zero
    | succ n =>
      have m_not_eq_n : m ≠ n := by
        apply ih
        calc
          ineq m n
          _ = ineq (succ m) (succ n) := by rfl
          _ = true := by rw [ineq_succ_m_n]
      intro succ_m_eq_succ_n
      apply m_not_eq_n
      apply succ_inj
      assumption

/- ex8 : prove the completeness of inequality -/
theorem ineq_complete : ∀ m n, m ≠ n → ineq m n = true := by
  intro m
  induction m with
  | zero =>
    intro n
    intro h1
    cases n with
    | zero =>
      have f : False := by
        apply h1
        rfl
      cases f
    | succ n =>
      calc ineq zero (succ n)
        _ = true := by rfl
  | succ m ih =>
    intro n succ_m_not_eq_n
    cases n with
    | zero =>
      calc ineq (succ m) zero
        _ = true := by rfl
    | succ n =>
      have m_not_eq_n : m ≠ n := by
        intro m_eq_n
        apply succ_m_not_eq_n
        rw [m_eq_n]
      have ineq_m_n : ineq m n = true := by
        apply ih
        assumption
      calc
        ineq (succ m) (succ n)
        _ = ineq m n := by rfl
        _ = true := by rw [ineq_m_n]

theorem ineq_complete_alt : ∀ m n, m ≠ n → ineq m n = true := by
  intro m
  induction m with
  | zero =>
    intro n
    intro h1
    induction n with
    | zero =>
      dsimp[ineq]
      have f : False := by
        apply h1
        rfl
      cases f
    | succ n ih =>
      dsimp[ineq]
  | succ m ih =>
    intro n
    intro h1
    induction n with
    | zero =>
      rw[ineq]
    | succ n ih' =>
      dsimp [ineq]
      apply ih
      intro hmn
      apply h1
      rw[hmn]
