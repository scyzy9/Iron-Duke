/- COMP2065 (IFR) - Tutorial 9 -/

namespace tutorial9

open Classical
open Nat
abbrev ℕ := Nat
open List
set_option pp.fieldNotation false

variable {P Q R : Prop}
variable {A B : Type}
variable {PP QQ : A → Prop}
variable {m n : ℕ}

/- Part1 : CheckList -/

/- (Constructive) Propositional Logic -/

/- Classical Logic -/

/- Predicate Logic -/

/- Equality -/

/- Boolean -/

/- Natural Number -/

/- Decidability -/

/- List -/

/- Part2 : Some exercises -/

example : (P → Q) → ¬ P ∨ Q := by
  intro h
  cases em P with
  | inl p =>
    cases em Q with
    | inl q =>
      right
      exact q
    | inr nq =>
      have f : False := by
        have q : Q := by
          exact h p
        apply nq
        exact q
      cases f
  | inr np =>
    left
    exact np



example : ¬ ¬ (¬ ¬ P → P) := by
  intro h
  apply h
  intro h1
  cases em P with
  | inl p =>
    exact p
  | inr np =>
    have f : False := by
      apply h1
      exact np
    cases f

example : (∃ x : A, True) → ∃ x, PP x → ∀ y, PP y := by
  intro h
  cases h with
  | intro x t =>
    apply Exists.intro x
    intro h1
    intro y
    sorry

/- Define 'Greater or Equal' -/
def GE : ℕ → ℕ → Prop
| _ , 0 => True
| 0 , _ => False
| succ m , succ n => GE m n

/- Define a function that decides 'GE' -/
def ge : ℕ → ℕ → Bool
| _, 0 => true
| 0, _ => false
| succ m, succ n => ge m n

/- Show 'ge' actually decides 'GE' -/

/- Define 'double' -/
def double : ℕ → ℕ
| 0 => 0
| succ n => succ (succ (double n))

/- Define 'half' that rounds the result to floor -/
def half : ℕ → ℕ
| 0 => 0
| 1 => 0
| succ (succ n) => succ (half n)

example : ∀ n, GE n (double (half n)) := by
  intro k
  induction k with
  | zero =>
    dsimp[GE]
    dsimp[half]
    dsimp[double]
    rw[GE]
    constructor
  | succ k ih =>
    cases k with
    | zero =>
      dsimp[GE,double,half]
    | succ k =>
      dsimp[GE,double,half]
      sorry



def map (f : A → B) : List A → List B
| nil => nil
| cons a as => f a :: map f as

def len : List A → ℕ
| nil => zero
| cons _ as => succ (len as)

/- Define sum over a list of ℕ -/
def sum : List ℕ → ℕ
| [] => 0
| a :: as => a + sum as

  theorem add_assoc : ∀ l m n : ℕ, (l + m) + n = l + (m + n) := by
    intro l m n
    induction n with
    | zero =>
      rfl
    | succ x ih =>
      change succ (l + m + x) = succ (l + (m + x))
      rw [ih]

theorem add_succ : ∀ m n : ℕ, (succ m) + n = succ (m + n) := by
  intro m n
  induction n with
  | zero =>
    rfl
  | succ n' ih =>
    change (succ m + n') + 1 = succ ((m + n') + 1)
    rewrite [ih]
    rfl

theorem add_lneutr : ∀ n : ℕ, 0 + n = n := by
 intro n
 induction n with
 | zero =>
    rfl
  | succ n' ih =>
    calc 0 + (n' + 1) = (0 + n') + 1 := by rfl
    _ = n' + 1 := by rw[ih]

theorem add_comm : ∀ m n : ℕ , m + n = n + m := by
  intro m n
  induction n with
  | zero =>
    rewrite [add_lneutr]
    rfl
  | succ n' ih =>
    rewrite [add_succ]
    rewrite [← ih]; simp; rfl

example : ∀ ns : List ℕ, sum (map succ ns) = len ns + sum ns := by
  intro ns
  induction ns with
  | nil =>
    rfl
  | cons k ks ih =>
    simp only[sum,map,len]
    calc succ k + sum (map succ ks)
      = succ k + (len ks + sum ks) := by rw[ih]
    _ = succ k + len ks + sum ks := by rw[add_assoc]
    _ = succ (k + len ks) + sum ks := by rw[add_succ]
    _ = succ (len ks + k) + sum ks := by rw[add_comm (len ks) k]
    _ = succ (len ks) + k + sum ks := by rw[←add_succ]
    _ = succ (len ks) + (k + sum ks) := by rw[add_assoc]
