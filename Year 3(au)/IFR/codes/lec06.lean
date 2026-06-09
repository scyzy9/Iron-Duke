/-

Lecture 06 : Predicate logic

-/

/-
predicate logic =

propositional logic
+ types (or sets)
+ functions
+ predicates and relations
+ quantifiers : ∀ (\forall) ∃ (\exists)


-/

variable (P Q R : Prop)

notation "ℕ" => Nat

#check Nat
#check ℕ -- \bn
#check Bool
#check Prop
#check List ℕ

variable (A B C : Type)

#check ℕ → ℕ

def f : ℕ → ℕ
| n => n+n

#eval f 3

def g : ℕ → ℕ → ℕ
| m , n => 2*m+n

#eval g 2 3
#check And -- Prop → Prop → Prop

-- isPrime : ℕ → Prop
-- isPrime 3 : "3 is prime number"
-- isPrime 4

-- le : ℕ → ℕ → Prop
-- le 2 3 : 2 is less or equal 3
-- 2 ≤ 3

variable (PP QQ : A → Prop)

-- A = Students
-- PP x = x is clever
-- P = the lecturer is happy

-- all students are clever
#check ∀ x : A, PP x
-- there is a clever student
#check ∃ x : A, PP x

#check ∀ x : A , (PP x ∧ P)
#check (∀ x : A, PP x) ∧ P
-- the scope of quantifiers goes as far as possible
#check ∀ x : A , (PP x ∧ QQ x)
--#check (∀ x : A, PP x) ∧ (QQ x)

#check ∀ x : A, PP x ∧ ∃ x : A , QQ x -- shadowing
#check ∀ x : A, PP x ∧ ∃ y : A , QQ y

-- how to prove with ∀ ?

example : (∀ x : A, PP x)
        → (∀ x : A, PP x → QQ x)
        → (∀ x : A, QQ x) := by
intro pp pq
intro a
apply pq
apply pp

-- how to prove ∀ x : A, PP x
-- intro a
-- we assume given a : A and prove PP a

-- how to use h : ∀ x : A, PP x
-- goal PP a
-- apply h, done
-- h : ∀ x : A, PP x → QQ x
-- goal QQ a
-- apply h
-- new goal PP a.

example : (∀ x : A, PP x ∧ QQ x)
       ↔ (∀ x : A, PP x) ∧ (∀ x : A, QQ x) := by
constructor
. intro pq
  constructor
  . intro a
    have apq := pq a
    cases apq with
    | intro pa qa =>
      exact pa
  · intro a
    have apq := pq a
    cases apq with
    | intro pa qa =>
      exact qa


. intro h
  cases h with
  | intro ap aq =>
       intro a
       constructor
       . exact ap a
       . exact aq a

example : (∃  x : A, PP x ∨  QQ x)
       ↔ (∃ x : A, PP x) ∨ (∃ x : A, QQ x) := by
    constructor
    · intro pq
      cases pq with
      | intro a pq =>
        cases pq with
        | inl pa =>
          left
          exact ⟨a, pa⟩
        | inr qa =>
          right
          exact ⟨a, qa⟩
    · intro pq
      cases pq with
      | inl pa =>
        cases pa with
        | intro a pa =>
          exact ⟨a, Or.inl pa⟩
      | inr qa =>
        cases qa with
        | intro a qa =>
          exact ⟨a, Or.inr qa⟩
