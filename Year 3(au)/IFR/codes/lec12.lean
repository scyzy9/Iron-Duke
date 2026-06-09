/-

Lecture 12 : Natural numbers

-/

-- Peano Arithmetic

-- inductive Nat : Type
-- | zero : Nat
-- | succ : Nat → Nat

-- axiom 1,2

notation "ℕ" => Nat -- \bn

open Nat

-- Axiom 3
-- no successor is equal to zero
example : ∀ n : ℕ , succ n ≠ zero := by
intro n h
cases h

-- Axiom 4
-- if succ m = succ n then m = n

def prd : ℕ → ℕ
| zero => zero
| succ n => n

#eval prd 7

example : ∀ m n : ℕ, succ m = succ n → m = n := by
  intro m n h
  change prd (m.succ) = n
  rw [h]
  rfl

example : ∀ m n : ℕ, succ m = succ n → m = n := by
intro m n h
injection h

-- Axiom 5
-- induction : any property which holds for 0
-- and if it holds for n then aso for succ n
-- holds for all natural numbers

variable (PP : ℕ → Prop)

theorem ind : (PP zero)
  → (∀ n : ℕ, PP n → PP (succ n))
  → ∀ n : ℕ, PP n := by
intro pz ps n
induction n with
| zero =>
    assumption
| succ m ih =>
    apply ps
    assumption

-- +

-- add 3 : ℕ → ℕ
-- add 3 4

def add : ℕ → ℕ → ℕ
| m , zero => m
| m , (succ n) => succ (add m n)

-- 3 + 4 =
-- 3 + (succ 3) =
-- succ (3 + 3) = succ 6 = 7

#eval (add 3 4)
/-
add 3 4
= succ (add 3 3)
= ...
= succ (succ (succ (succ 3)))
= 7
-/

-- m + n = add m n
#eval (3 + 4)

def mult : ℕ → ℕ → ℕ
| _ , zero => zero
| m , (succ n) => mult m n + m
/-
3 * 4
= 3 * (succ 3)
= 3 * 3 + 3
= (9 + 3)
= 12
-/
#eval (mult 3 4)

#eval (3 * 4)

/-
3 * 4
= 3 + 3 + 3 + 3 + 0
-/

def exp : ℕ → ℕ → ℕ
| _ , zero => 1
| m , (succ n) => exp m n * m

#eval exp 3 4
#eval 3 ^ 4

/-
3 ^ 4
= 3 * 3 * 3 * 3 * 1
= 81

3 ^ 4
= 3 ^ (succ 3)
= 3 ^ 3 * 3
= 27 * 3
= 81
-/

/-
Ackermann, Hilbert's student
Ackermann's function

ack : ℕ → ℕ → ℕ → ℕ
ack 0 m n = m + n
ack 1 m n = m * n
ack 2 m n = m ^ n
...
(ℕ → ℕ) → ℕ higher order functions
System T (Goedel)
In Lean we can define ack using higher order functions
-/

/-
Peano added + and *
Goedel showed this is enough
what if only have +
Presburger Arithmetic (is complete)
-/

-- prove properties of addition (algebra)
-- ∀ l m n : ℕ, (l + m) + n = l + (m + n)
-- ∀ m n : ℕ , m + n = n + m
-- monoid (associative,left neutr, right neutr)
-- commutative monoid

-- what is an example of a non commutative monoid ?

-- def add : ℕ → ℕ → ℕ
-- | m , zero => m
-- | m , (succ n) => succ (add m n)

theorem add_rneutr : ∀ n : ℕ, n + 0 = n := by
intro n
rfl -- reflexivity, by definition

-- m + 1 = m + (succ zero) = succ (m + 0) = succ m
-- succ m = m.succ

theorem add_lneutr : ∀ n : ℕ, 0 + n = n := by
intro n
induction n with
| zero => rfl
| succ m ih =>
    calc (0 + succ m)
      = succ (0 + m) := by rfl
      _ = succ m := by rw [ih]

theorem add_assoc : ∀ l m n : ℕ, (l + m) + n = l + (m + n) := by
  intro l m n
  induction n with
  | zero =>
    rfl
  | succ n ih =>
    rw [Nat.add_succ]
    rw [Nat.add_succ]
    rw [Nat.add_succ]
    rw [ih]

theorem add_assoc_alt : ∀ l m n : ℕ, (l + m) + n = l + (m + n) := by
  intro l m n
  induction n with
  | zero =>
    rfl
  | succ n ih =>
    have h1 : (l + m) + succ n = succ ((l + m) + n) := rfl
    have h2 : m + succ n = succ (m + n) := rfl
    have h3 : l + succ (m + n) = succ (l + (m + n)) := rfl
    rw [h1]
    rw [ih]
    rw [← h3]
    rw [← h2]

theorem add_assoc_n : ∀ l m n : ℕ, (l + m) + n = l + (m + n) := by
  intro l m n
  induction n with
  | zero =>
    calc (l + m) + 0
    =    l + m := by rfl
    _ =  l + (m + 0) := by rfl
  | succ n ih =>
    calc (l + m) + (succ n)
      = succ ((l + m) + n) := by rfl
    _ = succ (l + (m + n)) := by rw [ih]
    _ = l + (succ (m + n)) := by rfl
    _ = l + (m + (succ n)) := by rfl


-- (ℕ , 0 , +) are commutative monoid
-- (ℕ , 1 , *) are commutative monoid
-- (Matr, I , *) is a monoid
-- (ℕ → ℕ , id , ∘) is a monoid
-- (A → B ???) is a category

--(l + m) * n = l * n + m * n
--n * (l + m) = n * l + n * m

theorem addsucc : ∀ l m : ℕ , (succ l) + m = succ (l + m) := by
  intro l m
  induction m with
  | zero =>
    rfl
  | succ m ih =>
    calc l.succ + m.succ
      = succ (succ l + m) := by rfl
    _ = succ (succ (l + m)) := by rw[ih]
    _ = succ (l + succ m) := by rfl


theorem add_comm : ∀ l m : ℕ , l + m = m + l := by
  intro l m
  induction m with
  | zero =>
    calc l + 0 =
         l := by rfl
         _ = 0 + l := by rw [add_lneutr]
  | succ m ih =>
    calc l + (succ m)
      = succ (l + m) := by rfl
    _ = succ (m + l) := by rw[ih]
    _ = (succ m) + l := by rw[←addsucc]

theorem add_succ : ∀ n m : ℕ , n + succ m = succ (n + m) := by
  intro n m
  induction n with
  | zero =>
    rfl
  | succ n ih =>
    calc succ n + succ m
      = succ (succ n + m) := rfl
