/-
  Mock class test.
  Date: 03 December 2025

  **By taking this mock test, you agree that this material is not to be printed in it's completed form and/or used during the class test**

  The real class test contains 10 questions and you will have 50 minutes to complete
  as many as you can. This mock test contains 9 questions as there are a few
  more difficult questions in this practice.

  This mock test is designed to be of approximately the same length as the real class test but
  does not necessarily reflect the number of questions of each topic.

  This mock is designed by Warren Jackson.
-/

set_option linter.all false

namespace mock

open Classical -- this gives you the excluded middle `em`

variable (P Q R : Prop)
variable {A : Type}
variable (PP QQ : A → Prop)

open List
open Nat

def append : List A → List A → List A
| [], xs => xs
| (x::xs), ys => x :: (append xs ys)

infixr:65(priority := 1001) " ++ " => append

def len : List Nat → Nat
| [] => 0
| a::as => 1 + len as

#eval len [1,2,3,4,5]

def rev : List Nat → List Nat
| [] => []
| a::as => rev as ++ [a]

#eval rev [1,2,3,4,5]

def max : Nat → Nat → Nat
| zero, n => n
| (succ m), zero => succ m
| (succ m), (succ n) => succ (max m n)

/- --- Do not change or delete anything above this line --- -/

/- Propositional Logic with tactics to include:
    * `intro`
    * `exact`
    * `cases` and `cases em _`
    * `left` and `right`
    * `constructor`
    * `have`
-/

theorem ex1 : P ∧ (Q ∨ R) → (P ∨ Q) ∨ R := by
  intro h
  cases h with
  | intro l r =>
    cases r with
    | inl ll =>
      left
      left
      assumption
    | inr rr =>
      right
      assumption


theorem ex2 : ¬P ∧ ¬Q → (¬P ∨ Q) := by
  intro h
  cases h with
  | intro l r =>
    left
    assumption


theorem ex3 :  ¬P ∧ ¬Q → ¬(P ∨ Q) := by
  intro h
  cases h with
  | intro l r =>
    intro h1
    cases h1 with
    | inl ll =>
      apply l
      assumption
    | inr rr =>
      apply r
      assumption

theorem ex4 : (P ↔ Q) ∨ (P ∨ Q) := by
  cases em P with
  | inl p =>
    cases em Q with
    | inl q =>
      right
      right
      exact q
    | inr nq =>
      right
      left
      exact p
  | inr np =>
    cases em Q with
    | inl q =>
      right
      right
      exact q
    | inr nq =>
      left
      constructor
      . intro p
        have f : False := by
          apply np
          exact p
        cases f
      . intro q
        have f : False := by
          apply nq
          exact q
        cases f


/- Predicate Logic with tactics to include all of the above as well as:
    * `rw` or `rewrite`
    * `apply`
    * `apply Exists.intro _` **but not `exists _`**
    * `rfl`
-/

theorem ex5 : (∃ x : A, True) → (∀ x : A, PP x) → ∃ x : A, PP x := by
  intro h1 h2
  cases h1 with
  | intro x t =>
    exists x
    exact h2 x

theorem ex6 : (∀ x : A, PP x) → (∀ x : A, QQ x) → ∀ x : A, PP x ↔ QQ x := by
  intro h1 h2
  intro x
  constructor
  . intro ppx
    exact h2 x
  . intro qqx
    exact h1 x

/- Booleans with tactics to include all of the above.
-/

theorem ex7 : ∀ a : Bool, ∃ b : Bool, (a == b) || !(b == a) := by
  intro a
  apply Exists.intro true
  cases a with
  | false =>
    rfl
  | true =>
    rfl

/- Natural numbers with tactics to include all of the above as well as:
    * `induction`
    * `simp only [_]` **but not `simp`, `simp [_]` or `dsimp [_]`**
    * `calc`
-/
theorem maxn0 : ∀ n : Nat , max n 0 = n := by
  intro n
  induction n with
  | zero =>
    rfl
  | succ n ih =>
    rw[max]

theorem ex8 : ∀ m n : Nat, max m n = max n m := by
  intro m
  induction m with
  | zero =>
    intro n
    calc max 0 n
      = n := by rfl
    _ = max n 0 := by rw[maxn0]
  | succ m ih =>
    intro n
    induction n with
    | zero =>
      rfl
    | succ n ih' =>
      rw[max]
      rw[ih]
      rfl


/- Lists with tactics to include all of the above.
-/
theorem add0n : ∀ n : Nat , 0 + n = n := by
  intro n
  induction n with
  | zero =>
    rfl
  | succ n ih =>
    calc 0 + (n + 1)
      = 0 + n + 1 := by rfl
    _ = n + 1 := by rw[ih]

theorem add_succ : ∀ m n : Nat , succ m + n = succ (m + n) := by
  intro m n
  induction n with
  | zero =>
    rfl
  | succ n ih =>
    calc m.succ + n.succ
      = succ (m.succ + n) := by rfl
    _ = succ (succ (m + n)) := by rw[ih]
    _ = (m + (n + 1)).succ := by rfl

theorem add_comm : ∀ m n : Nat , m + n = n + m := by
  intro m n
  induction n with
  | zero =>
    calc m + 0
      = m := by rfl
    _ = 0 + m := by rw[add0n]
  | succ n ih =>
    calc m + (n + 1)
      = succ (m + n) := by rfl
    _ = succ (n + m) := by rw[ih]
    _ = succ n + m := by rw[add_succ]
    _ = n + 1 + m := by rfl

theorem add_assoc : ∀ l m n : Nat , (l + m) + n = l + (m + n) := by
  intro l m n
  induction n with
  | zero =>
    rfl
  | succ n ih =>
    calc l + m + (n + 1)
      = l + m + n.succ := by rfl
    _ = succ (l + m + n) := by rfl
    _ = succ (l + (m + n)) := by rw[ih]
    _ = l + succ (m + n) := by rfl
    _ = l + (m + n.succ) := by rfl


theorem len_append : ∀ xs ys : List Nat,
  len (xs ++ ys) = len xs + len ys := by
  intro xs ys
  induction xs with
  | nil =>
    simp only [len]
    simp only [append]
    rw[add0n]
  | cons x xs ih =>
    calc len (x :: xs ++ ys)
      = 1 + len (xs ++ ys) := by rfl
    _ = 1 + (len xs + len ys) := by rw[ih]
    _ = 1 + len xs + len ys := by rw[add_assoc]
    _ = len (x :: xs) + len ys := by rfl

theorem ex9 : ∀ ms : List Nat, len ms = len (rev ms) := by
  intro ms
  induction ms with
  | nil =>
    rfl
  | cons m ms ih =>
    simp only[len]
    simp only[rev]
    simp only[ih]
    simp only[len_append]
    simp only[add_comm]
    rfl



end mock
