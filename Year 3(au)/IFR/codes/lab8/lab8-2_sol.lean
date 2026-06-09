
/-
Introduction to Formal Reasoning (Comp 2065)
Tutorial 08: Lists
Date: 27 Nov 2025
TA: Aref Mohammadzadeh
You can download tutorial files from moodle `Tutorials -> Aref`.
-/


namespace tutorial08

abbrev ℕ := Nat
open Nat
open List

-- Disable some automatic features to force manual proof steps
set_option tactic.customEliminators false
set_option pp.fieldNotation false

variable {A : Type}

/- **-----------------------------------------------------** -/
/- ------------------ Part 1: Definitions ---------------- -/
/- **-----------------------------------------------------** -/

-- 1. Append (++)
def append : List A → List A → List A
| [],    bs => bs
| a::as, bs => a :: (append as bs)

infixr:65 (priority := 1001) " ++ " => append

-- 2. Snoc (Append to end)
def snoc : List A → A → List A
| [],    a => [a]
| x::xs, a => x :: (snoc xs a)

-- 3. Naive Reverse
def rev : List A → List A
| []    => []
| a::as => snoc (rev as) a

-- 4. Fast Reverse

def revaux : List A → List A → List A
| [], bs => bs
| (a :: as), bs => revaux as (a :: bs)

def fastrev (l : List A) : List A
  := revaux l []

--------------
-- (Assumed from Lectures:)

theorem app_assoc : ∀ as bs cs : List A, (as ++ bs) ++ cs = as ++ (bs ++ cs) := by
  intro as bs cs
  induction as with
  | nil => rfl
  | cons a as ih => simp [append, ih]

theorem app_nil_r : ∀ as : List A, as ++ [] = as := by
  intro as
  induction as with
  | nil => rfl
  | cons a as ih => simp [append, ih]


-- EXERCISE 1: Definition
-- Define duplicate. duplicate replicates each item in a list twice
-- #eval duplicate [1,2,3] should give [1,1,2,2,3,3]
def duplicate : List A → List A
| [] => []
| a :: as => a :: a :: duplicate as


#eval duplicate [1,2,3] -- Test your definition here


/- **-----------------------------------------------------** -/
/- ------------------ Part 2: Warm-up -------------------- -/
/- **-----------------------------------------------------** -/

-- Let's inspect how these functions behave using #reduce
-- append:
#reduce append [1] [2,3]
#reduce [1] ++ [2,3]
#reduce [[1]] ++ [[2], [3]] ++ [[4]]

-- snoc:
#reduce snoc [3,2] 1
#reduce snoc [[3,5,2]] (snoc [1] 4)

-- rev sample
#reduce rev [1,2,3]


-- Exercise 2: Do we need Induction on `as` in these examples?
example : ∀ as : List A, ∀ a : A, a :: as = [] ++ a :: as := by
  intro as a
  rfl

example : ∀ as : List A, ∀ a : A, a :: as = a :: ([] ++ as) := by
  intro as a
  rfl

example : ∀ as : List A, ∀ a : A, a :: as = (a :: []) ++ as := by
  intro as a
  rfl

example : ∀ as : List A, ∀ a : A, a :: as = a :: as ++ [] := by
  intro as a
  simp only [app_nil_r]



/- **-----------------------------------------------------** -/
/- --------- Part 3: Snoc and Reverse  ----------- -/
/- **-----------------------------------------------------** -/

-- To understand `rev`, we must understand `snoc`, because `rev` is defined using `snoc`.

-- EXERCISE 3: Relating snoc to append
theorem snoc_eq_append : ∀ as : List A, ∀ x : A, snoc as x = as ++ [x] := by
  intro as x
  induction as with
  | nil =>  rfl
  | cons a as ih =>
    simp only [append , snoc]
    rw [ih]


-- EXERCISE 4: Reverse of Singleton
theorem rev_singleton : ∀ a : A, rev [a] = [a] := by
  intro a
  simp only [rev]
  rfl

-- EXERCISE 5: Distributivity of Reverse
-- How does reverse interact with append?
-- You will likely need `app_assoc` and `snoc_eq_append`.
theorem rev_append : ∀ as bs : List A, rev (as ++ bs) = rev bs ++ rev as := by
  intro as bs
  induction as with
  | nil =>  simp only [append , rev, app_nil_r]
  | cons a as ih =>  simp only [rev , append , snoc_eq_append ,ih, app_assoc]

-- EXERCISE 6:
-- Proving that reversing a list twice gives back the original list.
-- You will need the `rev_append` lemma you just proved.
theorem rev_rev : ∀ as : List A, rev (rev as) = as := by
  intro as
  induction as with
  | nil =>  rfl
  | cons a as ih =>
       simp only [rev]
       rw [snoc_eq_append]
       rw [rev_append]
       rw [rev_singleton]
       rw [ih]
       simp only [append]

end tutorial08
