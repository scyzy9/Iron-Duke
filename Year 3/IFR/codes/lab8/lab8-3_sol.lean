/- COMP2065 (IFR) - Tutorial 8 -/

namespace tutorial8

set_option pp.fieldNotation false

variable {A : Type}

inductive ℕ : Type where
| zero : ℕ
| succ : ℕ → ℕ
open ℕ

def add : ℕ → ℕ → ℕ
| m , zero => m
| m , succ n => succ (add m n)

------------------------------------------------------------
/- List -/

inductive List (A : Type) : Type where
| nil : List A
| cons : A → List A → List A
open List

def empty_list : List ℕ := nil -- []

def singleton_list : List ℕ := cons zero nil -- [0]

def one_two_tree : List ℕ := -- [1, 2, 3]
  cons (succ zero)
  (cons (succ (succ zero))
  (cons (succ (succ (succ zero)))
  nil))

def length : List A → ℕ
| nil => zero
| cons _ as => succ (length as)

def append : List A → List A → List A
| nil       , as => as
| cons a as , bs => cons a (append as bs)

def snoc : List A → A → List A
| nil , b => cons b nil
| cons a as , b => cons a (snoc as b)

def rev : List A → List A
| nil => nil
| cons a as => snoc (rev as) a

------------------------------------------------------------
/- What is a monoid? -/

/-
-- (M, ⊗, e) :
-- ∀ a : M, e ⊗ a = a = a ⊗ e
-- ∀ a b c : M, a ⊗ (b ⊗ c) = (a ⊗ b) ⊗ c
-/

/- (ℕ, add, zero) :
-- ∀ n, add zero n = n = add n zero
-- ∀ m n l, add m (add n l) = add (add m n) l
--/

/- (List A, append, nil):
-- ∀ as, append nil as = as = append as nil
-- ∀ as bs cs, append as (append bs cs) = append (append as bs) cs
-/

/- nil is left unit -/
theorem append_lneutr : ∀ as : List A, append nil as = as := by
  intro as
  calc
    append nil as
    _ = as := by rfl

/- ex0 : prove nil is right unit -/
theorem append_rneutr : ∀ as : List A, append as nil = as := by
  intro as
  induction as with
  | nil =>
    calc
      append nil nil
      _ = nil := by rfl
  | cons a as ih =>
    calc
      append (cons a as) nil
      _ = cons a (append as nil) := by rfl
      _ = cons a as := by rw [ih]

/- ex1 : prove append is associative -/
theorem append_assoc : ∀ as bs cs : List A, append as (append bs cs) = append (append as bs) cs := by
  intro as
  induction as with
  | nil =>
    intro bs cs
    calc
      append nil (append bs cs)
      _ = append bs cs := by rfl
      _ = append (append nil bs) cs := by rfl
  | cons a as ih =>
    intro bs cs
    calc
      append (cons a as) (append bs cs)
      _ = cons a (append as (append bs cs)) := by rfl
      _ = cons a (append (append as bs) cs) := by rw [ih]
      _ = append (cons a (append as bs)) cs := by rfl
      _ = append (append (cons a as) bs) cs := by rfl

/- ex2 : prove this lemma -/
theorem snoc_append : ∀ b : A, ∀ as bs : List A, snoc (append as bs) b = append as (snoc bs b) := by
  intro b as
  induction as with
  | nil =>
    intro bs
    calc
      snoc (append nil bs) b
      _ = snoc bs b := by rfl
      _ = append nil (snoc bs b) := by rfl
  | cons a as ih =>
    intro bs
    calc
      snoc (append (cons a as) bs) b
      _ = snoc (cons a (append as bs)) b := by rfl
      _ = cons a (snoc (append as bs) b) := by rfl
      _ = cons a (append as (snoc bs b)) := by rw [ih]
      _ = append (cons a as) (snoc bs b) := by rfl

/- ex3 : prove this lemma -/
theorem rev_append : ∀ as bs : List A, rev (append as bs) = append (rev bs) (rev as) := by
  intro as
  induction as with
  | nil =>
    intro bs
    calc
      rev (append nil bs)
      _ = rev bs := by rfl
      _ = append (rev bs) nil := by rw [append_rneutr]
      _ = append (rev bs) (rev nil) := by rfl
  | cons a as ih =>
    intro bs
    calc
      rev (append (cons a as) bs)
      _ = rev (cons a (append as bs)) := by rfl
      _ = snoc (rev (append as bs)) a := by rfl
      _ = snoc (append (rev bs) (rev as)) a := by rw [ih]
      _ = append (rev bs) (snoc (rev as) a) := by rw [snoc_append]
      _ = append (rev bs) (rev (cons a as)) := by rfl

/- ex4 : Can you name (define) and prove any other monoid? -/

/- (ℕ, mul, one) -/
/- (Bool, and, true) -/
/- (Bool, or, false) -/
/- (Prop, ∧, True) -/
/- (Prop, ∨, False) -/
