/-
COMP2065-IFR Exercise 08
(permutation)

Our goal is to prove that reverse outputs a permutation of its input.

-/
namespace ex08

open List
variable {A B C : Type}

/-
In the lecture we have introduced the function reverse
(and the auxilliary function snoc)
-/

def snoc : List A → A → List A
| [], a => [a]
| (a :: as), b => a :: (snoc as b)

def rev : List A → List A
| [] => []
| (a :: as) => snoc (rev as) a

/-
1. Show that rev (or fastrev) does actually outputs a permutation
of its input. That is, prove perm_rev.

I include the definition of Perm (and the auxilliary Insert)
here.

Hint : You will need to state and prove a lemma about snoc.
-/

inductive Insert : A → List A → List A → Prop
| ins_hd : ∀ a:A, ∀ as : List A,Insert a as (a :: as)
| ins_tl : ∀ a b:A, ∀ as as': List A, Insert a as as'
        → Insert a (b :: as) (b :: as')

inductive Perm : List A → List A → Prop
| perm_nil : Perm [] []
| perm_cons : ∀ a : A, ∀ as bs bs' : List A,Perm as bs
      → Insert a bs bs' → Perm (a :: as) bs'

open Insert
open Perm

theorem insert_snoc : ∀ (a : A) (as : List A), Insert a as (snoc as a) := by
  intro a as
  induction as with
  | nil =>
    rw[snoc]
    apply ins_hd
  | cons a' as ih =>
    rw[snoc]
    apply ins_tl
    exact ih

theorem perm_rev : ∀ as : List A, Perm as (rev as) := by
  intro as
  induction as with
  | nil =>
    dsimp[rev]
    exact perm_nil
  | cons a as ih =>
    rw[rev]
    apply Perm.perm_cons
    . exact ih
    . apply insert_snoc


/-
2. This shouldn't be to difficult. If you are looking for a challenge
try to prove that Perm is an equivalence relation, that is:
variables as bs cs  : List A

theorem refl_perm : Perm as as := sorry
theorem sym_perm : Perm as bs → Perm bs as := sorry
theorem trans_perm : Perm as bs → Perm bs cs → Perm as cs := sorry

The first one is quite easy but the other
two require some lemmas.
-/

variable (as bs cs as' bs' cs' : List A)
variable (a b : A)

theorem refl_perm : Perm as as := by
  induction as with
  | nil =>
    exact perm_nil
  | cons a as' ih =>
    apply Perm.perm_cons
    . exact ih
    . apply ins_hd

theorem trans_perm : Perm as bs → Perm bs cs → Perm as cs := by
  intro h1 h2
  sorry

theorem sym_perm : Perm as bs → Perm bs as := by
  intro h
  induction as with
  | nil =>
    cases h
    apply Perm.perm_nil
  | cons a as' ih =>
    sorry




end ex08
