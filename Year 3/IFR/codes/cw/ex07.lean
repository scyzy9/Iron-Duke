/-
COMP2065-IFR Exercise 07
(fast reverse)

Our goal is to prove that fast reverse computes the same function
as reverse.

-/

open List

variable {A B C : Type}
namespace revDefn

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
Our implementation of rev is inefficient: it has O(n^2) complexity.
The definition below (called fastrev) is efficient, having only O(n) complexity.
It uses an auxillary function revaux which accumulates the reversed
List in a 2nd variable.
-/

def revaux : List A → List A → List A
| [], bs => bs
| (a :: as), bs => revaux as (a :: bs)

def fastrev (l : List A) : List A
  := revaux l []

#reduce fastrev [1,2,3]


end revDefn

namespace ex07
open revDefn
/- --- Do not add/change anything above this line --- -/

/-
However we would like to show that fast rev and rev do the same thing.

You'll need to establish a lemma about revaux (hint: try writing
down a precise specification of what revaux does).

You may use the fact that lists with ++ form a monoid
(just copy the proofs from the lecture).
-/
theorem append_nil : ∀ xs : List A , xs ++ [] = xs := by
  intro xs
  induction xs with
  | nil =>
    rfl
  | cons a as ih =>
    calc a :: as ++ []
      = a :: (as ++ []) := by rfl
    _ = a :: as := by rw[ih]

theorem append_assoc : ∀ as bs cs : List A ,  (as ++ bs) ++ cs = as ++ (bs ++ cs) := by
  intro as bs cs
  induction as with
  | nil =>
    rfl
  | cons a as ih =>
    calc a :: as ++ bs ++ cs
      = a :: (as ++ bs ++ cs) := by rfl
    _ = a :: (as ++ (bs ++ cs)) := by rw[ih]
    _ = a :: as ++ (bs ++ cs) := by rfl

theorem snoc_append : ∀ as : List A , ∀ a : A , snoc as a = as ++ [a] := by
  intro as a
  induction as with
  | nil =>
    rfl
  | cons a' as ih =>
    calc snoc (a' :: as) a
      = a' :: snoc as a := by rfl
    _ = a' :: (snoc as a) := by rfl
    _ = a' :: (as ++ [a]) := by rw[ih]
    _ = a' :: as ++ [a] := by rfl

theorem revaux_eq_rev : ∀ xs ys : List A , revaux xs ys = rev xs ++ ys := by
  intro xs
  induction xs with
  | nil =>
    intro ys
    rfl
  | cons a as ih =>
    intro ys
    rw[revaux]
    rw[ih]
    rw[rev]
    rw[snoc_append]
    rw[append_assoc]
    rfl

theorem fastrev_thm : ∀ as : List A , fastrev as = rev as := by
  intro as
  rw[fastrev]
  rw[revaux_eq_rev]
  rw[append_nil]
--- Do not add/change anything below this line ---
end ex07
