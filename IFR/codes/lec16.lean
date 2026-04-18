/-

Lecture 16 : Lists

-/


namespace l16


set_option tactic.customEliminators false

notation "ℕ" => Nat -- \bn
open Nat

def add : ℕ → ℕ → ℕ
| m  , zero     => m
| m  , (succ n) => succ (add m n)
-- ANCHOR_END: add

--infixl:65 " + " => add
--notation:65 m:arg "+" n:arg => add m n
notation:65 (priority := 1001) m:65 "+" n:66 => add m n

-- ANCHOR: add_rneutr
theorem add_rneutr : ∀ n : ℕ, n + 0 = n := by
intro n
rfl
-- ANCHOR_END: add_rneutr

-- ANCHOR: add_lneutr
theorem add_lneutr : ∀ n : ℕ, 0 + n  = n := by
intro n
induction n with
 | zero => rfl
 | succ m ih =>
     calc 0 + (succ m)
          = succ (0 + m)  := by rfl
          _ = succ m := by rw [ih]
-- ANCHOR_END: add_lneutr

-- ANCHOR: add_assoc
theorem add_assoc : ∀ l m n : ℕ , (l + m) + n = l + (m + n) := by
intro l m n
induction n with
| zero => rfl
| succ n' ih =>
     calc  (l + m) + (succ n')
         = succ ((l + m) +n') := by rfl
      _  = succ (l + (m + n')) := by rw [ih]
      _  = l + (succ (m + n')) := by rfl
      _  = l + (m + (succ n')) := by rfl
-- ANCHOR_END: add_assoc

-- ANCHOR: add_succ
theorem add_succ :
∀ l m : ℕ, (succ l) + m = succ (l + m) := by
intro l m
induction m with
 | zero => rfl
 | succ m ih =>
     calc
       (succ l) + (succ m)
         = succ ((succ l ) + m) := by rfl
       _ = succ (succ (l + m)) := by rw [ih]
       _ = succ (l + succ m) := by rfl
-- ANCHOR_END: add_succ

-- ANCHOR: add_comm
theorem add_comm : ∀ l m : ℕ, l + m = m + l := by
{
intro l m
induction m with
  | zero =>
      calc l + 0
          = l := by rfl
        _ = 0 + l := by rw [add_lneutr]
  | succ m ih =>
        calc   l + (succ m)
            = succ (l + m) := by rfl
          _ = succ (m + l) := by rw[ih]
          _ = (succ m) + l := by rw [← add_succ]}
-- ANCHOR_END: add_comm

open List
variable {A B C : Type}

#check [1,2,3]
#check 1 :: 2 :: 3 :: []
#check cons 1 (cons 2 (cons 3 nil))
-- 1 : 2 : 3 : [] :: [Int]

#check [true,false]
#check [[1],[2,3]]
-- #check [1,2,true]

inductive NatOrBool : Type where
| nat : ℕ → NatOrBool
| bool : Bool → NatOrBool

open NatOrBool

#check [nat 1, nat 2, bool true]

-- disjoint union

-- LISP 1959, McCarthy
-- [] , nil = not in list
-- cons , ::

-- inductive List (A : Type) : Type where
-- | nil : List A
-- | cons : A → List A → List A

-- inductive Nat : Type where
-- | zero : Nat
-- | succ : Nat → Nat

-- Lists are very similar to natural numbers

-- Peano like principles for List
-- 0 ≠ succ n
theorem no_conf : ∀ a : A, ∀ as : List A , [] ≠ a :: as := by
intro a as h
cases h

def IsNil : List A → Prop
| [] => True
| _ :: _ => False

-- succ m = succ n → m = n
-- via pred
-- constructors are injective

theorem cons_inj1 : ∀ a b : A, ∀ as bs : List A,
  a :: as = b :: bs → a = b := by
  intro a b as bs eq
  injection eq

theorem cons_inj2 : ∀ a b : A, ∀ as bs : List A,
  a :: as = b :: bs → as = bs := by
  intro a b as bs eq
  injection eq

-- how can I prove?
def tl : List A → List A
| [] => []
| _ :: as => as

theorem cons_inj2' : ∀ a b : A, ∀ as bs : List A,
  a :: as = b :: bs → as = bs := by
  intro a b as bs eq
  change tl (a :: as) = bs
  rw [eq]
  rfl

def hd : List A → A
| [] => sorry
| a :: _ => a

-- doesn't work
-- challenge: prove cons_inj1 without using injection

-- List induction
-- If a property holds for [] and given that it holds for as
-- it also holds for a :: as (for any a), then it holds for all lists.

def length : List A → ℕ
| [] => 0
| _ :: as => succ (length as)

#eval length [1,2,3]

def append : List A → List A → List A
| [] , as => as
| a :: as , bs => a :: (append as bs)

#eval append [1,2,3] [4,5]

infixr:65 (priority := 1001) " ++ " => append

#eval [1,2,3]++[4,5]

#eval length ([1,2,3]++[4,5])
#eval (length [1,2,3])+(length [4,5])

theorem length_append : ∀ as bs : List A,
  length (as ++ bs) = (length as) + (length bs) := by
intro as bs
induction as with
| nil =>
   calc length ([] ++ bs)
        = length bs := by rfl
      _ = 0 + length bs := by rw [add_lneutr]
      _ = length []+length bs := by rfl
| cons a as ih =>
   calc length ((a :: as) ++ bs)
          = length (a :: (as ++ bs)) := by rfl
        _ = succ (length (as ++ bs)) := by rfl
        _ = succ (length as + length bs) := by rw [ih]
        _ = (succ (length as))+length bs := by rw [← add_succ]
        _ = length (a :: as)+length bs := by rfl

-- next : (List A, [], ++) are a monoid
#eval ([1,2]++[3])++[5,6,7]
#eval [1,2]++([3]++[5,6,7])

#eval [1,2]++[3,4]
#eval [3,4]++[1,2]
-- free monoid


end l16
