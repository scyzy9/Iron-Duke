/-

Lecture 17 : Lists 2

-/


namespace l17


set_option tactic.customEliminators false

notation "ℕ" => Nat -- \bn
open Nat
open List

variable {A B C : Type}

def append : List A → List A → List A
| [] , as => as
| a :: as , bs => a :: (append as bs)

infixr:65(priority := 1001) " ++ " => append

-- neutral
-- n + 0 = n
-- 0 + n = n
-- associativity
-- l + (m + n) = (l + m) + n
-- monoid
-- l + m = m + l
-- commutativity
-- commutative monoid

-- [] ++ as = as
-- as ++ [] = as
-- (as ++ bs) ++ cs = as ++ (bs ++ cs)

#eval ([1,2]++[3])++[4,5,6]
#eval [1,2]++([3]++[4,5,6])

-- not commutative
#eval [1,2]++[3]
#eval [3]++[1,2]

theorem app_lneutr : ∀ as : List A , [] ++ as = as := by
  intro as
  rfl

theorem app_rneutr : ∀ as : List A , as ++ [] = as := by
   intro as
   induction as with
   | nil =>
      rfl
   | cons a bs ih =>
      calc
        (a :: bs) ++ []
          = a :: (bs ++ []) := by rfl
        _ = a :: bs := by rw [ih]

theorem app_assoc : ∀ as bs cs : List A,
  (as ++ bs) ++ cs = as ++ (bs ++ cs) := by
intro as bs cs
induction as with
| nil =>
    calc
      ([] ++ bs) ++ cs
        = bs ++ cs := by rfl
      _ = [] ++ (bs ++ cs) := by rfl
| cons a as' ih =>
    calc ((a :: as') ++ bs) ++ cs
        = (a :: (as' ++ bs)) ++ cs := by rfl
      _ = a :: ((as' ++ bs) ++ cs) := by rfl
      _ = a :: (as' ++ (bs ++ cs)) := by rw[ih]
      _ = (a :: as') ++ (bs ++ cs) := by rfl

-- (List A , [] , ++) is a monoid
-- not commutative
-- the free monoid , category theory

-- rev : List A → List A
-- rev [1,2,3] = [3,2,1]
-- rev 1::[2,3] = snoc (rev [2,3]) 1
-- snoc [3,2] 1 = [3,2,1]

def snoc : List A → A → List A
| [] , a => [a]
| b :: as , a => b :: snoc as a

#eval snoc [3,2] 1

def rev : List A → List A
| [] => []
| a :: as => snoc (rev as) a

#eval rev [1,2,3]
#eval rev (rev [1,2,3])

-- theorem revsnoc : ∀ bs : List A, ∀ a : A,
--     rev (snoc (rev bs) a) = a :: rev (rev bs) := by sorry

theorem revsnoc : ∀ bs : List A, ∀ a : A , rev (snoc bs a) = a :: rev bs := by
  intro bs a
  induction bs with
  | nil =>
      calc
        rev (snoc [] a)
          = rev [a] := by rfl
        _ = a :: rev [] := by rfl
  | cons b as ih =>
      calc
        rev (snoc (b :: as) a)
        = rev (b :: snoc as a) := by rfl
        _ = snoc (rev (snoc as a)) b := by rfl
        _ = snoc (a :: rev as) b := by rw [ih]
        _ = a :: snoc (rev as) b := by rfl
        _ = a :: rev (b :: as) := by rfl

theorem revrev : ∀ as : List A , rev (rev as) = as := by
  intro as
  induction as with
  | nil => rfl
  | cons a bs ih =>
      calc rev (rev (a :: bs))
          = rev (snoc (rev bs) a) := by rfl
        _ = a :: rev (rev bs)  := by rw [revsnoc]
        _ = a :: bs := by rw [ih]


end l17
