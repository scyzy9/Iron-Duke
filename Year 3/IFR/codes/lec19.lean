/-

Lecture 19 : Permutation

-/


namespace l19


set_option tactic.customEliminators false

notation "ℕ" => Nat -- \bn
open Nat
--open List
open List hiding Perm perm_cons perm_nil

variable {A B C : Type}

def le_ℕ : ℕ → ℕ → Bool
| zero , n => true
| succ m , zero => false
| succ m , succ n => le_ℕ m n

def insert : ℕ → List ℕ → List ℕ
| n , [] => [n]
| n , m :: ms =>
    match le_ℕ n m with
    | true => n :: (m :: ms)
    | false => m :: insert n ms

#eval insert 3 [1,2,4,5]

def sort : List ℕ → List ℕ
| [] => []
| n :: ns => insert n (sort ns)

#eval sort [6,3,8,2,3]

-- Sorted : List ℕ → Prop
-- ∀ ns : List ℕ, Sorted (sort ns)

def cheat_sort : List ℕ → List ℕ
| _ => []

-- ∀ n : ℕ, n ∈ ns ↔ n ∈ sort ns

-- permutation
-- Perm : List A → List A → Prop
-- Perm [1,2,3] [3,2,1]
-- Perm [1,2,1] [1,1,2]
-- ¬ Perm [1,2,1] [1,2,2]
-- Perm ns (sort ns)
-- Insert : A → List A → List A → Prop
-- Insert 2 [1,3] [1,2,3]
-- Insert 2 [1,3] [2,1,3]
-- Insert 2 [1,3] [1,3,2]
-- Insert 2 [1,3] [2,1,3]

inductive Insert :
   A → List A → List A → Prop

| ins_hd : ∀ {a : A}{as : List A},

    ---------------------
    Insert a as (a :: as)

| ins_tl :
    ∀ a b : A, ∀ bs abs : List A,

    Insert a bs abs →
    -------------------------
    Insert a (b::bs) (b::abs)

open Insert

example : Insert 2 [1,3] [1,2,3] := by
  apply ins_tl
  apply ins_hd

inductive Perm : List A → List A → Prop

| perm_nil :

  -----------
  Perm [] []

| perm_cons :
  ∀ a : A, ∀ as bs abs : List A,

  Perm as bs →
  Insert a bs abs →
  ------------------
  Perm (a::as) abs

open Perm -- Perm.perm_nil

example : Perm [1,2,3] [3,2,1] := by
  apply perm_cons
  . apply perm_cons
    . apply perm_cons
      . apply perm_nil
      . apply ins_hd
    . apply ins_tl
      apply ins_hd
  . apply ins_tl
    apply ins_tl
    apply ins_hd

example : Perm [1,2] [2,1] := by
  apply perm_cons
  . apply perm_cons
    . apply perm_nil
    . apply ins_hd
  . apply ins_tl
    apply ins_hd

example : Perm [1,2,3,4] [4,3,2,1] := by
  apply perm_cons
  . apply perm_cons
    . apply perm_cons
      . apply perm_cons
        . apply perm_nil
        . apply ins_hd
      . apply ins_tl
        . apply ins_hd
    . apply ins_tl
      apply ins_tl
      apply ins_hd
  . apply ins_tl
    apply ins_tl
    apply ins_tl
    apply ins_hd

theorem insert_inserts :
  ∀ ns : List ℕ , ∀ n : ℕ,
  Insert n ns (insert n ns) := by
  intro ns n
  induction ns with
  | nil =>
      dsimp [insert]
      apply ins_hd
  | cons m ms ih =>
      dsimp [insert]
      -- split
      -- .
      -- .
      cases le_ℕ n m with
      | true =>
        change Insert n (m :: ms) (n :: m :: ms)
        apply ins_hd
      | false =>
        change Insert n (m :: ms) (m :: insert n ms)
        apply ins_tl
        assumption

theorem perm_sort : ∀ ns : List ℕ,
    Perm ns (sort ns) := by
  intro ns
  induction ns with
  | nil =>
      dsimp [sort]
      apply perm_nil
  | cons n ns ih =>
      dsimp [sort]
      apply perm_cons
      . apply ih
      . apply insert_inserts

theorem refl_perm : ∀ as : List A,
    Perm as as := by
    intro as
    induction as with
    | nil =>
        apply perm_nil
    | cons a as ih =>
        apply perm_cons
        apply ih
        apply ins_hd

theorem sym_perm : ∀ as bs : List A,
  Perm as bs → Perm bs as := by sorry

theorem trans_perm : ∀ as bs cs : List A,
  Perm as bs → Perm bs cs → Perm as cs := by sorry





--- START

end l19
