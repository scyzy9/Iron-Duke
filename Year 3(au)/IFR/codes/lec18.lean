/-

Lecture 18 : insertion sort

-/


namespace l18


set_option tactic.customEliminators false

notation "ℕ" => Nat -- \bn
open Nat
open List

variable {A B C : Type}

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

-- ANCHOR: LE
def LE : Nat → Nat → Prop
| m , n => ∃ k : ℕ , k + m = n

infix:50 (priority := 1001) " ≤ " => LE
-- ANCHOR_END: LE

-- ANCHOR: refl_LE
theorem refl_LE : ∀ n : ℕ, n ≤ n := by
intro n
exists 0
apply add_lneutr
-- ANCHOR_END: refl_LE

-- ANCHOR: trans_LE
theorem trans_LE : ∀ l m n : ℕ, l ≤ m → m ≤ n → l ≤ n := by
intro l m n
intro lm mn
cases lm with
| intro k klm =>
    cases mn with
    | intro j jmn =>
        exists j + k
        calc j + k + l
             = j + (k + l) := by rw [add_assoc]
            _ = j + m := by rw [klm]
            _ = n := by assumption
-- ANCHOR_END: trans_LE

def le_ℕ : ℕ → ℕ → Bool
| zero , n => true
| succ m , zero => false
| succ m , succ n => le_ℕ m n

theorem LE2le : ∀ m n : ℕ, m ≤ n → le_ℕ m n = true := by
  sorry
theorem le2LE : ∀ m n : ℕ, le_ℕ m n = true → m ≤ n := by
  sorry

--- START

#check [6,3,8,2,3]

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

-- want to show that sort ns is a sorted list
-- how to specify sorted
-- Sorted : List ℕ → Prop
-- Mem : A → List A → Prop
-- write a ∈ as for Mem a as
/-

---------
Sorted []

Sorted ns
∀ i : ℕ, i ∈ ns → n ≤ i
-----------------------
Sorted (n :: ns)

-----------
a ∈ a :: as

a ∈ as
-----------
a ∈ b :: as
-/

inductive Mem : A → List A → Prop
| mem_hd : ∀ {a : A} , ∀ {as : List A},

  ---------------
  Mem a (a :: as)

| mem_tl : ∀ {a b : A} , ∀ {as : List A},

  Mem a as →
  ----------
  Mem a (b :: as)

open Mem

infix:50 (priority := 1001)" ∈ " => Mem

example : 2 ∈ [1,2,3] := by
  apply mem_tl
  apply mem_hd

example : ∀ a : A, ¬ (a ∈ []) := by
  intro a pcf
  cases pcf

example : ∀ i : ℕ, i ∈ [1,2] → i=1 ∨ i=2 := by
  intro i h
  cases h with
  | mem_hd =>
      left
      rfl
  | mem_tl x =>
      cases x with
      | mem_hd =>
          right
          rfl
      | mem_tl y =>
          cases y

example : ¬ Mem 5 [1,2,3] := by
  intro h
  cases h with
  | mem_tl h'=>
    cases h' with
    | mem_tl h'' =>
      cases h'' with
      | mem_tl h''' =>
        cases h'''

/-

---------
Sorted []

Sorted ns
∀ i : ℕ, i ∈ ns → n ≤ i
-----------------------
Sorted (n :: ns)
-/

inductive Sorted : List ℕ → Prop

|  sorted_nil :

   ---------
   Sorted []

| sorted_cons : ∀ {n : ℕ}, ∀ {ns : List ℕ},

   Sorted ns →
   (∀ i : ℕ, i ∈ ns → n ≤ i) →
   ----------------------------
   Sorted (n :: ns)

open Sorted

example : Sorted [1,2] := by
  apply sorted_cons
  . apply sorted_cons
    . apply sorted_nil
    . intro i h
      cases h
  . intro i h
    cases h with
      | mem_hd =>
          apply le2LE
          rfl
      | mem_tl pcf =>
          cases pcf

example : ¬ Sorted [3,4,2,1] := by
  intro h
  cases h with
  | sorted_cons h1 h2 =>
    cases h1 with
    | sorted_cons h3 h4 =>
      cases h3 with
      | sorted_cons h5 h6 =>
        have hf : 2 ≤ 1 := h6 1 mem_hd
        cases hf with
        | intro n hfalse =>
          cases hfalse


  example : ¬Sorted [3, 1, 2] := by
  intro h
  cases h with
  | sorted_cons h_sorted h_le =>
    have h1 : 3 ≤ 1 := h_le 1 mem_hd
    cases h1 with
    | intro n h2 =>
      cases h2


-- by decide

theorem insert_lem : ∀ ns :List ℕ, ∀ n : ℕ,
  Sorted ns → Sorted (insert n ns) := by
  intro ns n h
  induction ns with
  | nil =>
      dsimp [insert]
      apply sorted_cons
      . apply sorted_nil
      . intro i pcf
        cases pcf
  | cons m ns ih =>
      dsimp [insert]
      cases b : le_ℕ n m
      . change Sorted (m :: insert n ns)
        sorry
      . change Sorted (n :: m :: ns)
        sorry

-- ∀ a : A, PP a → QQ a
-- ∀ x : A, x ∈ as → PP x
-- ∀ x : A, x ∈ as → QQ x

-- ¬ (m ≤ n) → n ≤ m

theorem sort_sorts : ∀ ns : List ℕ,
  Sorted (sort ns) := by
  intro ns
  induction ns with
  | nil =>
      dsimp [sort]
      apply sorted_nil
  | cons n ns ih =>
      dsimp [sort]
      apply insert_lem
      assumption
