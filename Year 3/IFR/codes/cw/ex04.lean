/-
COMP2065-IFR Exercise 04
(Booleans)

    This exercise has 2 parts.

    The first part is "logic chess" which has slightly different rules
    than logic poker but see below. The 2nd part asks you to disprove a
    higher order formula by providing a counterexample.
-/
namespace ex04
/- --- Do not add/change anything above this line --- -/

/-
PART I (60%)
============
Logic chess

Unlike logic poker in logic chess there is no guessing. You either
prove the proposition or you prove its negation.

Consider the following examples:
-/
def Ch0 := ∀ x : Bool, x=x
def Ch00 := ∀ x : Bool, x ≠ x

open ex04

/- the first one is provable hence we prove it -/

theorem ch0 : Ch0 := by
  intro x
  rfl

/- the second one is false hence we prove its negation -/

theorem ch00 : ¬ Ch00 := by
  intro h
  have g : true ≠ true := by
    apply h
  apply g
  rfl

def Ch01 := ∀ x : Bool, (! x) = x
def Ch02 := ∀ x:Bool,∃ y:Bool, x = y
def Ch03 := ∃ x:Bool,∀ y:Bool, x = y
def Ch04 := ∀ x y : Bool, x = y → (! x) = (! y)
def Ch05 := ∀ x y : Bool, (!x) = (!y) → x = y
def Ch06 := ∀ x y z : Bool, x=y ∨ y=z
def Ch07 := ∃ b : Bool, ∀ y:Bool, (b || y) = y
def Ch08 := ∃ b : Bool, ∀ y:Bool, (b || y) = b
def Ch09 := ∀ x : Bool, (∀ y : Bool, (x && y) = y) ↔ x = true
def Ch10 := ∀ x y : Bool, (x && y) = y ↔ x = false

/-
Name your theorems ch01 ch02 ... ch10. chXX should either
be a proof of ChXX or a proof of ¬ ChXX so either delete the
? or replace it by a ¬.
-/

-- @[autogradedProof 3]
theorem ch01 : ¬ Ch01 := by
  intro x
  have np : !true = true := x true
  cases np

-- @[autogradedProof 3]
theorem ch02 : Ch02 := by
  intro x
  cases x
  apply Exists.intro false
  rfl
  apply Exists.intro true
  rfl

-- @[autogradedProof 3]
theorem ch03 : ¬ Ch03 := by
  intro h
  cases h with
  | intro x hx =>
    cases x
    have hxy : false = true := hx true
    cases hxy
    have hxy : true = false := hx false
    cases hxy


-- @[autogradedProof 3]
theorem ch04 : Ch04 := by
  intro x y
  intro xy
  rw[xy]

-- @[autogradedProof 3]
theorem ch05 : Ch05 := by
  intro x y
  intro nxny
  cases x
  cases y
  rfl
  cases nxny
  cases y
  cases nxny
  rfl


-- @[autogradedProof 3]
theorem ch06 : ¬ Ch06 := by
  intro h
  have f := h true false true
  cases f with
  | inl tf =>
    cases tf
  | inr ft =>
    cases ft

-- @[autogradedProof 3]
theorem ch07 : Ch07 := by
  apply Exists.intro false
  intro y
  cases y
  rfl
  rfl


-- @[autogradedProof 3]
theorem ch08 : Ch08 := by
  apply Exists.intro true
  intro y
  cases y
  rfl
  rfl

-- @[autogradedProof 3]
theorem ch09 : Ch09 := by
  intro x
  constructor
  intro hy
  have hyt := hy true
  cases x
  cases hyt
  rfl
  intro hx
  rw [hx]
  intro y
  cases y
  rfl
  rfl

-- @[autogradedProof 3]
theorem ch10 : ¬ Ch10 := by
  intro h
  have h_case := h true true
  have left : true && true = true := by rfl
  cases h_case with
  | intro h1 h2 =>
    have tf := h1 left
    cases tf

/-
PART II (40%)
=============

Show that
(∀ x : A, PP x ∨  QQ x) →  ((∀ x : A, PP x) ∨  (∀ x : A, QQ x))
is not a tautology by constructing a counterexample.
That is, prove the following theorem:
-/
-- @[autogradedProof 20]

theorem cex :
  ¬ ∀ A : Type, ∀ PP QQ : (A → Prop),
   ((∀ x : A, PP x ∨  QQ x) →  ((∀ x : A, PP x) ∨  (∀ x : A, QQ x))) := by
  intro h
  let PP' (b : Bool) : Prop := b = true
  let QQ' (b : Bool) : Prop := b = false
  have H := h Bool PP' QQ'
  have tof : ∀ x : Bool, x = true ∨ x = false := by
    intro x
    cases x
    right
    rfl
    left
    rfl
  have Htof := H tof
  dsimp [PP',QQ'] at Htof
  cases Htof with
  | inl xt =>
    have f : false := xt false
    cases f
  | inr xf =>
    have f := xf true
    cases f



/- --- Do not add/change anything below this line --- -/
 end ex04
