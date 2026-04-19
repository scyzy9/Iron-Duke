/-
Introduction to Formal Reasoning (Comp 2065)
Tutorial 04: Predicate Logic- Part 2
Date: 30 Oct 2025
TA: Aref Mohammadzadeh
You can download tutorial files from moodle `Tutorials -> Aref`.

-/

/-

How to PROVE ∀ and ∃? (when they are in the goal):
- `∀ x, P x`: Use `intro x`. This gives an arbitrary `x : A` and a new goal `P x`.
- `∃ x, P x`: Use `exists x` to provide the witness
              and get the goal `P x` immediately.

How to USE them (when they are hypotheses):
- `h : ∀ x, P x`: Use `apply h`. Or, create a specific copy by `have`.
- `h : ∃ x, P x`: Use `cases h with | intro x hx => ...`. This gives you
                  a *specific* element `x` and a hypothesis `hx : P x`.

--------------

The `rw` tactic uses equality.
- `rw [h]`: If `h : x = y`, changes `x` to `y` in the goal.
- `rw [← h]`: If `h : x = y`, changes `y` to `x` in the goal.
- `rw [h] at p` : If `h : x = y`, changes `x` to `y` in the assumption `p`.

The `rfl` tactic proves any goal of the form `t = t`.

-/
variable {A B : Type}
variable (P Q : A → Prop)
variable (R PP QQ : A → A → Prop)

/-
## Part 1: Quantifiers and Equality
-/

theorem ex1 : ∀ a b : A, P b → ∃ x : A, P a → P x := by
   intro a b
   intro pb
   exists a
   intro pa
   exact pa

theorem ex2 : ∀ a b : A, ∃ c : A, QQ a b → b=c := by
  intro a b
  exists b
  intro qqab
  rfl

theorem ex3 : ∀ a : A, ∃ b : A, ∀ c : A, b=c → PP a b → PP c b := by
  intro a
  exists a
  intro c
  intro ac
  intro ppaa
  rw[←ac]
  exact ppaa

theorem ex4 : ∀ a b c d : A, ∃ e : A, a=c → d=e → P a = P b → P c = P d := by
  intro a b c d
  exists b
  intro ac db
  intro papb
  rw[db]
  rw[←ac]
  exact papb

--a bit more challenging exercise?
theorem ex5 :
  (∀ a : A, ∃ b : A, R a b) →
  (∀ a b : A, (R a b ∧ P a) → P b) →
  (∀ a y z : A, (R a y ∧ P y) ∧ (R a z ∧ P z) → z = y) →
  (∀ x : A, P x → (∃ y : A, R x y ∧ P y ∧ (∀ z : A, (R x z ∧ P z) → y = z))) :=
by
  intro h1
  intro h2
  intro h3
  intro x
  intro px
  have h1a := h1 x





-- exercise 6:
-- (a): Define the following property:
-- A property `P` is unique to `x` if `x` has it,
-- and any other thing `z` that has it must be equal to `x`.
def IsUnique (P : A → Prop) (x : A) : Prop :=
∀ z : A, P z → z = x

-- (b) Prove this theorem: If `P` is unique to `x`, and `y` has property `P`,
-- then `y` must be equal to `x`.
theorem ex6 (x y : A) (P : A → Prop) :
  IsUnique P x → P y → y = x := by
  intro ipx
  intro py
  have xy : y = x := ipx y py
  exact xy

/-
## Part 2: Translation to Predicate Logic
-/
namespace University

axiom Person : Type
axiom Course : Type

axiom Student : Person → Prop
axiom Professor : Person → Prop

axiom Teaches : Person → Course → Prop
axiom Enrolled : Person → Course → Prop

axiom Smith : Person
axiom LogicCourse : Course

-- "Smith is a professor and teaches COMP2065."
def ex7_smith_teaches_2065 : Prop :=
sorry

-- "There exists at least one professor."
def ex8_has_professors : Prop :=
  sorry

-- "No person is both a student and a professor."
def ex9_no_student_prof : Prop :=
 sorry

-- "The person `x` is a student who is not enrolled in any courses."
def ex10_student_no_courses (x : Person) : Prop :=
  sorry

-- "The persons `x` and `y` are students and share at least one course."
def ex11_common_course (x y : Person) : Prop :=
sorry

-- "There is a student who is only enrolled in courses taught by Professor Smith."
def ex12_only_smith : Prop :=
sorry
-- Exercise 13:
-- Now first state and then prove this fact:
-- "If two people are course-mates, then there must exist at least one course."
theorem ex13 (x y : Person) :
  ex11_common_course x y → (∃ c : Course, true) := by
 sorry


end University
