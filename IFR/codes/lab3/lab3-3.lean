/-
Introduction to Formal Reasoning (Comp 2065)
Tutorial 03: Predicate Logic
Date: 23 Oct 2025
TA: Aref Mohammadzadeh
You can download tutorial files from moodle `Tutorials -> Aref`.



This week, we cover the quantifiers 'For all' (∀) and 'There exists' (∃),
and equality (=), and translation from natural language to predicate logic.
-/

variable {A B : Type}
variable (P Q : A → Prop)
variable (S : Prop)
variable (R : A → B → Prop)

open Classical

/-
## Part 1: Quantifiers (∀, ∃)

How to PROVE them (when they are in the goal):
- `∀ x, P x`: Use `intro x`. This gives an arbitrary `x : A` and a new goal `P x`.
- `∃ x, P x`: Use `exists x` to provide the witness
              and get the goal `P x` immediately.

How to USE them (when they are hypotheses):
- `h : ∀ x, P x`: Use `apply h`. Or, create a specific copy by `have`.
- `h : ∃ x, P x`: Use `cases h with | intro x hx => ...`. This gives you
                  a *specific* element `x` and a hypothesis `hx : P x`.
-/
--
theorem ex1 :
  (¬ (∀ x : A, ¬ P x)) → (¬ ¬ (∃ x : A, P x)) := by
   intro nnpx
   intro npx
   apply nnpx
   intro x
   intro px
   apply npx
   exists x



theorem ex2 : (∀ x : A, P x ∧ Q x) ↔ (∀ x : A, P x) ∧ (∀ x : A, Q x) := by
  constructor
  · intro pxqx
    constructor
    · intro x
      have hpxqx := pxqx x
      cases hpxqx with
      | intro px qx =>
        exact px
    · intro x
      have hpxqx := pxqx x
      cases hpxqx with
      | intro px qx =>
        exact qx
  · intro pxqx
    cases pxqx with
    | intro px qx =>
      intro x
      have hpx := px x
      have hqx := qx x
      constructor
      · assumption
      · assumption





theorem ex3 : (∃ x : A, P x ∨ Q x) ↔ (∃ x : A, P x) ∨ (∃ x : A, Q x) := by
  constructor
  · intro pxqx
    cases pxqx with
    | intro x hpxqx =>
      cases hpxqx with
      | inl px =>
        left
        exists x
      | inr qx =>
        right
        exists x
  · intro pxqx
    cases pxqx with
    | inl xpx =>
      cases xpx with
      | intro x px =>
        exists x
        left
        exact px
    | inr xqx =>
      cases xqx with
      | intro x qx =>
        exists x
        right
        exact qx


theorem ex4 : (∃ x : A, P x → Q x) → (∀ x : A, P x) → (∃ x : A, Q x) := by
  intro pxqx
  intro px
  cases pxqx with
  | intro x hpxqx =>
    have hpx := px x
    have qx := hpxqx hpx
    exists x

--
theorem ex5 : (∀ x : A, P x ∨ S) → (∀ x : A, P x) ∨ S := by
  intro pxs
  cases em S with
  | inl s =>
    right
    exact s
  | inr ns =>
    left
    intro x
    have hpxs : (P x ∨ S) := pxs x
    cases hpxs with
    | inl px =>
      exact px
    | inr s =>
      contradiction

/-

## Part 2: Equality (=)

The `rw` tactic uses equality.
- `rw [h]`: If `h : x = y`, changes `x` to `y` in the goal.
- `rw [← h]`: If `h : x = y`, changes `y` to `x` in the goal.
- `rw [h] at p` : If `h : x = y`, changes `x` to `y` in the assumption `p`.

The `rfl` tactic proves any goal of the form `t = t`.
-/

theorem ex6_refl : ∀ (x : A), x = x := by
  intro x
  rfl

theorem ex7_symm : ∀ (x y : A), x = y → y = x := by
 intro x y xy
 rw[xy]

theorem ex8_trans : ∀ (x y z : A), x = y → y = z → x = z := by
  intro x y z
  intro xy yz
  rw[xy]
  exact yz

theorem ex9_congr : ∀ (x y : A), x = y → P x → P y := by
  intro x y
  intro xy px
  rw[←xy]
  exact px

-- Try to solve the next exercise by using `rw [_] at _ `.
theorem ex10_trans_variant : ∀ (x y z : A), x = y → z = y → x = z := by
 intro x y z
 intro xy zy
 rw[←zy] at xy
 exact xy

-- Exercise 11:
-- (a) Define this property:
-- A property `P` is unique to `x` if `x` has it,
-- and any other thing `z` that has it must be equal to `x`.
def IsUnique (P : A → Prop) (x : A) : Prop :=
  P x ∧ (∀ z : A, P z → z = x)


-- (b) Now state and prove this theorem: If `P` is unique to `x`,
-- and `y` has property `P`, then `y` must be equal to `x`.
--theorem eq6_uniqueness (x y : A) (P : A → Prop) :



/-
## Part 3: Translation to Predicate Logic
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

--
-- "Smith is a professor and teaches LogicCourse."
def ex12_smith_teaches_Logic : Prop :=
  sorry




-- "There exists at least one professor."
def ex13_has_professors : Prop := sorry


--
-- "No person is both a student and a professor."
def ex14_no_student_prof : Prop :=
 sorry




-- "The person `x` is a student who is not enrolled in any courses."
def ex15_student_no_courses (x : Person) : Prop := sorry


--
-- "The persons `x` and `y` are students and share at least one course."
def ex16_common_course (x y : Person) : Prop :=
 sorry

-- "There is a student who is only enrolled in courses taught by Professor Smith."
def ex17_only_smith : Prop := sorry


-- exercise 18 : State and then prove this fact:
-- "If two people are course-mates, then there must exist at least one course."
theorem ex18 (x y : Person) :
ex16_common_course x y → (∃ c : Course, true) := by
sorry


end University
