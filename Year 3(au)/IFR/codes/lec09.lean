--       How to prove      How to use
-- ∧     constructor       cases ... with
-- ∨     left / right      cases ... with
-- →      intro a           apply ...
-- ∀     intro xa          apply ...
-- ∃     constructor/      cases ... with
-- ∃       exists xa


--De Morgan's Propositional logic

-- ¬(P ∨ Q) ↔ ¬ P ∧ ¬ Q   can be proven intuitioistically
-- ¬(P ∧ Q) ↔ ¬ P ∨ ¬ Q

--De Morgan's Predicate logic
--(¬ ∃ x : A, PP x) ↔ (∀ x : A, ¬ PP x)
--(¬ ∀ x : A, PP x) ↔ (∃ x : A, ¬ PP x)

variable (PP QQ : A → Prop)

theorem dm1 : (¬ ∃ x : A, PP x) ↔ (∀ x : A, ¬ PP x) := by
  constructor
  · intro nex
    intro x
    intro ppx
    apply nex
    exists x
  · intro anx
    intro ex
    cases ex with
    | intro x ppx =>
      have nppx :=anx x
      exact nppx ppx

open Classical

theorem raa : ¬¬ P → P := by
  intro nnp
  cases em P with
  | inl p =>
    exact p
  | inr np =>
    have f : False := by
      apply nnp
      exact np
    cases f

theorem dm2 : (¬ ∀ x : A, PP x) ↔ (∃ x : A, ¬ PP x) := by
  constructor
  · intro nax
    apply raa
    intro nenx
    apply nax
    intro x
    apply raa
    intro nppx
    apply nenx
    exists x
  · intro enx
    cases enx with
    | intro x nppx =>
      intro appx
      apply nppx
      have ppx := appx x
      exact ppx


example {P Q R} : (P → (Q → R)) ↔ ((P → Q) → R):= sorry
--false when P Q R are all false.


example : ¬ ∀ P Q R : Prop,(P → (Q → R)) ↔ ((P → Q) → R) := by
  intro all
  have counter : (False → (False → False)) ↔ ((False → False) → False) := by
    apply all
  cases counter with
  | intro ttf ftt =>
    apply ttf
    intro f _
    exact f
    intro f
    exact f

example : ∃ P Q : Prop, P → Q := by
  exists False
  exists True

example : ∃ P : Prop,
