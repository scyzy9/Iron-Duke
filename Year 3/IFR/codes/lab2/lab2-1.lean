-- Welcome to the COMP2065 (IFR) Tutorial!
-- Many thanks to Warren for providing these exercises!
--
-- Download today's tutorial from Moodle:
-- `Tutorials > Cas > Tutorial 2 Exercises - Cas`.
--
--

-- we need classical logic in parts of this session
-- for the excluded middle
open Classical

variable (P Q R : Prop)


/-
 -- Tutorial #2: Part 1
 -/

/- demo -- `true`, `false`, and `neg(ation)` -/

-- if true is in our goal, then we can finish the proof with `constructor`
example : True := by
  constructor

-- here we introduce `false` into our assumed truths; hence, we can finish our
--proof by applying the cases tactic.
-- remember the vacuous truth: False → "anything" is always True.
example : False → P := by
  intro f
  cases f

-- note here that I use `theorem` and give it a name `def_not`.
-- this is because I think this is useful and I might use it later on!
  -- remember here that the assumption we introduce `np : ¬P` is just pretty
  --printing for `np : P → false`.
theorem def_not : ¬P → P → False := by
  intro np p
  apply np
  exact p

-- I already proved the left-to-right dorection in the theorem `def_not`.
example : ¬P ↔ P → False := by
  constructor
  · intro np p
    apply np
    exact p
  · intro pf np
    apply pf
    assumption


-- this is not provable intuitionistically -- see below.
example : ¬¬P → P := by
  sorry

/- exercises - construction of truth table for implication. -/

theorem ex1 : False → True := by
  intro f
  constructor

theorem ex2 : False → False := by
  intro f
  cases f

theorem ex3 : True → True := by
  intro t
  exact t

theorem ex4 : True → False := by
  sorry

/- exercises - negation -/

theorem ex5 : ¬ (P ∧ ¬P) := by
  intro h
  cases h with
  | intro p np =>
    apply np
    exact p

theorem ex6 : ¬P → ¬¬¬P := by
  intro np
  intro nnp
  apply nnp
  exact np




/-
 -- Tutorial #2: Part 2
 -/

/- demo -- Proving the unprovable. -/

-- we can show something is not provable, in this case `ex4`, by proving its negation.
theorem neg_ex4 : ¬(True → False) := by
  intro tf
  apply tf
  constructor

/- demo -- Classical Logic: Excluded Middle (`em P`) and Reduction Ad Adsurdo
(`raa`) -/

-- note the definition `em : ∀ (p : Prop), p ∨ ¬p`
-- Read, for all Propositions p, p ∨ ¬p is true.

-- uncomment to check if you want.
-- #check em

/- truth table for P ∨ ¬P
--
--------------------
-- P | ¬P | P ∨ ¬P |
--------------------
-- T | F  |   T    |
-- F | T  |   T    |
--------------------
-/

-- we can't do anything here with `P`.
-- Using `P ∨ ¬P` can help since we can then prove `P` in the first case,
-- and we can derive a contradiction through `¬P` being added to the premises.
-- this proof also requires the tactic `have` to prove a contradiction on the
--right-hand case.
example : (¬ P → Q) → (¬ Q → P) := by
  intro npq nq
  have pnp : P ∨ ¬P := by
    apply em P
  cases pnp with
  | inl p =>
    exact p
  | inr np =>
    have f : False := by
      apply np


-- we can prove `¬¬P → P` classically. Lets call this theorem `raa` so we can reuse
--it later.
open Classical

theorem raa : ¬¬ P → P := by
  classical
  intro nnp
  cases Classical.em P with
  | inl p =>
    exact p
  | inr np =>
    contradiction

-- we saw previously that this cannot be proven intuitionistically.
-- Let's try and prove this classically using raa and **without using (em P)**.
example : P ∨ ¬P := by
    have nnp : ¬¬(P ∨ ¬P) := by
        intro n
        apply n
        right
        intro p
        apply n
        left
        exact p
    apply raa
    exact nnp

/- exercises - excluded middle and reduction ad adsurdo -/

-- this example demonstrates that we can use any Proposition other than `P` with
--the excluded middle.
-- Remember the definition `em : ∀ (p : Prop), p ∨ ¬p`, what if our Proposition
--is `Q`?
-- This can be proven in one line if you think about it!
theorem ex7 : Q ∨ ¬Q := by
  apply em Q

-- this is another example, but this time, our proposition is `P ∧ Q`
-- this can, of course, be proven by applying `em` and lean does its magic, but that's
--not the point of this exercise!
theorem ex8 : (P ∧ Q) ∨ ¬(P ∧ Q) := by
  have nnpq : ¬¬(P ∧ Q ∨ ¬(P ∧ Q)) := by
    intro n
    apply n
    right
    intro pq
    apply n
    left
    exact pq
  apply raa
  exact nnpq

-- this example is from the lecture notes but solved in one whole attempt.
-- try to solve it without referening the lectures by using the tactics we have
--reinforced today.
theorem ex9 : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  constructor
  intro npq
  have pnp : P ∨ ¬P := by
    apply em P
  cases pnp with
  | inr np =>
    left
    exact np
  | inl p =>
    right
    intro q
    have f : False := by
      apply npq
      constructor
      assumption
      assumption
    cases f
  intro npnq
  intro pq
  cases pq with
  | intro p q =>
    cases npnq with
    | inl np =>
      have f : False := by
        apply np
        exact p
      cases f
    | inr nq =>
      have f : False := by
        apply nq
        exact q
      cases f

open Classical

theorem ex10 : (¬ P → Q) → (¬ Q → P) := by
  intro h nq
  have nnP : ¬¬P := by
    intro nP
    exact nq (h nP)
  exact not_not.mp nnP


theorem ex11 : (¬ P → P) → P := by
  intro h
  cases em P with
    | inl p =>
      exact p
    | inr np =>
      exact h np




-- this example was to demonstrate how it is useful to reuse proofs we have
--already proven.
-- feel free not to use `raa` but you will be here a while using serveral `cases em P`
--and `have f : False := by`!
theorem ex12 : ¬¬ ¬¬ ¬¬P -> P := by
  intro h
  apply raa
  apply raa
  apply raa
  exact h


-- End of tutorial #2 exercises 🍰 --

/-
  If you managed to get ahead during the tutorial, here is a challenge for you!
-/
open Classical
theorem advanced_constraposition : (P → Q) ↔ (¬Q → ¬P) := by
  constructor
  · intro pq nq
    intro p
    exact nq (pq p)
  · intro nqnp p
    cases em Q with
    | inl q =>
      exact q
    | inr nq =>
      have np : ¬ P := nqnp nq
      have f : False := np p
      cases f





/-
  Challenge - prove the second De Morgan's Theorem.
  Not required during tutorials but interesting to do in your own time.
-/

theorem dm2 : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  constructor
  · intro npq
    constructor
    · intro p
      apply npq
      left
      exact p
    · intro q
      apply npq
      right
      exact q
  · intro npnq
    cases npnq with
    | intro np nq =>
      intro pq
      cases pq with
      | inl p =>
        exact np p
      | inr q =>
        exact nq q
