/-
Introduction to Formal Reasoning (Comp 2065)
Tutorial 02: Propositional logic-part2
Date: 16 Oct 2025
TA: Aref Mohammadzadeh
You can download tutorial files from moodle `Tutorials -> Aref`.
-/

-------------------------------------------------
--section1:

/-
This week we have four goals:

1. Understand what it means when we say a proposition P can be proved in:

     - Constructive Logic
     - Classical Logic

2. Prove more constructive propositions using the `have` tactic.

3. Prove some classical propositions and understand
   why they cannot be proved constructively.

4. How to prove that a proposition is not provable.
   Can Lean help us for this?
-/

variable {P Q R S : Prop}
open Classical




--Constructive or Classical?
theorem ex1 : (P → ¬ Q) → (Q → ¬P) := by
  intro pnq
  intro q
  intro p
  have nq := pnq p
  exact nq q



-- Double Negation Introduction:
theorem ex2_doubleNegIntro : P → ¬¬P := by
  intro p
  intro np
  exact np p



-- Double Negation Elimination:
theorem ex3_doubleNegElim : ¬¬P → P := by
  exact byContradiction




-- Is this classical or constructive?
theorem ex4 : (P → Q) ∨ (Q → P) := by
  cases em P with
  | inl p =>
    right
    intro q
    exact p
  | inr np =>
    left
    intro p
    cases np p


-- what about this one?
theorem ex5 : (P → Q → P) → P → Q := by
 sorry


--ex

theorem ex6 : (P → Q) → ¬¬P → ¬¬Q := by
  intro pq
  intro nnp
  intro nq
  have p := byContradiction nnp
  have q := pq p
  exact nq q

--ex
theorem ex7 : ¬ (P → ¬P) ↔ ¬¬P := by
  constructor
  · intro npnp np
    apply npnp
    intro p
    exact np
  · intro nnp
    intro pnp
    apply nnp
    intro p
    have np := pnp p
    exact np p









----------------------------------------------
-- section2
-- Double negation elimination and the law of excluded middle are
-- equivalent to each other.

theorem ex8 : (P ∨ ¬P) → (¬¬P → P) := by
  intro pnp nnp
  have p := byContradiction nnp
  exact p


-- Question: Is there any constructive proof for (¬¬P → P) → (P ∨ ¬P)?
-- Can you prove the following proposition?
-- theorem ex9' : (¬¬P → P) → (P ∨ ¬P)  := by


-- However, you can do this one:
theorem ex9 : (¬¬P → P) → ¬¬ (P ∨ ¬P)  := by
  intro nnp
  intro npnp
  have pnp := em P
  exact npnp pnp



-- So what it means when we say LEM and DNE are equivalent?
-- Think about it first, but you can find the answer in the solution.


--------------------------
-- The following classically valid proposition is called Peirce's law.
-- It can be proved that it is equivalent to the law of excluded middle,
-- Therefore it is not constructive.
theorem ex10 : ((P → Q) → P) → P := by
  intro pqp
  apply pqp
  intro p
  exact pqp p

-------------------------
