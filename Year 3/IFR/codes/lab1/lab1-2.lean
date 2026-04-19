/-
# Tutorial 1: Intro to Lean ─ Propositional Reasoning

-- 1. Write ∧, ∨, →, ↔, ¬, in English.

-- 2. if Q is false, and P is true, what is Q → P?

-- 3. For each set, write the one which is *not* a lean teactic:
    1. intro, constructor, destructor, right
    2. assumption, assume, have, cases

-- 4. Convert the following sentence into symbols:
     "If P and Q are both true, then either R is true or T is false"

-/

variable (P Q R S T U V W X : Prop)

section s1
  theorem s1ex1 : P → Q → P := by
    intro p q
    assumption


  theorem s1ex2 :  (P ∨ Q) → (P ∧ Q) → (R → Q) → (P ∧ Q) := by
    intro p_or_q p_and_q rq
    assumption

  theorem s1ex3 : P → Q → Q → P := by
    intro p q1 q2
    assumption

  theorem s1ex4 : P → (P → Q) → Q := by
    intro p pq
    apply pq
    assumption

end s1

section s2
  theorem s2ex1 : P → Q ∧ P → Q := by
    intro p qp
    cases qp with
    | intro q p1 =>
      exact q


  theorem s2ex2 : (P ∧ Q) → (Q ∧ P) → Q → P := by
    intro pq qp q
    cases pq with
    | intro p1 q1 =>
      exact p1

  theorem s2ex3 : P ∧ Q → Q ∧ P := by
    intro pq
    cases pq with
    | intro p q =>
      constructor
      · exact q
      · exact p

  theorem s2ex4 : P ∧ Q → P ∨ Q := by
    intro pq
    cases pq with
    | intro p q =>
      left
      exact p

  theorem s2ex5 : (P → R) → (Q → R) → P ∨ Q → R := by
    intro pr qr pq
    cases pq with
    | inl p =>
      apply pr
      exact p
    | inr q =>
      apply qr
      exact q
end s2

section MAZES!
-- This is the maze section
theorem maze1 : P → Q → P ∧ Q ∧ (P ∧ Q ∧ Q) ∧ (P ∧ Q) := by
  sorry

theorem maze2 : (P ∧ ((P ∧ Q) ∧ P) ∧ P ∧ P ∧ P) ∧ (P ∧ P) ∧ P → Q := by
  sorry

theorem maze3 : P → (Q ∨ Q ∨ (Q ∨ (Q ∨ Q ∨ P) ∨ Q ∨ Q)) := by
  sorry

theorem maze4 : (X → R) → (X → V) → (R → U) → (V → W) → (V → Q) → (U → P) → (Q → S) → (P → T) → (S → T) →  R → T := by
  sorry

/-=======================================
CHALLENGE:

Create your own maze!
Combine some of the previous ideas
you have propositions P Q R S T U V W X : Prop at your disposal.

Give it to the person next to you and make them try and solve it

use the followng template, and fill in where it says "MAZE" with your own maze.

theorem my_maze : MAZE := by
  sorry

=========================================-/
end MAZES!

section s3
  theorem s3ex1 : (P ∧ Q) ↔ (Q ∧ P) := by
    constructor
    · intro pq
      cases pq with
      | intro p q =>
        constructor
        · exact q
        · exact p
    · intro qp
      cases qp with
      | intro q p =>
        constructor
        · exact p
        · exact q

  theorem s3ex2 : P ∨ Q ↔ Q ∨ P := by
    constructor
    · intro pq
      cases pq with
      | inl p =>
        right
        exact p
      | inr q =>
        left
        exact q
    · intro qp
      cases qp with
      | inl q =>
        right
        exact q
      | inr p =>
        left
        exact p

  theorem s3ex3 : P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R) := by
    intro pqr
    cases pqr with
    | intro p qr =>
      cases qr with
      | inl q =>
        left
        constructor
        · exact p
        · exact q
      | inr r =>
        right
        constructor
        · exact p
        · exact r

  theorem s3ex4 : ¬(P ∨ Q) → ¬ P := by
    intro n_pq p
    apply n_pq
    left
    exact p



  theorem s3ex5  : (P → Q) → ¬Q → ¬P := by
    intro pq nq p
    apply nq
    apply pq
    exact p


  theorem s3ex6 : P → True := by
    intro p
    trivial


  theorem s3ex7 : ¬¬¬P ↔ ¬P := by
    constructor
    · intro nnnp p
      apply nnnp
      intro np
      exact np p
    · intro np nnnp
      apply nnnp
      exact np


  theorem s3ex8 : (P → Q) ↔ (P ∧ P → Q) := by
    sorry

  theorem s3ex9 : ¬P → P → False := by
    sorry

  -- HINT: Use have!
  theorem s3ex10 : ¬P → (P → Q) := by
    sorry

  theorem s3ex11 : (P ∨ Q → R) ↔ (P → R) ∧ (Q → R) := by
    sorry
end s3
