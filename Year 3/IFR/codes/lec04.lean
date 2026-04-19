/-

Lecture 04 : Propositional logic

-/

variable {P Q R : Prop}

example : True := by
  constructor

-- P ∧ True ↔ P

-- ex falso quod libet
-- from false everything follows

theorem efq : False → P := by
  intro pcf
  cases pcf

example : ¬ (P ∧ ¬ P) := by
  intro pnp
  cases pnp with
  | intro p np =>
      apply np
      assumption

---
--- cut (have)

theorem double_or : R ∨ R → R := by
  intro rr
  cases rr with
  | inl r =>
      assumption
  | inr r =>
      assumption

example : (P → Q ∨ Q) → P → Q := by
  intro h p
  apply double_or
  apply h
  assumption

example : (P → Q ∨ Q) → P → Q := by
  intro pqq p
  have qq := pqq p
  cases qq with
  | inl q =>
    assumption
  | inr q =>
    assumption

-- Gentzen, cut elimination

-- de Morgan rules

theorem dm1 : ¬ (P ∨ Q) ↔ (¬ P) ∧ (¬ Q) := by
  constructor
  · intro npq
    constructor
    · intro p
      apply npq
      left
      assumption
    · intro q
      apply npq
      right
      assumption
  . intro npnq pq
    cases npnq with
    | intro np nq =>
        cases pq with
        | inl p =>
           apply np
           assumption
        | inr q =>
          apply nq
          assumption




theorem dm2 : ¬ (P ∧ Q) ↔ (¬ P) ∨ (¬ Q) := by
  constructor
  . intro npq
    right
    intro q
    apply npq
    constructor
    . sorry
    . assumption
  . intro npnq pq
    cases pq with
    | intro p q =>
        cases npnq with
        | inl np =>
            apply np
            assumption
        | inr nq =>
            apply nq
            assumption
