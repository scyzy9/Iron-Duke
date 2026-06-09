/-

Lecture 05 : Classical logic

-/

variable {P Q R : Prop}

-- de Morgan rules

theorem dm1 : ¬ (P ∨ Q) ↔ (¬ P) ∧ (¬ Q) := by
  constructor
  . intro npq
    constructor
    . intro p
      apply npq
      left
      assumption
    . intro q
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


open Classical

#check em
-- excluded middle
-- tertium non datur
-- omniescience, Bishop

theorem dm2 : ¬ (P ∧ Q) ↔ (¬ P) ∨ (¬ Q) := by
  constructor
  . intro npq
    have pnp : P ∨ ¬ P := by
      apply em
    cases pnp with
    | inl p =>
        right
        intro q
        apply npq
        constructor
        . assumption
        . assumption
    | inr np =>
        left
        assumption
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
/-
Intuitionistic logic - logic of evidence
Classical logic - logic of truth

¬ (P ∧ Q) → ¬ P ∨ ¬ Q
P = I have dogs
Q = I have cats

If I dont have dogs and cats
then I don't have dogs or I don't have cats

-/

/-
Alternative to em :
proof by contradiction
(¬ P → False) → P
¬ ¬ P → P
reductio ad adsurdum
-/

theorem byContradiction : ¬ ¬ P → P := by
  intro nnp
  have pnp : P ∨ ¬ P := by
     apply em
  cases pnp with
  | inl p =>
      assumption
  | inr np =>
      have pcf : False := by
        apply nnp
        assumption
      cases pcf

#check Classical.byContradiction

-- em → byContradiction
-- byContradiction → em

-- ¬ ¬ (P ∨ ¬ P)
-- should be called excluded midddle

theorem nnem : ¬ ¬ (P ∨ ¬ P) := by
  intro npnp
  apply npnp
  right
  intro p
  apply npnp
  left
  assumption

theorem em' : P ∨ ¬ P := by
  apply Classical.byContradiction
  apply nnem
/-
False = Gold
P = philosophers stone

P ∨ ¬ P

-/

/-
logic poker
P : Prop
provable intuitionistically
provable classically
unprovable

Why do we want to avoid em (or byContradiction) ?

- philosophical
  Plato

- pragmatic
  constructive
  exists a number

-/
