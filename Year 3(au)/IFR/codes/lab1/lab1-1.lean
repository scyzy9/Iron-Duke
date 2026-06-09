-- Welcome to the COMP2065 (IFR) Tutorial!
--
-- Download today's tutorial from Teams `COMP2065-IFR 2025-26`
-- from the channel `Tutorials - Warren`.
--
--Proof
-- ∧ constructor
-- ∨ left/right
-- →  intro + exact/assumption
--Use
-- ∧ cases a with
--       | intro p q =>
-- ∨ cases a with
--       | inl p =>
--       | inr q =>
-- → apply/assumption

/-
 -- Tutorial #1: Part 1
 -/
variable (P Q R : Prop)

/- demo -- `intro`, `apply`, and `exact` -/

example : P → P → P := by
    intro p
    intro p1
    exact p

/- demo -- `constructor` and `cases` -/

example : P → Q → Q ∧ P := by
  intro p
  intro q
  constructor
  · exact q
  · exact p

example : P ∧ Q → P → Q := by
  intro pq
  intro p
  cases pq with
  | intro p1 q1 =>
    exact q1

/- exercises - propositional basics: `apply` and `exact` -/

-- this is the same as : P -> (Q -> (Q -> P)) :=
theorem ex1 : P → Q → Q → P := by
  intro p
  intro q
  intro q1
  exact p

-- this is the same as: P -> ((P -> Q) -> Q) :=
theorem ex2 : P → (P → Q) → Q := by
  intro p
  intro pq
  have q : Q := pq p
  exact q

theorem ex3 : P ∧ Q → Q → P := by
  intro pq
  intro q
  cases pq with
  | intro p1 q1 =>
    exact p1

theorem ex4 : (P ∧ Q) → (Q ∧ P) → Q → P := by
  intro pq
  intro qp
  intro q
  cases pq with
  | intro p1 q1 =>
    exact p1

theorem ex5 : (P ∧ Q) ↔ (Q ∧ P) := by
  constructor
  · intro pq
    cases pq with
    | intro p1 q1 =>
      constructor
      · exact q1
      · exact p1
  ·intro qp
   cases qp with
   | intro q1 p1 =>
     constructor
     · exact p1
     · exact q1

/-
 -- Tutorial #1: Part 2
 -/

/- demo -- `left` and `right` -/

example : P → P ∨ Q := by
  intro p
  left
  exact p


example : Q → P ∨ Q := by
  intro q
  right
  exact q

/- exercises -/

theorem ex6 : P ∧ Q → P ∨ Q := by
  intro pq
  cases pq with
  | intro p1 q1 =>
    right
    exact q1

theorem ex7 : P ∧ Q ↔ Q ∧ P := by
  constructor
  · intro pq
    cases pq with
    | intro p1 q1 =>
      constructor
      · exact q1
      · exact p1
  · intro qp
    cases qp with
    | intro q1 p1 =>
      constructor
      · exact p1
      · exact q1


theorem ex8 : P ∨ Q ↔ Q ∨ P := by
  constructor
  · intro pq
    cases pq with
    | inl p1 =>
      right
      exact p1
    | inr q1 =>
      left
      exact q1
  · intro qp
    cases qp with
    | inl q1 =>
      right
      exact q1
    | inr p1 =>
      left
      exact p1



theorem ex9 : (P → R) → (Q → R) → P ∨ Q → R := by
  intro pr
  intro qr
  intro pq
  cases pq with
  | inl p1 =>
    have r : R := pr p1
    exact r
  | inr q1 =>
    have r : R := qr q1
    exact r

/-
 -- End of tutorial #1 exercises 🍰 --
 -/

-- Here is an additional exercise for anyone who wants a challenge!
theorem ex10 : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by
  constructor
  · intro pqr
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
  · intro pqpr
    cases pqpr with
    | inl pq =>
      cases pq with
      | intro p q =>
        constructor
        · exact p
        · left
          exact q
    | inr pr =>
      cases pr with
      | intro p r =>
        constructor
        · exact p
        · right
          exact r
