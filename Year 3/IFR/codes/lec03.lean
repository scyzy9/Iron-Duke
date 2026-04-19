variable {P Q R : Prop}

--P → Q
--prove
example : P → Q → P∧Q := by
  intro p
  intro q
  constructor
  . exact p
  . exact q

--use
example : P ∧ Q → P := by
  intro pq
  cases pq with
  | intro p q =>
    assumption

-- a curry theorem
-- P → Q → R
-- P ∧ Q → R
theorem curry : P → Q → R ↔ P ∧ Q → R := by
  constructor
  . intro pqr
    intro pq
    apply pqr
    .cases pq with
    | intro p q =>
      assumption
    .cases pq with
    | intro p q =>
      assumption
  . intro pqr
    intro p q
    apply pqr
    constructor
    . assumption
    . assumption


--e.g.2
theorem curry2 : P → Q → R ↔ P ∧ Q → R := by
  constructor
  . intro pqr
    intro pq
    cases pq with
    | intro p q =>
      apply pqr
      . exact p
      . exact q
  . intro pqr
    intro p q
    apply pqr
    constructor
    . exact p
    . exact q

--P ∨ Q
--prove with left and right
example : P → P ∨ Q := by
  intro p
  left
  exact p

example : (P → R) → (Q → R) → (P ∨ Q → R) := by
  intro pr qr pq
  cases pq with
  | inl p =>
    apply pr
    assumption
  | inr q =>
    apply qr
    assumption


theorem distr : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by
  apply Iff.intro
  . intro h
    cases h with
    | intro p qr =>
      cases qr with
      | inl q =>
        left
        constructor
        .exact p
        .exact q
      | inr r =>
        right
        constructor
        assumption
        assumption
  . intro h
    cases h with
    | inl pq =>
      cases pq with
      | intro p q =>
        constructor
        .exact p
        .left;exact q
    | inr r =>
      cases r with
      | intro p r =>
        constructor
        .exact p
        .right;exact r
