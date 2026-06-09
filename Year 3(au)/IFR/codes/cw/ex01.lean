/-
COMP2065-IFR
Exercise 01 (10 points)

Prove all the following propositions in Lean. 1 point per exercise.
That is replace "sorry" with your proof.

You are only allowed to use the tactics introduced in the lecture
(i.e. assume, exact, apply, constructor, cases, left, right, have)
and only in the way we have introduced them.

You can use auxilliary theorems (lemmas) which you need to prove
as well. Indeed this is good practice where appropriate.

-/
--import AutograderLib
namespace proofs

variable (P Q R : Prop)

/- --- Do not add/change anything above this line --- -/

--@[autogradedProof 1]
theorem q01 : (P → P → Q) → (P → Q) := by
  intro h p
  exact h p p


--@[autogradedProof 1]
theorem q02 : (P → Q) → (P → P → Q) := by
  intro h p p2
  exact h p

--@[autogradedProof 1]
theorem q03 : (P → P → Q) ↔ (P → Q) := by
  constructor
  · intro h p
    exact h p p
  · intro h p p2
    exact h p


--@[autogradedProof 1]
theorem q04 : P ∧ True ↔ P := by
  constructor
  · intro h
    cases h with
    | intro p t =>
      exact p

  · intro p
    constructor
    · exact p
    constructor


--@[autogradedProof 1]
theorem q05 : (P ∧ Q) ∧ R ↔ P ∧ (Q ∧ R) := by
  constructor
  · intro h
    cases h with
    | intro pq r =>
      cases pq with
      | intro p q =>
        constructor
        · exact p
        · constructor
          · exact q
          · exact r

  · intro h
    cases h with
    | intro p qr =>
      cases qr with
      | intro q r =>
        constructor
        · constructor
          · exact p
          · exact q
        · exact r

--@[autogradedProof 1]
theorem q06 : P ∨ false ↔ P := by
  constructor
  · intro h
    cases h with
    | inl p =>
      exact p
    | inr f =>
      cases f
  · intro p
    left
    exact p

--@[autogradedProof 1]
theorem q07 : (P ∨ Q) ∨ R ↔ P ∨ (Q ∨ R) := by
  constructor
  · intro h
    cases h with
    | inl pq =>
      cases pq with
      | inl p =>
        left
        exact p
      | inr q =>
        right
        left
        exact q
    | inr r =>
      right
      right
      exact r
  · intro h
    cases h with
    | inl p =>
      left
      left
      exact p
    | inr qr =>
      cases qr with
      | inl q =>
        left
        right
        exact q
      | inr r =>
        right
        exact r


--@[autogradedProof 1]
theorem q08 : (P ↔ Q) ↔ (Q ↔ P) := by
  constructor
  · intro h
    cases h with
    | intro hpq hqp
    constructor
    intro q
    exact hqp q
    intro p
    exact hpq p
  · intro h
    cases h with
    | intro hqp hpq
    constructor
    intro p
    exact hpq p
    intro q
    exact hqp q


--@[autogradedProof 1]
theorem q09 : (P ↔ Q) → ((P → R) ↔ (Q → R)) := by
  intro h
  cases h with
  | intro hpq hqp =>
    constructor
    · intro hPR
      intro q
      have p : P := hqp q
      exact hPR p
    · intro hQR
      intro p
      have q : Q := hpq p
      exact hQR q

--@[autogradedProof 1]
theorem q10 : (P ∨ Q ↔ P ∧ Q) ↔ (P ↔ Q) := by
  constructor
  · intro h
    cases h with
    | intro hOrToAnd hAndToOr =>
      constructor
      --> P → Q
      · intro p
        have pq : P ∨ Q := by
          left
          exact p
        have hpq : P ∧ Q := hOrToAnd pq
        cases hpq with
        | intro _ hq =>
          exact hq
      --> Q → P
      · intro q
        have pq : P ∨ Q := by
          right
          exact q
        have hpq : P ∧ Q := hOrToAnd pq
        cases hpq with
        | intro hp _ =>
          exact hp
  · intro h
    cases h with
    | intro hpq hqp =>
      constructor
      · intro hOr
        cases hOr with
        | inl p =>
          have q : Q := hpq p
          constructor
          · exact p
          · exact q
        | inr q =>
          have p : P := hqp q
          constructor
          · exact p
          · exact q
      · intro hAnd
        cases hAnd with
        | intro p q =>
          right
          exact q





/- --- Do not add/change anything below this line --- -/
end proofs
