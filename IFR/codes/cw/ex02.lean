/-
COMP2065-IFR Exercise 02
-/
--import AutograderLib
namespace poker

variable (P Q R : Prop)

inductive PokerAnswer : Type
| UNANSWERED : PokerAnswer
| NotProvable : PokerAnswer
| Intuition : PokerAnswer
| Classical : PokerAnswer
open PokerAnswer

open Classical
/- --- Do not add/change anything above this line --- -/

/-
We play the game of logic poker :-)

  You have to classify each proposition as either
  a) provable intuitionistically (i.e. in plain lean)
  b) provable classically (using em : P ∨ ¬ P or byContradiction : ¬¬ P → P).
  c) not provable classically.
  and then you have to prove the propositions in a) and b) accordingly.

  You will start with a score of 10 points and then 1 point will be deducted
  for each incorrect classification and 1 point will be deducted for each
  incorrect proof. We stop deducting at zero so you cannot earn negative points.
  So for instance if you do every proof correctly but do not classify anything
  you will earn 0/10.
-/

/-
CLASSIFICATION: For each proposition replace UNANSWERED with
  Intuition     if the proposition is provable intuitionistically (i.e. in plain lean)
  Classical     if the proposition is provable classically (using em : P ∨ ¬ P or byContradiction : ¬¬ P → P)
  NotProvable   if the proposition is not provable classically

**Important**: Every classification should be one of these three or UNANSWERED.
DO NOT put anything else on the right-hand side or leave it totally blank.

Examples:                                  -/
-- q00 : P → P
def answer00 : PokerAnswer := Intuition

-- q00' : ¬¬P → P
def answer00' : PokerAnswer := Classical

-- q00'' : false
def answer00'' : PokerAnswer := NotProvable

/-
PROOFS:
  Then prove the propositions you classified as 'Intuition' or 'Classical'.
  For the 'Classical' ones you may use em or byContradiction as discussed in lecture.
  For propositions classified as 'NotProvable' just keep "sorry" as the proof.

  You are only allowed to use the tactics introduced in the lecture
  (e.g. intro exact apply constructor cases left right have)

  Please only use the tactics in the way indicated in the lecture notes
  otherwise we may deduct points.
-/

--@[autogradedDef 1]
def answer01 : PokerAnswer  := Intuition
--@[autogradedProof 1]
theorem q01 : (P → Q ∧ R) ↔ (P → Q) ∧ (P → R) := by
  constructor
  · intro h
    constructor
    · intro p
      have qr := h p
      cases qr with
      | intro q r =>
        exact q
    · intro p
      have qr := h p
      cases qr with
      | intro q r =>
        exact r

  · intro h p
    constructor
    · exact h.left p
    · exact h.right p





--@[autogradedDef 1]
def answer02 : PokerAnswer  := Classical
--@[autogradedProof 1]
theorem q02 : (P → Q) → ¬ P ∨ Q := by
  classical
  intro pq
  cases em P with
  | inl p =>
    right
    exact pq p
  | inr np =>
    left
    exact np

--@[autogradedDef 1]
def answer03 : PokerAnswer  := Intuition
--@[autogradedProof 1]
theorem q03 : (¬ P ∨ Q) → P → Q := by
  intro npq p
  cases npq with
  | inr q =>
    exact q
  | inl np =>
    cases np p



--@[autogradedDef 1]
def answer04 : PokerAnswer  := Classical
--@[autogradedProof 1]
theorem q04 : ¬ (P ↔ ¬ P) := by
  intro pnp
  cases em P with
  | inl p =>
    cases pnp with
    | intro f g =>
        have np : ¬ P := f p
        exact np p
  | inr np =>
    cases pnp with
    | intro f g =>
      have p := g np
      exact np p



--@[autogradedDef 1]
def answer05 : PokerAnswer  := Classical
--@[autogradedProof 1]
theorem q05 : ¬ ¬ (P ∧ Q) ↔ ¬ ¬ P ∧ ¬ ¬ Q := by
  classical
  constructor
  · intro nnpq
    constructor
    · intro np
      apply nnpq
      intro pq
      cases pq with
      | intro p q =>
        exact np p
    · intro nq
      apply nnpq
      intro pq
      cases pq with
      | intro p q =>
        exact nq q
  · intro nnpnnq
    cases nnpnnq with
    | intro nnp nnq =>
      have p := byContradiction nnp
      have q := byContradiction nnq
      intro npq
      apply npq
      constructor
      . exact p
      . exact q                       --

--@[autogradedDef 1]
def answer06 : PokerAnswer  := Classical
--@[autogradedProof 1]
theorem q06 : ¬ ¬ P ∨ ¬ ¬ Q ↔ ¬ ¬ (P ∨ Q) := by
  classical
  constructor
  · intro nnpnnq
    intro npq
    cases nnpnnq with
    | inl nnp =>
      have p := byContradiction nnp
      apply npq
      left
      assumption            --
    | inr nnq =>
      have q := byContradiction nnq
      apply npq
      right
      assumption
  · intro nnpq
    cases em P with
    | inl p =>
      left
      intro np
      exact np p
    | inr np =>
      right
      intro nq
      apply nnpq
      intro pq
      cases pq with
      | inl p =>
        exact np p
      | inr q =>
        exact nq q


--@[autogradedDef 1]
def answer07 : PokerAnswer  := Classical
--@[autogradedProof 1]
theorem q07 : (P → ¬ ¬ Q) ↔ ¬ ¬ (P → Q) := by
  classical
  constructor
  · intro pnnq
    intro npq
    have h : P → Q := by
      intro p
      exact byContradiction (pnnq p)
    exact npq h
  · intro nnpq p
    intro nq
    apply nnpq
    intro pq
    have q := pq p
    exact nq q


--@[autogradedDef 1]
def answer08 : PokerAnswer  := Intuition
--@[autogradedProof 1]
theorem q08 : ¬ P ↔ ¬ ¬ ¬ P := by
  constructor
  · intro np nnp
    exact nnp np
  · intro nnnp p
    have nnp : ¬ ¬ P := by
      intro np
      exact np p
    exact nnnp nnp

--@[autogradedDef 1]
def answer09 : PokerAnswer  := NotProvable
--@[autogradedProof 1]
theorem q09 : (P → Q) → R ↔ P → (Q → R) := by
  sorry

--@[autogradedDef 1]
def answer10 : PokerAnswer  := UNANSWERED
--@[autogradedProof 1]
theorem q10 : ((P ↔ Q) ↔ R) ↔ (P ↔ (Q ↔ R)) := by
  constructor
  · intro h
    constructor
    · intro p
      constructor
      · intro q







--- Do not add/change anything below this line ---
end poker
