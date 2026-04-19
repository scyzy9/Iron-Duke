
-- # Tutorial 3: Predicate Logic

/-
## Quantifiers
-/

variable (A B C : Type)
         (P Q : A → Prop)
         (RR : A → A → Prop)
         (R : Prop)

open Classical
theorem raa : ¬¬R → R := by
  intro nnr
  cases (em R) with
  | inl r =>
    exact r
  | inr nr =>
    have f : False := by
      apply nnr
      exact nr
    cases f





-- ### Universals

example : (∀ x : A , P x ∧ Q x) → ∀ y : A, Q y  := by
  intro pxqx
  intro x
  have hpxqx : P x ∧ Q x := pxqx x
  cases hpxqx with
  | intro px qx =>
  exact qx



example (S : ∀ x, P x) (a : A) : P a := by
  exact S a


-- ### Existentials

example (a : A) : ∃ x, P x := by
  sorry

example : (∃ x : A, P x) → ∃ x : A, true := by
  intro px
  cases px with
  | intro a pa =>
    exists a


-- Exists commutes with disjunction
example : (∃ x:A , P x ∨  Q x) ↔ (∃ x:A, P x) ∨ (∃  x:A , Q x) := by
  constructor
  · intro pxqx
    cases pxqx with
    | intro x hpxqx =>
      cases hpxqx with
      | inl px =>
        left
        exists x
      | inr qx =>
        right
        exists x
  · intro pxqx
    cases pxqx with
    | inl px =>
      cases px with
      | intro x px =>
        exists x
        left
        exact px
    | inr qx =>
      cases qx with
      | intro x qx =>
        exists x
        right
        exact qx


-- DeMorgan 1 :
example : ¬ (∃ x : A , P x) ↔ ∀ x : A, ¬ P x := by
  constructor
  · intro npx
    intro x
    intro px
    apply npx
    exists x
  · intro npx
    intro px
    cases px with
    | intro x px =>
      have hnpx := npx x
      exact hnpx px


-- DeMorgan 2 : Requires Classical!
example : ¬ (∀ x : A, P x) ↔ ∃ x : A, ¬ (P x) := by
  constructor
  · intro npx
    apply raa
    intro nnpx
    apply npx
    intro x
    apply raa
    intro hnpx
    apply nnpx
    exists x
  · intro npx
    intro px
    cases npx with
    | intro x hnpx =>
      have hpx := px x
      exact hnpx hpx


/-
## Equality and Rewriting
-/
-- Prove equality using rfl
theorem reflexivity: ∀ x: A, x = x := by
  intro x
  rfl

-- prove using `rw [h]` or `rw [ ← h]`
example : ∀ x y z : A, x=y → y=z → x=z := by
  intro x y z
  intro xy yz
  rw[xy]
  exact yz


example : ∀ x y z : A, x=y → y=z → x=z := by
  intro x y z
  intro xy yz
  rw[←yz]
  exact xy

example : ∀ x y z : A, x=y → y=z → x=z := by
  sorry

example : ∀ x y z : A, x=y → y=z → x=z := by
  sorry


-- Which of these is intuitionistically provable?
example : ∀ x y z : A, ¬(x=y ∧ x=z) → (x≠y ∨ x≠z) := by
  intro x y z
  intro nxyxz
  cases em (x = y) with
  | inl xy =>
    right
    intro xz
    apply nxyxz
    constructor
    · assumption
    · assumption
  | inr xny =>
    left
    exact xny



example : ∀ x y z : A, ¬(x=y ∨ x=z) → (x≠y ∧ x≠z) := by
  intro x y z
  intro nxyxz
  constructor
  · intro xy
    apply nxyxz
    left
    exact xy
  · intro xz
    apply nxyxz
    right
    exact xz



example : ∀ x y z : A, ¬(x≠y ∨ x≠z) → (x=y ∧ x=z) := by
  intro x y z
  intro nxnyxnz
  cases em (x = y) with
  | inl xy =>
    cases em (x = z) with
    | inl xz =>
      constructor
      · assumption
      · assumption
    | inr xnz =>
      have f : False := by
         apply nxnyxnz
         right
         exact xnz
      cases f
  | inr xny =>
    have f : False := by
      apply nxnyxnz
      left
      exact xny
    cases f




-- ### Exercises with quantifiers

axiom Person : Type
axiom Male : Person -> Prop
axiom Female : Person -> Prop
axiom Parent : Person -> Person -> Prop
axiom Married : Person -> Person -> Prop
axiom Sibling : Person -> Person -> Prop

--
def Sister(x y : Person) : Prop
  := Female x ∧ Sibling x y

-- x has a brother
def hasBrother(x : Person) : Prop
  := ∃ b : Person , Male b ∧ Sibling b x

--  `x` has an uncle
def hasUncle(x : Person) : Prop
  := ∃ u  : Person, ∃ b : Person, Male u ∧ Parent u b ∧ Sibling b x

-- no one has a sibling who is their parent
def weird : Prop
  := ∀ x s p : Person ,(Sibling s x) ∧ (Parent p x) → s ≠ p

-- everybody has exactly two parents
def twoparents : Prop
  := ∃ a b x : Person, ∀ c : Person,(Parent a x) ∧ (Parent b x) ∧ (Parent c x) →  (c = a)∨(c = b)

-- there is somebody who doesn't have two parents
def notTwoParents : Prop
  := ∃ a x : Person, ∀ b : Person,(Parent a x)∧(Parent b x) → (a = b)

-- There is a person who is neither male nor female
def nonBinary : Prop
  := ∃ x : Person ,(¬ Female x)∧(¬ Male x)

/-
  Here's a challenge for anyone who is finished or wants a puzzle to do at home 🙂

  Hints
    1. you will need to exists `have`.
    2. I believe the proof is classical and `raa` was my friend here on *multiple* occasions!
    3. Do not "throw away" something which might later be exists-able (i.e. doing `left` or `right` too early).
-/
example : (∀ x y : Person, ¬Sibling x y ∨ ¬Parent y x) ↔ (∀ x y : Person, ¬(Sibling x y ∧ Parent y x)) := by
  sorry
