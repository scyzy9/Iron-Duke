/- COMP2065 (IFR) - Tutorial 4 -/

/- More on Predicate Logic & Equality -/

variable (A B : Type)
variable (P Q : Prop)
variable (PP QQ : A → Prop)
variable (R : A → B → Prop)

theorem ex0 : ∀ x y : A, x = y → PP x → PP y := by
  intro x y
  intro xy
  rw[xy]
  intro hy
  exact hy


theorem ex1 : ∀ x₁ x₂ : A, ∀ y₁ y₂ : B, x₁ = x₂ → y₁ = y₂ → R x₁ y₁ → R x₂ y₂ := by
  intro x1 x2 y1 y2
  intro x1x2 y1y2
  intro x1y1
  rw[←x1x2]
  rw[←y1y2]
  exact x1y1

theorem ex2 : (∃ _ : A, true) → (∀ x : A, PP x) → ∃ x : A, PP x := by
  intro tt
  intro ax
  cases tt with
  | intro x htt =>
    exists x
    have hppx := ax x
    exact hppx



theorem ex3 : (∀ x : A, PP x) → (a : A) → PP a := by
  intro ax
  intro a
  have ppx := ax a
  exact ppx

theorem ex4 : (∀ x : A , PP x ∧ QQ x) ↔ (∀ x : A, PP x) ∧ (∀ x : A, QQ x) := by
  constructor
  · intro appxqqx
    constructor
    · intro x
      have ppxqqx := appxqqx x
      cases ppxqqx with
      | intro ppx qqx =>
        exact ppx
    · intro x
      have ppxqqx := appxqqx x
      cases ppxqqx with
      | intro ppx qqx =>
        exact qqx
  · intro appxqqx
    cases appxqqx with
    | intro appx aqqx =>
      intro x
      have ppx := appx x
      have qqx := aqqx x
      constructor
      · exact ppx
      · exact qqx



theorem ex5 : (∃ x : A, PP x ∨  QQ x) ↔ (∃ x : A, PP x) ∨ (∃ x : A, QQ x) := by
  constructor
  · intro eppxqqx
    cases eppxqqx with
    | intro x ppxqqx =>
      cases ppxqqx with
      | inl ppx =>
        left
        exists x
      | inr qqx =>
        right
        exists x
  · intro eppxeqqx







axiom Person : Type
axiom Male : Person -> Prop
axiom Female : Person -> Prop
axiom Parent : Person -> Person -> Prop
axiom Married : Person -> Person -> Prop
axiom Sibling : Person -> Person -> Prop

-- x is the sister of y
def Sister(x y : Person) : Prop
  := sorry

-- x has a brother
def hasBrother(x : Person) : Prop
  := sorry

--  x has an uncle
def hasUncle(x : Person) : Prop
  := sorry

-- no one has a sibling who is their parent
def weird : Prop
  := sorry

-- everybody has exactly two parents
def twoparents : Prop
  := sorry

/- (Classical) challange -/

open Classical

example : (∀ x y : Person, ¬Sibling x y ∨ ¬Parent y x) ↔ (∀ x y : Person, ¬(Sibling x y ∧ Parent y x)) := by
  sorry
