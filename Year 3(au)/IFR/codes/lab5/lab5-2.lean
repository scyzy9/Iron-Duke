/- COMP2065 (IFR) - Tutorial 5 -/

namespace tutorial5

/- (Finite) Inductive Types & Functions -/

inductive Empty : Type

inductive Unit : Type
| unit : Unit

inductive Bool' : Type
| true' : Bool'
| false' : Bool'

def not' : Bool → Bool
| true => false
| false => true

def and' : Bool → Bool → Bool
| true , b => b
| false, _ => false

def or' : Bool → Bool → Bool
| true , _ => true
| false , b => b

/- Tactic : contradiction -/

example : true ≠ false := by
  intro h
  contradiction

/- ex0 : define 'eq' on Bool -/
def eq : Bool → Bool → Bool
  | true , b => b
  | false , b => !b

/- ex1 : finish the proof using 'apply Exists.intro ...' , instead of 'exists' -/
theorem ex1 : ∃ x y : Bool, x ≠ y ∧ ∀ z : Bool, x = z ∨ y = z := by
  apply Exists.intro true
  apply Exists.intro false
  constructor
  . intro h
    cases h
  . intro z
    cases z with
    | false =>
      right
      rfl
    | true =>
      left
      rfl

/- ex2 : define an inductive type with exactly 3 terms -/
inductive Colour : Type
| red : Colour
| green : Colour
| blue : Colour

open Colour

/- ex3 : state that this type has exactly 3 terms -/
theorem ex3 : True /- TODO -/ := by
  constructor


/- Relating Boolean and Propositions -/

def isTrue : Bool → Prop
| b => b = true

/- Tactic : dsimp [...], dsimp [...] at ... -/

example : ∀ b : Bool, isTrue (true || b) := by
  intro b
  cases b with
  | false =>
    rfl
  | true =>
    rfl

theorem ex4 : ∀ b : Bool, ¬ isTrue (false && b) := by
  intro b
  intro h
  cases b with
  | false =>
    cases h
  | true =>
    cases h

theorem ex5 : ∀ b : Bool, isTrue (b || ! b) := by
  intro b
  cases b with
  | false =>
    rfl
  | true =>
    rfl

theorem ex6 : ∀ x y : Bool, isTrue (eq x y) ∨ ¬ isTrue (eq x y) := by
  intro x y
  cases x with
  | false =>
    cases y with
    | false =>
      left
      rfl
    | true =>
      right
      intro h
      cases h
  | true =>
    cases y with
    | false =>
      right
      intro h
      cases h
    | true =>
      left
      rfl


theorem not_ok : ∀ b : Bool, isTrue (! b) ↔ ¬ isTrue b := by
  intro b
  constructor
  . intro h tb
    cases b
    . dsimp [isTrue] at tb
      cases tb
    . dsimp [not, isTrue] at h
      cases h
  . intro ntb
    cases b
    . dsimp [not, isTrue]
    . dsimp [not, isTrue]
      contradiction




theorem or_ok : ∀ b c : Bool, isTrue (b || c) ↔ isTrue b ∨ isTrue c := by
  intro b c
  constructor
  . intro h1
    dsimp[isTrue]
    dsimp[isTrue] at h1
    cases b with
    | false =>
      cases c with
      | false =>
        cases h1
      | true =>
        right
        rfl
    | true =>
      left
      rfl
  . intro h1
    dsimp[isTrue]
    dsimp[isTrue] at h1
    cases b with
    | false =>
      cases c with
      | false =>
        cases h1 with
        | inl h2 =>
          cases h2
        | inr h3 =>
          cases h3
      | true =>
        rfl
    | true =>
      cases c with
      | false =>
        rfl
      | true =>
        rfl
