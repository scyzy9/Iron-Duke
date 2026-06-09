
/-
Introduction to Formal Reasoning (Comp 2065)
Tutorial 05: The Booleans
Date: 06 Nov 2025
TA: Aref Mohammadzadeh
You can download tutorial files from moodle `Tutorials -> Aref`.

-/

/-
## Tactics for today:
- `dsimp [_]`  and `dsimp [_] at _`
-  And again, `cases`, this time for `Bool`

-/


--def not : Bool → Bool
-- | true  => false
-- | false => true

-- def and : Bool → Bool → Bool
-- | true, b  => b
-- | false, _ => false

-- def or : Bool → Bool → Bool
-- | true, _  => true
-- | false, b => b

-------------------------------------------------
namespace tuorial05
/-
# Part I : Underestanding Booleans
-/
theorem ex1 : ∀ x : Bool, (x && true) = x := by
  intro x
  cases x
  rfl
  rfl

-- Prove or disprove:
def Ex2 := ∀ x : Bool, ∃ y : Bool, (x && y) = false

theorem ex2 : Ex2 := by
  intro x
  cases x
  exists false
  exists false
-- Prove or disprove:
def Ex3 := ∃ x : Bool, (x && x) = (! x || ! x)

theorem ex3 : ¬ Ex3 := by
  intro h
  cases h with
  | intro x hx =>
    cases x
    dsimp [or,and,not] at hx
    cases hx
    dsimp [or,and,not] at hx
    cases hx

--Prove or disprove:
def Ex4 := (∀ x y z : Bool, (x && (y || z)) = ((x || y) && (x || z)))

theorem ex4 : ¬ Ex4 := by
  intro h
  have ftt := h false true true
  cases ftt

theorem ex5 : ¬(∀ x y : Bool, ∃ z : Bool, (x && y) = (x || z)) := by
  intro h
  have tf := h true false
  dsimp[and,or] at tf
  cases tf with
  | intro z h1 =>
    cases h1


theorem ex6 : ∀ x : Bool,  ∃ y : Bool, y ≠ x ∧ (∀ z : Bool, z = x ∨ z = y) := by
  intro x
  cases x
  exists true
  exists false


-------------------------------------------
/-
# Part II : From Bool to Prop:
-/

def isTrue : Bool → Prop
| b => b = true


theorem ex7 : ∀ b : Bool, isTrue (true || b) := by
  intro b
  dsimp [isTrue]
  cases b
  rfl
  rfl

theorem ex8 : ∀ b : Bool, ¬ isTrue (false && b) := by
  intro b
  intro h
  dsimp [isTrue,and] at h
  cases h



theorem ex9 : ∀ x : Bool, ∃ y : Bool, (isTrue (x || y) ∧ isTrue (x && y)) ↔ isTrue x := by
  intro x
  apply Exists.intro true
  constructor
  intro h
  dsimp [isTrue] at h
  cases x
  cases h with
  | intro hl hr =>
    cases hr
  dsimp [isTrue]
  intro h
  dsimp [isTrue] at h
  cases x
  cases h
  dsimp [isTrue,or,and]
  constructor
  · rfl
  · rfl





theorem ex10  : ∀ a b : Bool, isTrue (a || b) ↔ isTrue a ∨ isTrue b := by
  intro a b
  constructor
  intro h
  dsimp [isTrue]
  cases a
  cases b
  dsimp [isTrue,or] at h
  cases h
  right
  rfl
  left
  rfl
  intro h
  dsimp [isTrue] at h
  dsimp [isTrue]
  cases a
  cases b
  cases h with
  | inl hft =>
    cases hft
  | inr ft =>
    dsimp [or]
    cases ft
  rfl
  cases b
  rfl
  rfl





-- Challenging question for home:
theorem ex11 (f : Bool → Bool) : isTrue (f true && f false)
                              ↔ (∀ x : Bool, isTrue (f x)) := by
    constructor
    intro h
    intro x
    cases x
    cases hf : f false
    cases ht : f true
    rw [ht] at h
    cases h
    rw [ht, hf] at h
    cases h
    rfl
    cases ht : f true
    rw [ht] at h
    cases h
    rfl
    intro h
    have ht := h true
    have hf := h false
    cases ht' : f true
    rw [ht'] at ht
    cases ht
    cases hf' : f false
    rw [hf'] at hf
    cases hf
    rfl
