--bool-empty
set_option linter.unusedVariables false
-- inductive Empty : Type
example : ∀ x : Empty, False := by
  intro xe
  cases xe

inductive Singleton' : Type
| void : Singleton'
export Singleton' (void)

example : ∃ x : Singleton', ∀ y : Singleton', x = y := by
  exists void
  intro yS
  cases yS
  rfl

--Booleans

-- inductive Bool : Type
-- | false : Bool
-- | true : Bool

example : true ≠ false := by
  intro teqf
  cases teqf

-- true ≠ false
-- ∀ x : Bool, x = true ∨ x = false
-- we need to define standard operators :
-- ! : Bool → Bool
-- && : Bool → Bool → Bool
-- || : Bool → Bool → Bool

-- (∀ x : Bool, QQ x) ↔ QQ true ∧ QQ false,and
-- (∃ x : Bool, QQ x) ↔ QQ true ∨ QQ Flase


-- def not : Bool → Bool
-- | true => false
-- | false => true

example : !(!b) = b := by
  cases b
  · dsimp [not]
    rfl
  · dsimp [not]
    rfl
-- def and : Bool → Bool → Bool
-- | true, b => b
-- | false b => false

example : (false && b) = false := by
  dsimp[and]

example : (b && false) = false := by
  cases b
  · dsimp[and]
  · dsimp[and]

-- def or : Bool → Bool → Bool
-- | true, b => true
-- | false, b => b

--De Morgan's
example : (!(x && y)) = (!x || !y) := by
  cases x
  · dsimp[not, or, and]
  · dsimp[not, or, and]

example : ∀ b : Bool, (b = true) ∨ (b = false) := by
  intro xb
  cases xb
  · right
    rfl
  · left
    rfl

def is_true : Bool → Prop
| true => True
| false => False

example : true ≠ false := by
  intro tf
  have ttff : is_true false → False := by
    dsimp[is_true]
    intro f
    exact f
  apply ttff
  rw[←tf]
  dsimp[is_true]

example : true ≠ false := by
  intro tf
  change is_true false
  rw[←tf]
  dsimp[is_true]

example : true ≠ false := by
  intro tf
  cases tf
