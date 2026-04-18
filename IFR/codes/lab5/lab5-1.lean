-- Welcome to the COMP2065 (IFR) Tutorial #5!

namespace warrens_tutorial

  ---- definitions
  def isTrue : Bool → Prop
    | b => b = true

  -- def not : Bool → Bool
  -- | true  => false
  -- | false => true

  -- def and : Bool → Bool → Bool
  -- | true, b  => b
  -- | false, _ => false

  -- def or : Bool → Bool → Bool
  -- | true, _  => true
  -- | false, b => b


  /- **-------------------------------------------------** -/
  /- recap - booleans: `exists`, `cases` and `contradiction`.** -/
  /- **-------------------------------------------------** -/

  -- show use of `exists` applied to an assumption
  example : ∀ x : Bool, ∃ y : Bool, x=y := by
    intro x
    exists x

  -- shows the use of `exists` on an inductive type
  example : ∃ x : Bool, (x==false) || (x==true) := by
    exists true

  -- shows the use of `exists` on an inductive type
  example : ∃ x : Bool, x=false ∨ x=true := by
    exists false

  -- `cases` and `contradiction`
  example : ∀ x y : Bool, x=y ∨ x≠y := by
    intro x y
    cases x
    cases y
    left
    rfl
    right
    intro ft
    cases ft
    cases y
    right
    intro tf
    cases tf
    left
    rfl


  /- **---------------------------------------------------** -/
  /- exercises - booleans: `exists`, `cases` and `contradiction`.  -/
  /- **---------------------------------------------------** -/

  -- solve the following exercises without using `exists ex` but instead `apply Exists.intro ex`
  -- to exercises a full understanding of the following proof.
  theorem ex1 : ∃ x y : Bool, y=true ∧ x=false := by
    apply Exists.intro false
    apply Exists.intro true
    constructor
    · rfl
    · rfl

  theorem ex1_1 : ∃ x y : Bool, y=true ∧ x=false := by
    exact ⟨false, true, rfl, rfl⟩

  theorem ex1_2 : ∃ x y : Bool, y=true ∧ x=false := by
    exists false

  theorem ex2 : ∀ x : Bool, ∃ y : Bool, x≠y := by
    intro x
    cases x
    exists true
    exists false

  theorem ex3 : ¬(∃ x y : Bool, x=y ∧ x≠y) := by
    intro h
    cases h with
    | intro x hy =>
      cases x
      cases hy with
      | intro y hhy =>
        cases y
        cases hhy with
        | intro l r =>
          apply r
          rfl
        cases hhy with
        | intro l r =>
          apply r
          exact l
      cases hy with
      | intro y hhy =>
        cases y
        cases hhy with
        | intro l r =>
          apply r
          exact l
        cases hhy with
        | intro l r =>
          apply r
          exact l

  theorem ex3_1 : ¬(∃ x y : Bool, x=y ∧ x≠y) := by
    intro h
    cases h with
    | intro x hx =>
      cases hx with
      | intro y hxy_and =>
        cases hxy_and with
        | intro hxy hxny =>
          exact hxny hxy

  -- this one is not trivial. You will need to use `have` and choose
  -- values for `x` and `y` that unifies with your only hypothesis.
  theorem ex4 : ¬(∀ x y : Bool, x=y ∧ x≠y) := by
    intro h
    have hx : true = false ∧ true ≠ false := h true false
    have hleft : true = false := hx.left
    have hright : true ≠ false := hx.right
    apply hright
    exact hleft

  /- **-------------------------------------------** -/
  /- recap - booleans: `dsimp` and `dsimp _ at _`.** -/
  /- **-------------------------------------------** -/

  example : ∀ x : Bool, true && (x == x) := by
    intro x
    cases x
    rfl
    rfl

  example : ∀ x : Bool, (x && true) == x := by
    intro x
    cases x
    rfl
    rfl

  example : ∀ x : Bool, false && x == true → false := by
    intro x
    cases x
    intro h
    have hx : (false && false == true) = false := rfl
    rw [hx] at h
    exact h
    intro h
    have hx : (false && true == true) = false := rfl
    rw [hx] at h
    exact h

/- **-----------------------------------------------** -/
/- exercises - booleans: `dsimp` and `dsimp _ at _`.** -/
/- **-----------------------------------------------** -/

theorem ex5 : ∃ b : Bool, ∀ x : Bool, (b || x) == true := by
  exists true
theorem ex6 : ∀ x y : Bool, (!(x || y)) == ((!x) && (!y)) := by
  intro x y
  cases x
  cases y
  rfl
  rfl
  rfl

/- This one is more difficult. You will need to use `have` and specify -/
/- something which unifies with the first assumption and is trivially true -/
theorem ex7 : ¬(∀ x : Bool, ∃ y : Bool, (x || y) = False) := by
  intro h
  have ht := h true
  cases ht with
  | intro y hy =>
    cases y
    dsimp[or] at hy




-- End of tutorial #5 exercises 🍰 --

/-
  Here's a challenge for anyone who is finished or wants a puzzle to do at home 🙂

  Do not use `trivial` or `exists` and try not to use `contradiction` or `assumption` in your solutions.
-/

theorem em_bool : ∀ b : Bool, (b || ! b) := by
  intro b
  cases b
  rfl
  rfl

theorem em_bool_1 : ∀ b : Bool, (b || ! b) := by
  intro b
  cases b
  dsimp [not,or]
  rfl

theorem neg_em_bool : ¬(∀ b : Bool, (b && ! b)) := by
  intro h
  have ht := h true
  dsimp[not,and] at ht
  cases ht


-- You could say `exists false` but `exists`
-- autocompletes the proof and is not very interesting
-- use `apply Exists.intro false` instead
example : ∃ x : Bool, ∀ y : Bool, !x ∨ y := by
  exists false

theorem or_thm : ∀ x y : Bool, (x || y) = !(!x && !y) := by
  intro x y
  cases x
  cases y
  rfl
  rfl
  cases y
  rfl
  rfl

theorem dm1_b : ∀ b c : Bool,
  (! (b || c)) = (! b && ! c) := by
  intro b c
  cases b
  cases c
  rfl
  rfl
  cases c
  rfl
  rfl

theorem dm2_b : ∀ b c : Bool,
   (! (b && c)) = (!b || ! c) := by
  intro b c
  cases b
  cases c
  rfl
  rfl
  cases c
  rfl
  rfl

end warrens_tutorial
