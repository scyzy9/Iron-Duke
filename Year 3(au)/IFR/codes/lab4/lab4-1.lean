-- Welcome to the COMP2065 (IFR) Tutorial #4!
--
-- Download today's tutorial from Moodle:
-- `Tutorials > Warren > Tutorial 4 Exercises - Warren`.
--
--

-- we will need to use classical logic (em) at various points today
open Classical

-- stop the linter from complaining about everything
set_option linter.all false

-- propositions
variable (P : Prop)

-- types
variable {A B : Type}

-- relations
variable {R : A → B → Prop}

-- predicates
variable {PP : A → Prop}
variable {QQ : A → A → Prop}

-- proof for `raa` - note can also use `byContradiction`
theorem raa : ¬¬P → P := by
  intro nnp
  cases em P with
  | inl p =>
    exact p
  | inr np =>
    have f : False := by
      apply nnp
      exact np
    cases f

/-
 -- Tutorial #4: Part 1
 --
 -- [ ] Predicate proofs and equality: part II.
 -/

 -- quick recap

example : ∀ a b : A, a=b → (PP a → PP b) → (PP b → PP a) := by
  intro a b
  intro ab
  intro hab
  rw[ab]
  intro hb
  exact hb

example : ∀ a b : A, ∃ c : A, QQ a b → QQ a c → b=c := by
 sorry


-- exercises

theorem ex1 : ∀ a b c d : A, a=b ∧ b=c ∧ c=d → a=d := by
  intro a b c d
  intro all
  cases all with
  | intro ab bccd =>
    cases bccd with
    | intro bc cd =>
      have ac : a = c := by
        rw[bc] at ab
        exact ab
      have ad : a = d := by
        rw[cd] at ac
        exact ac
      exact ad

theorem ex2 : ∀ a : A, ∃ b : A, ∀ c : A, b=c → QQ a b → QQ c b := by
  intro a
  exists a
  intro c
  intro ac
  intro qqaa
  rw[ac]
  rw[←ac]
  exact qqaa


theorem ex3 : ∀ a b c d : A, ∃ e : A, a=c → d=e → PP a = PP b → PP c = PP d := by
  intro a b c d
  exists b
  intro ac db hab
  rw[ac] at hab
  rw[←db] at hab
  exact hab

theorem ex4 : ∀ a b : A, ∃ c : A, QQ a b → ¬(QQ a c) := by
 sorry


/-
 -- Tutorial #4: Part 2
 --
 -- [ ] Definitions of formal relations.
 --
 -- In this exercise we focus on definitions in formal logic and limit
 -- the set of genders to {Male,Female} for simplicity of the exercise.
 -/



/- demo -- recap of predicate logic and definitions in lean -/

axiom Person : Type

axiom Male : Person → Prop

axiom Female : Person → Prop

axiom Parent : Person → Person → Prop

axiom Married : Person → Person → Prop

axiom Sibling : Person → Person → Prop

-- `x` is the sister of `y`.
def Sister(x y : Person) : Prop
  := Female x ∧ Sibling y x

-- `x` has a brother.
def hasBrother(x : Person) : Prop
  := ∃ Male y : Person, Sibling y x



/- exercises - predicate logic and definitions in lean -/

-- `x` has an uncle
def hasUncle(x : Person) : Prop
:= ∃ Male z : Person,∃ y : Person, Parent y x ∧ Sibling z y

-- Nobody has a sibling who is also their parent
def weird : Prop
  := ∀ x y : Person,Parent y x ∧ ¬(Sibling y x)

-- Everybody has exactly two parents (challenging)
-- be careful not to define that everybody has at least two parents!
def twoparents : Prop
  := ∀ x : Person,∃ y z : Person,∀ m : Person,(Parent y x ∧ Parent z x ∧ Parent m x)→(m = y ∨ m = z)



-- End of tutorial #4 exercises 🍰 --

/-
  Here's a challenge for anyone who is finished or wants a puzzle to do at home 🙂

  Hints:
    1. you will need to exists `have`.
    2. I believe the proof is classical and `raa` was my friend here on *multiple* occasions!
    3. Do not "throw away" something which might later be exists-able (i.e. doing `left` or `right` too early).
-/
example : (∀ x y : Person, ¬Sibling x y ∨ ¬Parent y x) ↔ (∀ x y : Person, ¬(Sibling x y ∧ Parent y x)) := by
  sorry
