/- COMP2065 (IFR) - Tutorial 3 -/

/- Predicate Logic -/

variable (A B C : Type)

variable (P Q : A → Prop)

/- Quantifiers
--                    How to prove             How to use
-- universal (∀)      intro h                  apply h
-- existential (∃)    exists a / constructor   cases h with | intro x p => …
-/

theorem ex0 : (∀ x : A, P x) → ¬ (∃ x : A, ¬ P x) := by
  intro px
  intro npx
  cases npx with
  | intro x hnpx =>
    have px := px x
    exact hnpx px


theorem ex1 : (∃ x : A, P x) → ¬ (∀ x : A, ¬ P x) := by
  intro px
  cases px with
  | intro x px =>
    intro npx
    have hnpx := npx x
    exact hnpx px

open Classical

#check byContradiction

example {P : Prop}: ¬ (¬ P) → P := by
  apply byContradiction

theorem ex2 : ¬ (∃ x : A, ¬ P x) → ∀ x : A, P x := by
  intro nnpx
  intro x
  have hnnpx : ¬¬P x := by
    intro npx
    apply nnpx
    exists x
  have px := byContradiction hnnpx
  exact px





theorem ex3 : ¬ (∀ x : A, ¬ P x) → ∃ x : A, P x := by
  intro nnAll
  have em_ex := em (∃ x : A, P x)
  cases em_ex with
  | inl yes =>
      exact yes
  | inr no =>
      have f : False := by
        apply nnAll
        intro x
        intro hpx
        apply no
        exists x
      cases f

/- Equality
--                   How to prove     How to use
-- equality (=)      rfl              rw [h] / rw [← h]
-/

theorem ex4 : ∀ x : A, x = x := by
  intro x
  rfl

theorem ex5 : ∀ x y : A, x = y → y = x := by
  intro x y
  intro xy
  rw[xy]

theorem ex6 : ∀ x y z : A, x = y → y = z → x = z := by
  intro x y z
  intro xy yz
  rw[←yz]
  assumption
/- Translate English into Predicate Logic -/

axiom Person : Type
axiom ReportsTo (x y : Person) : Prop

/- Two people are colleague if they have a common person to report to -/
def Colleague (x y : Person) : Prop :=
  ∃ z : Person, (ReportsTo x z)∧(ReportsTo y z)

/- Being colleague should be a symmetric relation -/
theorem symColleague (x y : Person) : Colleague x y → Colleague y x := by
   intro h
   cases h with
   | intro z xzyz =>
     cases xzyz with
     | intro xy yz =>
       exists z

/- A person is the head of department if he is reported to by a person who is reported to by other person -/

def Head (x : Person) : Prop :=
  ∃ y z : Person, (ReportsTo x y)∧(ReportsTo y z)

/- Every person reports to some people or is reported to by some people -/

def Fact0 : Prop :=
  sorry
