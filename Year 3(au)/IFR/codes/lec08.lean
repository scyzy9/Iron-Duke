/-

Lecture 8 : Predicate logic

-/

/-
predicate logic =

propositional logic
+ types (or sets)
+ functions
+ predicates and relations
+ quantifiers : ∀ (\forall) ∃ (\exists)
+ Equality
-/

variable (P Q R : Prop)
variable {A B C : Type}
variable (PP QQ : A → Prop)
notation "ℕ" => Nat

/-
Summary
∀
How to prove : intro a
How to use : apply h
∃
How to prove : constructor , exists a
How to use : cases h with
             | intro a pa => ....
-/

/- What is equality?

Given A : Type
a b : A
we can form
a = b : Prop
a and b are equal.

3 + 4 = 7

f , g : List ℕ → List ℕ , functional extensionality
P Q : Prop
P ↔ Q , do we know P = Q ?
R ∧ S = S ∧ R ? yes, propositional extensionality

ℕ = ℚ ? not equal in Lean, univalence
-/

/-
How to prove a = b ? use rfl
How to use h : a = b use rw
-/

example : ∀ x : A, x = x := by
intro a
rfl

example : ∀ x y : A, x = y → PP y → PP x := by
intro x y xy py
rw [xy] -- rewrite
assumption

example : ∀ x y : A, x = y → PP x → PP y := by
intro x y xy px
rw [← xy] -- \<-
assumption

#check @Eq A

-- reflexive : ∀ x : A, x = x
-- symmetric : ∀ x y : A, x=y → y=x
-- transitive : ∀ x y z : A, x=y → y=z → x=z
-- = is a equivalence-relation

/-
Examples :
Eq (=)
same row
5 ≡ 7 [MOD 2]

Counterexamples
≠ (a ≠ b) = ¬ (a = b) = (a = b) → False
Love
≤ : 3 ≤ 4 but ¬ (4 ≤ 3) preorder
⊆ : Set A → Set A → Prop
Set A = A → Prop
-/


example : ∀ x y : A, x=y → y=x := by
intro x y xy
rw [xy]
-- rfl : y = y

example : ∀ x y z : A, x=y → y=z → x=z := by
intro x y z xy yz
rw [xy]
assumption

example : ∀ x y z : A, x=y → y=z → x=z := by
intro x y z xy yz
rw [← yz]
assumption

---
axiom People : Type
axiom Loves : People → People → Prop

-- 1) everybody loves somebdody else
def P1 : Prop
:= ∀ x : People, ∃ y : People ,
    Loves x y ∧ x ≠ y
-- 2) There are people who love exactly one person.
def P2 : Prop
:= ∃ x : People, ∃ y : People, Loves x y
    ∧ ∀ z : People, Loves x z → z = y
-- If you get bored
/-
R : A → B → Prop

(∀ x : A, ∃ y : B, R x y)
→ ∃ f : A → B, ∀ x : A, R x (f x)

is this a tautology? Has it got a name?
Do people disagree on this.
-/
