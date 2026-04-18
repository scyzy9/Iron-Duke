/-

Lecture 7 : Predicate logic

-/

/-
predicate logic =

propositional logic
+ types (or sets)
+ functions
+ predicates and relations
+ quantifiers : ∀ (\forall) ∃ (\exists)

People : Type
Loves : People → People → Prop

"Everybody loves somebody"
∀ x : People , ∃ y : People, Loves x y
"Somebody is loved by everybody"
∃ x : People, ∀ y : People , Loves y x


-/

variable (P Q R : Prop)
variable (A B C : Type)
variable (PP QQ : A → Prop)

-- how to prove with ∀ ?
-- to prove : intro
-- to use : apply

example : (∀ x : A, PP x)
        → (∀ x : A, PP x → QQ x)
        → (∀ x : A, QQ x) := by
intro pp pq
intro a
apply pq
apply pp

-- (∀ x : A, PP x ∧ QQ x) ↔ (∀ x : A, PP x) ∧ (∀ x : A, QQ x)
-- (∀ x : A, PP x ∨ QQ x) ← (∀ x : A, PP x) ∨ (∀ x : A,  QQ x)
-- (∃ x : A, PP x ∨ QQ x) ↔ (∃ x : A, PP x) ∨ (∃ x : A, QQ x)

-- how to use ∃ ?
-- to prove : exists x : A, PP x
--    exists a,
--    remains to prove PP a
-- to use H : ∃ x : A, PP x
-- cases H with
--   | intro a pa => ,,,
-- H is replaced by a : A, pa : P a

example : (∃ x : A, PP x)
        → (∀ x : A, PP x → QQ x)
        → (∃ x : A, QQ x) := by
intro pp pq
cases pp with
| intro a pa =>
    exists a
    apply pq
    exact pa

example : (∃ x : A, PP x)
        → (∀ x : A, PP x → QQ x)
        → (∃ x : A, QQ x) := by
intro pp pq
cases pp with
| intro a pa =>
   constructor
   apply pq
   assumption

-- example : (∃ x : A, PP x)
--         → (∀ x : A, PP x → QQ x)
--         → (∃ x : A, QQ x) := by
--   intro pp pq
--   constructor
--   apply pq
--   cases pp with
--   | intro a pa =>
--     assumption
--error

example :
(∃ x : A, PP x ∨ QQ x) ↔ (∃ x : A, PP x) ∨ (∃ x : A,  QQ x) := by
constructor
. intro pq
  cases pq with
  | intro a pqa =>
     cases pqa with
     | inl pa =>
         left
         exists a
         -- assumption
     | inr qa =>
         right
         exists a
. intro pq
  cases pq with
  | inl pp =>
     cases pp with
     | intro a pa =>
         exists a
         left
         exact pa
  | inr qq =>
      cases qq with
      | intro a pa =>
          exists a
          right
          assumption


/-
P ∧ Q → R ↔ P → Q → R

(∃ x : A, PP x) → R ↔ ∀ x : A, (PP x → R)

-/

example : (∃ x : A, PP x) → R ↔ ∀ x : A, (PP x → R) := by
constructor
. intro pr a pa
  apply pr
  exists a
. intro pr pp
  cases pp with
  | intro a pa =>
     apply pr
     assumption
