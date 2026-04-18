/-
COMP2065-IFR Exercise 03
(Predicate logic) (20)

    This exercise has 2 parts.

    The first part is multiple choice and your task is to
    translate english to predicate logic.

    In the 2nd part we play logic poker again :-) but this time for
    predicate logic.

-/

-- part 1 (10)
namespace family

-- Given the following type, predicates and relations:

axiom People : Type
axiom Male : People → Prop
axiom Female : People → Prop
-- Male x means x is male
-- Female x means x is female
axiom Parent : People → People → Prop
-- Parent x y means x is a parent of y
axiom Married : People → People → Prop
-- Married x y means x is married to y

/- --- Do not add/change anything above this line --- -/

/-
The following questions are all mutiple choice and there is
exactly one correct answer. You get 2 points for each correct answer.

To answer, replace 'sorry' by the number of the correct definition (1-5).

DO NOT modify any of the provided definitions.

For example:

Q0 : How do we translate
"Everybody is equal to themself"
into predicate logic?
-/
def Self_Equal_1 : Prop := false
def Self_Equal_2 : Prop := false
def Self_Equal_3 : Prop := ∀ x : People, x = x
def Self_Equal_4 : Prop := false
def Self_Equal_5 : Prop := false

def answer0 : Nat := 3


/- Q1 : How do we translate
"x is the grandmother of y"
into predicate logic -/

def Grandmother_1 (x y z : People) : Prop
:= Female x ∧ Parent x z ∧ Parent z y
def Grandmother_2 (x y z : People) : Prop
:= Female x ∧ Parent x z → Parent z y
  def Grandmother_3 (x y : People) : Prop
  := Female x ∧ ∃ z : People , Parent x z ∧ Parent z y
def Grandmother_4 (x y : People) : Prop
:= Female x ∧ ∀ z : People , Parent x z → Parent z y
def Grandmother_5 (x y : People) : Prop
:= ∀ z : People , Female z ∧ Parent x z → Parent z y

def answer1 : Nat := 3

/- Q2 : How do we translate
"Everybody has got a mother."
into predicate logic ?
-/
def every_mother_1 : Prop
:= ∀ x : People , ∃ y : People , Female y ∧ Parent y x
def every_mother_2 : Prop
:= ∀ x y : People , Female y → Parent y x
def every_mother_3 : Prop
:= ∃ x : People , ∀ y : People , Female y → Parent y x
def every_mother_4 : Prop
:= ∀ x : People , ∃ y : People , Parent y x → Female y
def every_mother_5 : Prop
:= ∀ x : People , ∀ y : People , Female y ∧ Parent y x

def answer2 : Nat := 1

/- Q3 : How do we translate
"Nobody is married to themselves."
into predicate logic ?
-/

def self_married_1 : Prop
:= ¬ ∀ x : People , Married x x
def self_married_2 : Prop
:= ∃  x : People , ¬ Married x x
def self_married_3 : Prop
:= ∀ x : People , Married x x ∧ x ≠ x
def self_married_4 : Prop
:= ∀ x : People , ¬ Married x x
def self_married_5 : Prop
:= ∀ x y : People , x≠y → Married x y

def answer3 : Nat := 4

/- Q4 : How do we translate
"Everybody is married at most to one other person."
into predicate logic ?
-/
def no_bigamy_1 : Prop
:= ∀ x : People , ∀ y z : People, Married x y ∧ Married x z ∧ x ≠ z
def no_bigamy_2 : Prop
:= ∀ x : People , ∀ y z : People, Married x y → Married x z → y = z
def no_bigamy_3 : Prop
:= ∀ x : People , ∃ y : People, Married x y ∧ y = y
def no_bigamy_4 : Prop
:= ∀ x : People , ∀ y : People, Married x y → x ≠ y
def no_bigamy_5 : Prop
:= ∀ x : People , ∃ y z : People, x ≠ y ∧ Married x y ∧ Married x z

def answer4 : Nat := 2

/- Q5 : How do we translate
"x is the sibling of y"
into predicate logic ?
-/
def Sibling_1 (x y : People) : Prop
  := x ≠ y ∧ ∀ z : People , Parent z x ∧ Parent z y
def Sibling_2 (x y : People) : Prop
  := x ≠ y ∧ ∃ z : People , Parent z x ↔ Parent z y
def Sibling_3 (x y z : People) : Prop
  := x ≠ y ∧ Parent z x ↔ Parent z y
def Sibling_4 (x y z : People) : Prop
  := x ≠ y ∧ Parent z x ∧ Parent z y
def Sibling_5 (x y : People) : Prop
  := x ≠ y ∧ ∀ z : People , Parent z x ↔ Parent z y

def answer5 : Nat := 2

/- DO NOT MODIFY OR DELETE -/
/- -/ end family
/- -/ namespace poker
/- -/ variable (A : Type)
/- -/ variable (PP QQ : A → Prop)
/- -/ variable (RR : A → A → Prop)
/- -/ variable (P Q R : Prop)
/- -/ inductive PokerAnswer : Type
/- -/ | NotProvable : PokerAnswer
/- -/ | Intuition : PokerAnswer
/- -/ | Classical : PokerAnswer
/- -/ | UNANSWERED : PokerAnswer
/- -/ open PokerAnswer
/- -/ open Classical
/- -/ theorem raa : ¬ ¬ P → P := by
/- -/   intro nnp
/- -/   cases (em P) with
/- -/   | inl p => exact p
/- -/   | inr np => contradiction
/- DO NOT MODIFY OR DELETE -/


/-
PART 2 (10 points)
We play the game of logic poker - but this time with predicate logic :-)

You have to classify each proposition as either
  a) provable intuitionistically (i.e. in plain lean)
  b) provable classically (using em : P ∨ ¬ P or raa : ¬¬ P → P).
  c) not provable classically.
and then you have to prove the propositions in a) and b) accordingly.

You will start with a score of 10 points, and then 1 point will be deducted
for each incorrect classification and 1 point will be deducted for each
incorrect proof. We stop deducting at zero, so you cannot earn negative points.
So, for instance, if you do every proof correctly but do not classify anything,
you will earn 0/10.

CLASSIFICATION: For each proposition, replace sorry with
  Intuition     if the proposition is provable intuitionistically (i.e. in plain lean)
  Classical     if the proposition is provable classically (using em : P ∨ ¬ P or raa : ¬¬ P → P)
  NotProvable   if the proposition is not provable classically

**Important**: Every classification should be one of these three, or sorry.
DO NOT put anything else on the right-hand side or leave it totally blank.

PROOFS:
  Then, prove the propositions you classified as 'Intuition' or 'Classical'.
  For the 'Classical' ones, you may use em or raa, as discussed in lecture.
  For propositions classified as 'NotProvable' just keep "sorry," as the proof.

  You are only allowed to use the tactics introduced in the lecture
  (e.g. assume, exact, apply, constructor, cases, left, right, have,
  exists, reflexivity, rewrite)

  Please only use the tactics in the way indicated in the lecture notes,
  otherwise we may deduct points.
-/

def classification01 : PokerAnswer := NotProvable
theorem q01 : (∀ x:A, ∃ y : A , RR x y) → (∃ y : A, ∀ x : A, RR x y) := by
  sorry

def classification02 : PokerAnswer := Intuition
theorem q02 :  (∃ y : A, ∀ x : A, RR x y) → (∀ x:A, ∃ y : A , RR x y) := by
  intro rrxy
  intro x
  cases rrxy with
  | intro y ay =>
    exists y
    exact ay x


def classification03 : PokerAnswer := Intuition
theorem q03 : ∀ x y : A, x = y → RR x y → RR x x := by
  intro x y xy rrxy
  cases xy
  assumption

def classification04 : PokerAnswer := NotProvable
theorem q04 : ∀ x y z : A, x ≠ y → x ≠ z → y ≠ z := by
  sorry

def classification05 : PokerAnswer := Intuition
theorem q05 : ∀ x y z : A, x = y → x ≠ z → y ≠ z := by
  intro x y z
  intro xy
  intro xnz
  cases xy
  assumption

def classification06 : PokerAnswer := Classical
theorem q06 : ∀ x y z : A, x ≠ y → (x ≠ z ∨ y ≠ z) := by
  intro x y z xny
  have emxz := em (x = z)
  cases emxz with
  | inl hxz =>
    right
    intro hyz
    apply xny
    rewrite [hxz, hyz]
    rfl
  | inr hnxz =>
    left
    exact hnxz



def classification07 : PokerAnswer := Intuition
theorem q07 : ¬ ¬ (∀ x : A, PP x) → ∀ x : A, ¬ ¬ PP x := by
  intro nnppx
  intro x
  intro nppx
  apply nnppx
  intro allppx
  have ppx := allppx x
  exact nppx ppx

def classification08 : PokerAnswer := Classical
theorem q08 : (∀ x : A, ¬ ¬ PP x) → ¬ ¬ ∀ x : A, PP x := by
  intro nnppx
  intro nppx
  have ppx : ∀ x : A , PP x := by
    intro x
    have h : ¬¬ PP x := nnppx x
    have hx : PP x := byContradiction h
    exact hx
  exact nppx ppx




def classification09 : PokerAnswer := NotProvable
theorem q09 : (∃ x : A, true) → (∃ x:A, PP x) → ∀ x : A,PP x := by
  sorry


def classification10 : PokerAnswer := Classical
theorem q10 : (∃ x : A, true) → (∃ x:A, PP x → ∀ x : A,PP x) := by
  intro h
  have emppx := em (∀ x : A, PP x)
  cases emppx with
  | inl ppx =>
    cases h with
    | intro a tt =>
      exists a
      intro ppa
      intro x
      exact ppx x
  | inr nppx =>
    have em_ex := em (∃ x, ¬ PP x)
    cases em_ex with
      | inl yes =>
          cases yes with
          | intro b hnb =>
              exists b
              intro hPb
              cases (hnb hPb)
      | inr no =>
          have hall : ∀ x, PP x := by
            intro x
            have em_px := em (PP x)
            cases em_px with
            | inl hpx =>
              exact hpx
            | inr hnp =>
              have hEx : ∃ x, ¬ PP x := by
                exists x
              cases no hEx
          cases nppx hall





--- Do not add/change anything below this line ---
end poker
