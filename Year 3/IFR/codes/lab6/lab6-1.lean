-- Welcome to the COMP2065 (IFR) Tutorial #6!

namespace warrens_tutorial_natural_numbers

    notation "ℕ" => Nat

    open Nat

    /- Definitions for operations on ℕ -/

    def pred : ℕ → ℕ
    | zero => zero
    | succ n => n

    def double : ℕ → ℕ
    | zero => zero
    | succ n => succ (succ (double n))

    def half : ℕ → ℕ
    | zero => zero
    | succ zero => zero
    | succ (succ n) => succ (half n)

    def add : ℕ → ℕ → ℕ
    | m, zero     => m
    | m, (succ n) => succ (add m n)

    /- Lemmas that may be useful for solving the exercises! -/

    theorem add_lneutr : ∀ n : ℕ, 0 + n  = n := by
        intro n
        induction n with
        | zero =>
            dsimp [add]
        | succ m ih =>
            change succ (0 + m) = succ m
            rw [ih]

    theorem add_assoc : ∀ l m n : ℕ , (l + m) + n = l + (m + n) := by
        intro l m n
        induction n with
        | zero =>
            dsimp [add]
        | succ x ih =>
            change succ (l + m + x) = succ (l + (m + x))
            rw [ih]

    theorem add_succ : ∀ l m : ℕ, (succ l) + m = succ (l + m) := by
        intro l m
        induction m with
        | zero =>
            dsimp [add]
        | succ x ih =>
            change (succ l + x) + 1 = succ ((l + x) + 1)
            rw [ih]

    theorem add_comm : ∀ l m : ℕ, l + m = m + l := by
        intro l m
        induction m with
        | zero =>
            dsimp [add]
            rewrite[add_lneutr]
            rfl
        | succ n ih =>
            rewrite [add_succ]
            rewrite [← ih]
            dsimp [add]
            rewrite [add_assoc]
            rfl

  /- Begin tutorial -/

  /- **-------------------------------** -/
  /- recap - `change` and `injection`.** -/
  /- **-------------------------------** -/

  /-
  [Reminder]
  def pred : ℕ → ℕ
  | zero := zero
  | (succ n) := n
  -/

  example : ∀ n : Nat, succ (pred n) = n → succ (pred n) = pred (succ n) := by
    intro n
    intro h
    rw[h]
    rfl

  /- `succ` is injective. That is to say, if `succ m = succ n`, then `m = n`. -/

  -- proof of injection
  example : ∀ m n : ℕ, succ m = succ n → m = n := by
    intro m n
    intro h
    injection h with h1

  -- use of injection
  example : ∀ m n : ℕ, succ m = succ n → m = n := by
    intro m n
    intro h
    injection h

  /- **-----------------------------------** -/
  /- exercises - `change` and `injection`.** -/
  /- **-----------------------------------** -/

  /-
    Try proving the following without using `rw` / `rewrite`
    immediately after the intro's.
    Hint: you are praciticing using `change` 🙂
  -/
  theorem ex1 : ∀ m n : ℕ, succ m = n → m = pred n := by
    intro m n h
    rw[←h]
    rfl

  /-
    Try to solve ex2:
    -- first with `injection` and without `change` (ex2_injection)
    -- and then with `change` but without `injection` (ex2_change)
  -/
  theorem ex2_injection : ∀ x y z : ℕ, succ x = succ y → y = z → x = z := by
    intro x y z
    intro h1 h2
    injection h1 with h3
    rw[h3]
    assumption

  theorem ex2_change : ∀ x y z : ℕ, succ x = succ y → y = z → x = z := by
    intro x y z
    intro h1 h2
    injection h1 with h3
    rw[h3]
    assumption

  -- good `injection` practice!
  theorem ex3 : ∀ x y z : ℕ, succ x = succ y ∧ succ (succ y) = succ (succ z) → x = z := by
    intro x y z
    intro h
    cases h with
    | intro h1 h2 =>
      injection h1 with h3
      injection h2 with h4
      injection h4 with h5
      rw[←h5]
      assumption

  /- **------------------------------------------------------** -/
  /- recap - `Structural Recursion` and `Induction` (Part I).** -/
  /- **------------------------------------------------------** -/

  /- [Definitions_on_ℕ] A definition for is_even -/
  def is_even : ℕ → Prop
| zero => True
| 1 => False
| succ (succ n) => is_even n

-- [Reminder]
-- def double : ℕ → ℕ
-- | zero => zero
-- | (succ n) => succ (succ (double n))

  /- [Reminder]
  -- def half : ℕ → ℕ
  -- | zero => zero
  -- | succ zero => zero
  -- | succ (succ n) => succ (half n)
  -/

  /- show than doubling any number returns an even number -/
  theorem double_n_is_even : ∀ n : ℕ, is_even (double n) := by
    intro n
    induction n with
    | zero =>
      simp only [double]
      simp only[is_even]
    | succ n ih =>
      dsimp[double]
      dsimp[is_even]
      assumption



  /- Here I will demonstrate the use of calc as it may be
  easier to use in `ex6` (and some coursework exercises)
  than applying/simplifying definitions -/
  theorem half_double : ∀ n : ℕ, half (double n) = n := by
    intro n
    induction n with
    | zero =>
      rfl
    | succ n ih =>
      dsimp[double]
      dsimp[half]
      rw[ih]


  /- **----------------------------------------------------------** -/
  /- exercises - `Structural Recursion` and `Induction` (Part I).** -/
  /- For each exercise, you should also state whether `induction` is -/
  /- required or is not required to prove them.                     -/
  /- **----------------------------------------------------------** -/


  /-
  ------------------------------------
  -- Ex# | Requires induction [Y/N] --
  -- Ex4 | [?]                      --
  -- Ex5 | [?]                      --
  -- Ex6 | [?]                      --
  -- Ex7 | [?]                      --
  ------------------------------------
  -/

  /- Think about how ℕ is defined and how `double` of ℕ is defined -/
  theorem ex4 : ∃ n : ℕ, double n = n := by
    exists 0

  /-
    Hint: `exists _` (which we should use in the form `apply Exists.intro _`)
           can take anything that reduces to ℕ
  -/
  theorem ex5 : ∀ m : ℕ, ∃ n : ℕ, double m = n := by
    intro m
    apply Exists.intro (double m)
    rfl


  theorem ex6 : ∀ m n : ℕ, (succ m) + n = succ (m + n) := by
    intro m n
    induction n with
    | zero =>
      rfl
    | succ n ih =>
      calc m.succ + (n + 1)
      _ = (m + (n + 1)).succ := by rw[add_succ]

  /-
    Hint: one of the previous exercises can be used as a lemma that is useful for this proof.
  -/

  theorem ex7 : ∀ n : ℕ, double n = n + n := by
    intro n
    induction n with
    | zero =>
      rfl
    | succ n ih =>
      dsimp[double]
      calc double n + 1 + 1
        = n + n + 1 + 1 := by rw[ih]
      _ = (n + n + 1) + 1 := by rfl
      _ = (n + (n + 1)) + 1 := by rw[←add_assoc]
      _ = (n + (1 + n)) + 1 := by rw[add_comm n 1]
      _ = (n + 1 + n) + 1 := by rw[←add_assoc]
      _ = n + 1 + (n + 1) := by rw[add_assoc]

  -- End of tutorial #6 exercises 🍰 --

end warrens_tutorial_natural_numbers
