/- The natural numbers ℕ - Part II -/

namespace tutorial_seven

  notation "ℕ" => Nat

  open Nat

  /- Less than or equals (as seen in lectures) -/
  def LE : Nat → Nat → Prop
  | m , n => ∃ k : ℕ , k + m = n

  infix:50 (priority := 1001) " ≤ " => LE

  /- Greater than or equals (new in this tutorial) -/
  def GE : Nat → Nat → Prop
  | m , n => ∃ k : ℕ , k + n = m

  infix:50 (priority := 1001) " ≥ " => GE

  /- custom version of addition -/
  def add : ℕ → ℕ → ℕ
  | m, zero => m
  | m, (succ n) => succ (add m n)

  /- custom verison of multiplication -/
  def mult : ℕ → ℕ → ℕ
  | _, zero => zero
  | m, (succ n) => (mult m n) + m

  /- A definition for is_even -/
  def is_even : ℕ → Prop
  | zero => true
  | (succ zero) => false
  | (succ (succ n)) => is_even n

  def double : ℕ → ℕ
  | zero => zero
  | succ n => succ (succ (double n))

  /- Lemmas which may (or may not) be useful in the following examples and exercises -/
  theorem add_assoc : ∀ l m n : ℕ, (l + m) + n = l + (m + n) := by
    intro l m n
    induction n with
    | zero =>
      -- base case
      dsimp [add]
    | succ x ih =>
      -- step case
      change succ (l + m + x) = succ (l + (m + x))
      rw [ih]

theorem add_lneutr : ∀ n : ℕ, 0 + n = n := by
 intro n
 induction n with
 | zero =>
    -- base case
    rfl
  | succ n' ih =>
    -- step case
    calc 0 + (n' + 1) = (0 + n') + 1 := by rfl
    _ = n' + 1 := by rw[ih]

theorem add_succ : ∀ m n : ℕ, (succ m) + n = succ (m + n) := by
  intro m n
  induction n with
  | zero =>
    -- base case
    dsimp [add]
  |  succ n' ih =>
    -- step case
    change (succ m + n') + 1 = succ ((m + n') + 1)
    rewrite [ih]
    rfl

theorem add_comm : ∀ m n : ℕ , m + n = n + m := by
  intro m n
  induction n with
  | zero =>
    -- base case
    dsimp [add]
    rewrite [add_lneutr]
    rfl
  | succ n' ih =>
    -- step case
    dsimp [add]
    rewrite [add_succ]
    rewrite [← ih]; simp; rfl

  /-

  Part 1 : Recap `induction` and more complex usages of `calc`.

  -/

  theorem ex6 : ∀ m n : ℕ, (succ m) + n = succ (m + n) := by
  intro m n
  cases n with
  | zero =>
    rfl
  | succ n' =>
    calc
      (m + 1) + (n' + 1)
      _ = m + (1 + n') + 1 := by apply add_assoc
      _ = m + (n' + 1) + 1 := by rw [add_comm 1]

  theorem ex7 : ∀ n : ℕ, double n = n + n := by
    intro n
    induction n with
    | zero =>
      rewrite[double]
      rfl
    | succ x ih =>
      rewrite [double]
      rewrite [ih]
      rewrite [ex6]
      rfl

  -- theorem add_assoc : ∀ a b c : ℕ, (a + b) + c = a + (b + c) :=
  example : ∀ k l m n : ℕ, k + l + m + n = n + m + l + k := by
    intro k l m n
    -- using `calc` we are demonstrating how to get from the expression on
    -- the left side of the `=` to the right side step-by-step
    -- k + l + m + n = n + l + m + k
    calc
      k + l + m + n
      _ = k + l + (m + n) := by apply (add_assoc (k+l) m n)
      _ = m + n + (k + l) := by rw [add_comm]
      _ = n + m + (k + l) := by rw [add_comm m n]
      _ = n + m + (l + k) := by rw [add_comm k l]
      _ = n + m + l + k := by rw [← add_assoc]

  /-
   - `The game of induction!`
   -
   - For the following exercises, identify which require `induction`
   - to be proven, and provide proofs for each exercise.
   -/

  /-
    Level 1 -- There exists a natural number `m` such that for all
      ℕ `n`, there exists a ℕ `k`, whereby `m + k = 1 + n`.
  -/
  theorem induction_game_lvl_1 : ∃ m : ℕ, ∀ n : ℕ, ∃ k : ℕ, m + k = succ n := by
    exists 0
    intro n
    exists (succ n)
    -- the proof for `add_lneutr` uses induction, therefore
    -- we require induction to prove "level 1".
    apply add_lneutr

  /-
    Level 2 -- For all natural numbers `n`, there exists two
      natural numbers that when added together, equals `n`.
  -/
  theorem induction_game_lvl_2 : ∀ n : ℕ, ∃ a b : ℕ, n = a + b := by
    intro n
    /- Can be proven without induction!
    Notice that before, we had a choice to make whether to apply `existsi` with `0` or `n`.
    Due to the definition of `add` (` | m zero := m `), if we do the zero last, we can prove
    without the need for induction :-)
    -/
    apply Exists.intro n
    apply Exists.intro 0
    rfl


  /-
    Level 3 -- ∀ n : ℕ, if `n` is even, then `succ (succ n)` is also even, and vice versa.
  -/
  theorem induction_game_lvl_3 : ∀ n : ℕ, is_even n ↔ is_even (succ (succ n)) := by
    intro n
    /- we might be tempted to use `constructor` here because we saw `↔` but the proof is much simpler! -/
    rfl
    /- Think about what happened here. Look back at the definition of `is_even`! -/

  /-
    Level 4 -- for all even natural numbers n, its successor cannot be even.
  -/
  theorem induction_game_lvl_4 : ∀ n : ℕ, is_even n → ¬is_even (succ n) := by
    intro n
    intro n_even
    intro succn_even
    induction n with
    | zero =>
      -- base case
      dsimp [is_even] at succn_even
      contradiction
    | succ n' ih =>
      -- step case
      dsimp [is_even] at succn_even
      apply ih
      exact succn_even
      exact n_even

  /-
    Level 5 -- yx + x = (y+1)x
  -/
  theorem induction_game_lvl_5 : ∀ x y : ℕ, y * x + x = succ y * x := by
    intro x y
    induction x with
    | zero =>
      -- base case
      rfl
    | succ x' ih =>
      -- step case
      -- ih : y * x' + x' = y.succ * x'
      -- ⊢ y * (x' + 1) + (x' + 1) = y.succ * (x' + 1)
      calc
        succ (y * x' + y + x')
        _ = succ ((y * x') + (y + x')) := by rw [add_assoc]
        _ = succ ((y * x') + (x' + y)) := by rw [add_comm x' y]
        _ = succ ((y * x') + x' + y)   := by rw [add_assoc]
        _ = succ (succ y * x' + y)     := by rw [ih]

  /-

  Part 2 : Show that `≥` is antisymmetric and `max` is a commutative monoid.

  -/

  /- Showing that `≥` is antisymmetric. -/

  -- needed for assignment - `sorry`
  theorem anti_sym_lem : ∀ x y : ℕ , x + y = y → x = 0 := by
    sorry -- prove for your assignment

  -- needed for assignment - `sorry`
  theorem add_lem : ∀ x y : ℕ , x + y = 0 → x = 0 := by
    sorry -- prove for your assignment

  /- antisymmetry of ≥ -/
  theorem anti_sym : ∀ x y : ℕ , x ≥ y → y ≥ x → x = y := by
    sorry -- too similar to your assignment

  /-

   Showing that `max` is a commutative monoid.

   - 1. max is left neutral : (max 0 n = n)
   - 2. max is right neutral : (max n 0 = n)
   - 3. max is associative : max (max l m) n = max l (max m n)
   - 4. max is commutative : max m n = max n m

  -/

-- we define a recursive function max computing the maximum of 2 numbers
def max : ℕ → ℕ → ℕ
| zero, n => n
| (succ m), zero => succ m
| (succ m), (succ n) => succ (max m n)

/- Exercises -/

theorem max_lneutr : ∀ n : ℕ, max 0 n = n := by
  intro n
  rewrite [max] -- `dsimp` also works here
  rfl

-- did not need induction here!
theorem max_rneutr : ∀ n : ℕ, max n 0 = n := by
  intro n
  cases n with
  | zero =>
    dsimp[max]
  | succ n =>
    rewrite [max]
    rfl

-- Hint: strong induction.
theorem max_assoc : ∀ l m n : ℕ, max (max l m) n = max l (max m n) := by
  intro l
  induction l with
  | zero =>
    -- base case of induction: ∀ (m n : ℕ), max (max 0 m) n = max 0 (max m n)
    dsimp [max]
    intro m n
    rfl
  | succ l' ih =>
    -- step case of induction
    -- ih : ∀ (m n : ℕ), max (max l' m) n = max l' (max m n)
    -- ⊢ ∀ (m n : ℕ), max (max (l' + 1) m) n = max (l' + 1) (max m n)
    intro m n
    cases m with
    | zero =>
      -- zero case on `m`
      dsimp [max]
    | succ m' =>
      -- succ case on `m`
      cases n with
      | zero =>
        -- zero case on `n`
        dsimp [max]
      | succ n' =>
        -- succ case on `n`
        dsimp [max]
        rewrite [ih]
        rfl

theorem max_comm : ∀ m n : ℕ, max m n = max n m := by
  intro m
  induction m with
  | zero =>
    -- base case
    intro n
    rw [max_rneutr]
    rfl
  | succ m' ih =>
    -- step case
    intro n
    cases n with
    | zero =>
      dsimp[max]
    | succ n' =>
      dsimp [max]
      rw [ih]

  -- End of tutorial #7 exercises 🍰 --

  /-
  If you reached the end and want additional practice, I recommend
  having a go at the exercises from Mark's tutorial #7.
  -/

end tutorial_seven
