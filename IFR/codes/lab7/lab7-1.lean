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

  theorem add_assoc_alt : ∀ l m n : ℕ, (l + m) + n = l + (m + n) := by
    intro l m n
    induction n with
    | zero =>
      rfl
    | succ n ih =>
      calc l + m + (n + 1)
        = l + m + n.succ := by rfl
      _ = succ ((l + m) + n) := by rfl
      _ = succ (l + m + n) := by rfl
      _ = succ (l + (m + n)) := by rw[ih]

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

  theorem add_succ_alt : ∀ m n : ℕ, (succ m) + n = succ (m + n) := by
    intro m n
    induction n with
    | zero =>
      rfl
    | succ n ih =>
      calc m.succ + (n + 1)
        = (m + 1) + n.succ := by rfl
      _ = succ ((m + 1) + n) := by rfl
      _ = succ (succ (m + n)) := by rw[ih]
      _ = succ (m + succ n) := by rfl
      _ = (m + (n + 1)).succ := by rfl


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

  theorem add_comm_alt : ∀ m n : ℕ , m + n = n + m := by
    intro m n
    induction n with
    | zero =>
      calc m + 0
        = m := by rfl
      _ = 0 + m := by rw[add_lneutr]
    | succ n ih =>
      calc m + (n + 1)
        = m + n.succ := by rfl
      _ = succ (m + n) := by rfl
      _ = succ (n + m) := by rw[ih]
      _ = (succ n) + m := by rw[←add_succ]
  /-

  Part 1 : Recap `induction` and more complex usages of `calc`.

  -/

  theorem ex6 : ∀ m n : ℕ, (succ m) + n = succ (m + n) := by
    intro m n
    induction n with
    | zero =>
      rfl
    | succ n ih =>
      calc m.succ + n.succ
      = (m.succ + n) + 1 := by rw [add_assoc]
      _ = (m + n).succ + 1 := by rw[ih]


  theorem ex7 : ∀ n : ℕ, double n = n + n := by
    intro n
    induction n with
    | zero =>
      rfl
    | succ n ih =>
      dsimp [double]
      calc double n + 1 + 1
        = n + n + 1 + 1 := by rw[ih]
      _ = n + n.succ + 1 := by rfl
      _ = n.succ + n + 1 := by rw[add_comm n n.succ]



  -- theorem add_assoc : ∀ a b c : ℕ, (a + b) + c = a + (b + c) :=
  example : ∀ k l m n : ℕ, k + l + m + n = n + m + l + k := by
    intro k l m n
    -- using `calc` we are demonstrating how to get from the expression on
    -- the left side of the `=` to the right side step-by-step
    -- k + l + m + n = n + l + m + k
    calc
      k + l + m + n
        = (k + l) + (m + n) := by rw[add_assoc]
      _ = (m + n) + (k + l) := by rw[add_comm]
      _ = (n + m) + (k + l) := by rw[add_comm m n]
      _ = (n + m) + (l + k) := by rw[add_comm k l]
      _ = (n + m + l) + k := by rw[←add_assoc]

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
    apply Exists.intro 1
    intro n
    apply Exists.intro n
    rw[add_comm]

  /-
    Level 2 -- For all natural numbers `n`, there exists two
      natural numbers that when added together, equals `n`.
  -/
  theorem induction_game_lvl_2 : ∀ n : ℕ, ∃ a b : ℕ, n = a + b := by
    intro n
    apply Exists.intro n
    apply Exists.intro 0
    rfl

  /-
    Level 3 -- ∀ n : ℕ, if `n` is even, then `succ (succ n)` is also even, and vice versa.
  -/
  theorem induction_game_lvl_3 : ∀ n : ℕ, is_even n ↔ is_even (succ (succ n)) := by
    intro n
    constructor
    · intro h
      dsimp[is_even]
      assumption
    · intro h
      dsimp[is_even] at h
      assumption


  /-
    Level 4 -- for all even natural numbers n, its successor cannot be even.
  -/
  theorem induction_game_lvl_4 : ∀ n : ℕ, is_even n → ¬is_even (succ n) := by
    intro n
    intro h
    intro h1
    induction n with
    | zero =>
      cases h1
    | succ n ih =>
      dsimp[is_even] at h1
      exact ih h1 h
    -- intro n
    -- dsimp[is_even]
    -- intro h
    -- intro h1
    -- induction n with
    -- | zero =>
    --   cases h1
    -- | succ n ih =>
    --   have h2 : is_even n = is_even (n + 1 + 1) := by rfl
    --   rw[←h2] at h1
    --   have h3 := ih h1 h
    --   assumption

  /-
    Level 5 -- yx + x = (y+1)x
  -/
  theorem induction_game_lvl_5 : ∀ x y : ℕ, y * x + x = succ y * x := by
    intro x y
    induction x with
    | zero => rfl
    | succ x ih =>
    calc y * succ x + succ x
      = (y * x + y) + succ x := rfl
      _ = y * x + (y + succ x) := by rw [add_assoc]
      _ = y * x + (succ y + x) := by
        have h1 : y + succ x = succ (y + x) := rfl
        have h2 : succ (y + x) = succ y + x := by
          calc succ (y + x)
            = succ (x + y) := by rw [add_comm y x]
            _ = succ x + y := by rw[add_succ]
            _ = x + succ y := by
                calc x.succ + y
                = x + 1 + y := by rfl
                _ = x + (1 + y) := by rw[add_assoc]
                _ = x + (y + 1) := by rw[add_comm 1 y]
            _ = succ y + x := by rw [add_comm]
        rw [h1, h2]
      _ = (y * x + x) + succ y := by rw [add_assoc, add_comm x (succ y), ← add_assoc]
      _ = succ y * x + succ y := by rw [← ih]
      _ = succ y * succ x := rfl

  theorem induction_game_lvl_5_alt : ∀ x y : ℕ, y * x + x = succ y * x := by
    intro x
    induction x with
    | zero =>
      intro y
      rfl
    | succ x ih =>
      intro y
      calc y * (x + 1) + (x + 1)
        = succ (y * x.succ + x) := by rfl
      _ = succ (y * x + y + x) := by rfl
      _ = succ (y * x + (y + x)) := by rw[add_assoc]
      _ = succ (y * x + (x + y)) := by rw[add_comm y x]
      _ = succ (y * x + x + y) := by rw[add_assoc]
      _ = succ (y.succ * x + y) := by rw[ih]
      _ = y.succ * (x + 1) := by rfl
  /-

  Part 2 : Show that `≥` is antisymmetric and `max` is a commutative monoid.

  -/

  /- Showing that `≥` is antisymmetric. -/

  -- needed for assignment - `sorry`
  theorem anti_sym_lem : ∀ x y : ℕ , x + y = y → x = 0 := by
    intro x y
    intro h
    induction y with
    | zero =>
      assumption
    | succ y ih =>
      have h1 : x + y.succ = y.succ := by
        calc x + y.succ = y + 1 := h
        _ = succ y := rfl
      have h2 : succ (x + y) = succ y := by
        calc succ (x + y)
          = x + succ y := by rfl
        _ = y.succ := by rw[h1]
      injection h2 with h3
      exact ih h3



  -- needed for assignment - `sorry`
  theorem add_lem : ∀ x y : ℕ , x + y = 0 → x = 0 := by
    intro x y
    intro h
    induction y with
    | zero =>
      assumption
    | succ y ih =>
      have h1 : x + y.succ = 0 := by
        calc x + y.succ
        = x + (y + 1) := by rfl
        _ = 0 := by rw[h]
      have h2 : y.succ + x = 0 := by
        calc y.succ + x
        = x + y.succ := by rw[add_comm]
        _ = 0 := by rw[h1]
      have h3 : succ (y + x) = 0 := by
        calc succ (y + x)
        = y.succ + x := by rw[←add_succ]
        _ = 0 := by rw[h2]
      cases h3

  theorem add_lem_alt : ∀ x y : ℕ , x + y = 0 → x = 0 := by
    intro x
    induction x with
    | zero =>
      intro y
      induction y with
      | zero =>
        intro h
        rfl
      | succ y ih =>
        intro h
        cases h
    | succ x ih =>
      intro y
      intro h
      have h1 : succ (x + y) = 0 := by
        rw[add_succ] at h
        assumption
      cases h1

  /- antisymmetry of ≥ -/
  theorem anti_sym : ∀ x y : ℕ , x ≥ y → y ≥ x → x = y := by
  intro x y hxy hyx
  cases hxy with
  | intro k hk =>
    cases hyx with
    | intro j hj =>
      have h : y + k + j = y := by
        calc y + k + j
            = k + y + j := by rw[add_comm y k]
          _ = x + j := by rw [hk]
          _ = j + x := by rw[add_comm]
          _ = y := hj
      have hkj : k + j = 0 := by
        have h1 : y + (k + j) = y := by
          rw [add_assoc] at h
          rw [h]
        have h2 : (k + j) + y = y := by
          rw[add_comm]
          assumption
        rw[anti_sym_lem (k + j) y]
        assumption
      cases k with
      | zero =>
        have h3 : 0 + j = j := by
          rw[add_lneutr]
        rw[h3] at hkj
        rw[hkj] at hj
        have h4 : 0 + x = x := by
          rw[add_lneutr]
        rw[h4] at hj
        assumption
      | succ k =>
        have h5 : succ (k + j) = 0 := by
          rw[add_succ] at hkj
          assumption
        cases h5

def GE2 : ℕ → ℕ → Prop
| _, 0 => True
| 0, _ => False
| succ m, succ n => GE m n

theorem succ_ge_succ : ∀ m n, succ m ≥ succ n → m ≥ n := by
  intro m n h
  cases h with
  | intro k h1 =>
    cases k with
    | zero =>
      have h2 : n.succ = m.succ := by
        calc n.succ
          = 0 + n.succ := by rw[add_lneutr]
        _ = m.succ := by rw[h1]
      injection h2 with hnm
      rw[←hnm]


theorem anti_sym_alt : ∀ x y : ℕ, x ≥ y → y ≥ x → x = y := by
  intro x y hxy hyx
  induction x generalizing y with
  | zero =>
    cases y with
    | zero => rfl
    | succ y =>
      cases hxy with
      | intro k h1 =>
        cases h1
  | succ x ih =>
    cases y with
    | zero =>
      cases hyx with
      | intro k h1 =>
        cases  h1
    | succ y =>




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
    induction n with
    | zero =>
      rfl
    | succ n ih =>
      rfl


  theorem max_rneutr : ∀ n : ℕ, max n 0 = n := by
    intro n
    induction n with
    | zero =>
      rfl
    | succ n ih =>
      rfl

  -- Hint: strong induction.
  theorem max_assoc : ∀ l m n : ℕ, max (max l m) n = max l (max m n) := by
    intro l m n
    induction n with
    | zero =>
      induction m with
      | zero =>
        calc max (max l 0) 0
          = max l 0 := by rw[max_rneutr]
        _ = max l (max 0 0) := by rfl
      | succ m ih =>
          calc max (max l (succ m)) 0
          = max l (succ m) := by rw [max_rneutr]
          _ = max l (max (succ m) 0) := by rw [max_rneutr]
    | succ n ih =>
      induction l with
      | zero =>
        calc max (max 0 m) (n + 1)
          = max m (n + 1) := by rw[max_lneutr]
        _ = max 0 (max m (n + 1)) := by rw[max_lneutr]
      | succ l ih' =>
        induction m with
        | zero =>
          calc max (max (l + 1) 0) (n + 1)
            = max (l + 1) (n + 1) := by rw[max_rneutr]
          _ = max (l + 1) (max 0 (n + 1)) := by rw[max_lneutr]
        | succ m ih'' =>
          calc max (max (l + 1) (m + 1)) (n + 1)
            = max (succ (max l m)) n.succ := by rfl
          _ = succ (max (max l m) n) := by rfl
  sorry

  theorem max_comm : ∀ m n : ℕ, max m n = max n m := by
    intro m n
    induction n with
    | zero =>
      calc max m 0
        = m := by rw[max_rneutr]
      _ = max 0 m := by rw[max_lneutr]
    | succ n ih =>
      sorry

  -- End of tutorial #7 exercises 🍰 --

  /-
  If you reached the end and want additional practice, I recommend
  having a go at the exercises from Mark's tutorial #7.
  -/

end tutorial_seven
