/-

Lecture 13 : Natural numbers

-/
notation "ℕ" => Nat -- \bn
open Nat

def add : ℕ → ℕ → ℕ
| m  , zero     => m
| m  , (succ n) => succ (add m n)

def add' : ℕ → ℕ → ℕ
| zero , n => n
| (succ m) , n => succ (add' m n)

#eval add' 5 3

-- m + n = add m n

def mult : ℕ → ℕ → ℕ
| _ , zero => zero
| m , (succ n) => mult m n + m

-- m * n = mult m n

def exp : ℕ → ℕ → ℕ
| _ , zero => 1
| m , succ n => exp m n * m

-- m^m = exp m n

theorem add_rneutr : ∀ n : ℕ, n + 0 = n := by
intro n
rfl

-- m + 1 = m + (succ zero) = succ (m + 0) = succ m
-- succ m = m.succ



theorem add_assoc :
  ∀ l m n : ℕ , (l + m) + n = l + (m + n) := by
intro l m n
induction n with
| zero =>
    calc  (l + m) + 0
            = l + m := by rfl
          _ = l + (m + 0) := by rfl
| succ n ih =>
    calc (l + m) + (succ n)
        = succ ((l + m) + n) := by rfl
      _ = succ (l + (m + n)) := by rw [ih]
      _ = l + (succ (m + n)) := by rfl
      _ = l + (m + (succ n)) := by rfl

theorem add_lneutr : ∀ n : ℕ, 0 + n = n := by
intro n
induction n with
| zero => rfl
| succ m ih =>
    calc (0 + succ m)
      = succ (0 + m) := by rfl
      _ = succ m := by rw [ih]

theorem addsucc : ∀ l m : ℕ,
    (succ l) + m = succ (l + m) := by
    intro l m
    induction m with
    | zero => rfl
    | succ m ih =>
        calc
          (succ l) + (succ m)
            = succ (succ l + m) := by rfl
          _ = succ (succ (l + m)) := by rw [ih]
          _ = succ (l + (succ m)) := by rfl

theorem add_comm :
∀ l m : ℕ, l + m = m + l := by
intro l m
induction m with
| zero =>
    calc l + 0
           = l := by rfl
         _ = 0 + l := by rw [add_lneutr]
| succ m ih =>
    calc l + (succ m)
         = succ (l + m) := by rfl
       _ = succ (m + l) := by rw [ih]
       _ = (succ m) + l := by rw [← addsucc]

-- (ℕ , 0 , +) are a commutative monoid
-- (ℕ , 1 , *) are a commutative monoid
-- (Matr , I , *) is a monoid
-- (ℕ → ℕ , id , ∘ ) is a monoid
-- (A → B ??? ) is a category

-- distributivity
-- (l + m) * n = l * n + m * n
-- n * (l + m) = n * l + n * m
-- 0 * n = 0
-- n * 0 = 0
-- semiring
-- what is a ring ?
