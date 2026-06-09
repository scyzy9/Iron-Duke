-- Welcome to the COMP2065 (IFR) Tutorial #8!

namespace warrens_tutorial_8

  set_option pp.fieldNotation false
  set_option tactic.customEliminators false

  variable {A B C : Type}

  open List

  /- Definitions from the lecture -/

  -- From the lecture - definition of `snoc`
  def snoc : List A → A → List A
  | [] , a => [a]
  | a :: as , b => a :: (snoc as b)

  -- From the lecture - definition of append (`append`)
  def append : List A → List A → List A
  | [], xs => xs
  | (x::xs), ys => x :: (append xs ys)

  infixr:65(priority := 1001) " ++ " => append

  -- From the lecture - definition of `rev`
  def rev : List A → List A
  | [] => []
  | (a :: as) => snoc (rev as) a

  -- From the lecture - definition of `revaux`
  def revaux : List A → List A → List A
  | [], bs => bs
  | (a :: as), bs => revaux as (a :: bs)

  -- From the lecture - definition of `fastrev`
  def fastrev (l : List A) : List A
    := revaux l []

  -- theorem from the lecture - useful later on
  theorem app_rneutr : ∀ as : List A, as ++ [] = as := by
    intro as
    induction as with
    | nil =>
      rewrite [append]
      rfl
    | cons a as ih =>
      rewrite [append,ih]
      rfl
theorem app_lneutr : ∀ as : List A , [] ++ as = as := by
  intro as
  rfl

theorem  app_assoc : ∀ as bs cs : List A , (as ++ bs) ++ cs = as ++ (bs ++ cs) := by
  intro as bs cs
  induction as with
  | nil =>
    rfl
  | cons a as' ih =>
    calc (a :: as' ++ bs) ++ cs
      = a :: (as' ++ bs) ++ cs := by rfl
    _ = a :: ((as' ++ bs) ++ cs) := by rfl
    _ = a :: (as' ++ bs ++ cs) := by rw[ih]


  /- Part 1 :: `cons` and `snoc` -/


  -- `cons` (::) puts an element on the front of a list of elements of the same Type
  #reduce cons 1 [2,3]
  #reduce 1::[2,3]

  #reduce [1]::[[2,3],[4]]


  -- `append` appends two lists
  #reduce append [1] [2,3]
  #reduce [1] ++ [2,3]

  #reduce [[1]] ++ [[2], [3]] ++ [[4]]

  -- `snoc` puts an element on to the end of a list
  #reduce snoc [3,2] 1
  #reduce snoc [[3,2]] (snoc [1] 4)

  -- all lists are `cons` lists of elements with other lists
  -- i.e. `[1,2,3] = 1::(2::(3::[]))`
  example : [1,2,3] = cons 1 (cons 2 (cons 3 [])) := by
    rfl

  -- `snoc` defines lists in the reverse way to using `cons`
  -- i.e. `[1,2,3] = (([]--1)--2)--3`
  example : [1,2,3] = snoc (snoc (snoc [] 1) 2) 3 := by
    calc
      [1, 2, 3]
      _ = snoc [1, 2] 3 := by rfl
      _ = snoc (snoc [1] 2) 3 := by rfl
      _ = snoc (snoc (snoc [] 1) 2) 3 := by rfl


  /- **----------------------------------------** -/
  /- Part 1 - Recap - `Lists`, `cons` and `snoc`.** -/
  /- **----------------------------------------** -/

  example : ∀ as : List A, ∀ a : A, a :: as = [] ++ a :: as := by
    intro as a
    induction as with
    | nil =>
      rfl
    | cons a' as ih =>
      calc a :: a' :: as
      _ = [] ++ a :: a' :: as := by rw[app_lneutr]

  example : ∀ as : List A, ∀ a : A, a :: as = a :: ([] ++ as) := by
    intro as a
    induction as with
    | nil =>
      rfl
    | cons a' as ih =>
      calc a :: a' :: as
      _ = a :: ([] ++ a' :: as) := by rw[app_lneutr]

  example : ∀ as : List A, ∀ a : A, a :: as = (a :: []) ++ as := by
    intro as a
    induction as with
    | nil =>
      rfl
    | cons a' as ih =>
      rfl

  -- here we append with nil whose case is defined as `app xs [] := xs`
  example : ∀ as : List A, ∀ a : A, a :: as = a :: as ++ [] := by
    intro as a
    induction as with
    | nil =>
      rfl
    | cons a' as ih =>
      calc a :: a' :: as
      = a :: a' :: as ++ [] := by rw[app_rneutr]

  /- **-----------------------------------------------------** -/
  /- ------------------ Part 1 - Exercises. ------------------ -/
  /- **-----------------------------------------------------** -/

  theorem singleton_lem : ∀ as : List A, ∀ a : A, [a] ++ as = a :: as := by
    intro as a
    rfl

  -- here we append to a non-empty list whose case
  -- is defined as `(x::xs) ys := x :: (app xs ys)`
  theorem consnoc : ∀ as : List A, ∀ a : A, as ++ [a] = snoc as a := by
    intro as a
    induction as with
    | nil =>
      rfl
    | cons a' as ih =>
      calc a' :: as ++ [a]
        = a' :: (as ++ [a]) := by rw[append]
      _ = a' :: (snoc as a) := by rw[ih]
      _ = snoc (a' :: as) a := by rfl

  -- Use the previously defined lemma to help you to prove `consappsnoc`
  -- Think about what you need to prove and what the `consnoc` lemma says
  -- This proof becomes very easy once you realise the power of more general lemmas!
  theorem consappsnoc : ∀ ns : List A, ∀ m n : A, m :: (rev ns) ++ [n] = snoc (m :: (rev ns)) n := by
    intro ns m n
    rw[consnoc]

  /- **--------------------------------------** -/
  /- Part 2 - Recap - `fastrev` and `revaux`.** -/
  /- **--------------------------------------** -/

  --  Definitions from the lecture
  --
  --  def fastrev (l : list A) : list A := revaux l []
  --
  --  def revaux : list A → list A → list A
  --  | [] bs := bs
  --  | (a :: as) bs := revaux as (a :: bs)

  example : ∀ as : List A, ∀ a : A, (fastrev [a] ++ as) = a :: as := by
    intro as a
    rfl

  /- **-----------------------------------------------------** -/
  /- ------------------ Part 2 - Exercises. ------------------ -/
  /- **-----------------------------------------------------** -/

  -- use only `intro`, `rewrite`, and `rfl` to prove the following
  theorem revsnoc_consinv : ∀ a b : A, rev (snoc [a] b) = b :: [a] := by
    intro a b
    rfl

  -- [Hint] - Useful lemma for `snocrevlem`
  theorem snocapplem : ∀ as : List A, ∀ a : A, snoc as a = as ++ [a] := by
  intro as a
  induction as with
  | nil =>
    rfl
  | cons a' as ih =>
    calc snoc (a' :: as) a
      = a' :: snoc as a := by rfl
    _ = a' :: (as ++ [a]) := by rw[ih]
    _ = a' :: as ++ [a] := by rfl

  theorem snocapplem_better : ∀ as : List A, ∀ a : A, snoc as a = as ++ [a] := by
    intro as a
    sorry


  -- [Hint] - The a few of the lemmas we have proven are useful!
  theorem snocrevlem : ∀ as : List A, ∀ a : A, snoc (rev as) a = rev as ++ [a] := by
    intro as a
    sorry


  -- Actually, `snocapplem` is even more useful if we consider that it is defined for all lists `as`
  -- Redo the previous proof with a single `rewrite` in at most 3 lines.
  -- Note, you are not allowed to just apply/rewrite snocrevlem
  theorem snocrevlem_better : ∀ as : List A, ∀ a : A, snoc (rev as) a = rev as ++ [a] := by
    intro as a
    rw[consnoc]

  -- End of tutorial #8 exercises 🍰 --

end warrens_tutorial_8
