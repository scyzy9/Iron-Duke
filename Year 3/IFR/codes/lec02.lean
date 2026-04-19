example (P Q R : Prop) :
  (P → Q) → ((Q → R) → (P → R)) := by
  intro hPQ        -- 蕴含引入 (implication introduction)
  intro hQR
  intro hP
  exact hQR (hPQ hP)

theorem swap (P Q R : Prop) :
(P → Q → R ) → (Q → P → R) := by
intro pqr q p
apply pqr
.assumption
.assumption
