import MathLib

example (x q : Nat) : 37 * x + q = 37 * x + q := rfl

example (x : ℝ) : x = x := rfl

example (P : Prop) : P → P := by
  intro a
  exact a

-- in the following, p and q are hypotheses, and then constructor splits the goal into two pieces.
example (P Q : Prop) (p : P) (q : Q) : P ∧ Q := by
  constructor
  exact p
  exact q



example (P Q : Prop) : (P → Q) → (¬ Q → ¬ P) := by
  unfold Not
  intro a
  intro b
  intro c
  apply b
  apply a
  exact c


-- The following are two proofs of the same statement

example (P Q : Prop) : (P ∧ ¬ P) → Q := by
  intro a
  have left := a.1
  have right := a.2
  exfalso
  exact a.2 a.1

example (P Q : Prop) : (P ∧ ¬ P) → Q := by
  intro a
  have := a.2 a.1
  contradiction


example (G : Type) (hg : Group G) (a b c : G) : a * a⁻¹ * 1 * b = b * c * c⁻¹ := by
  simp


example (x : Nat) : x ≤ 1 + x := by
  rw[le_iff_exists_add]
  use 1
  linarith
