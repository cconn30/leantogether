import MathLib
set_option linter.style.longLine false

-- Lecture 1: The Story of Real Analysis

example (x : ℝ) (h : x = 5) : x = 5 := by
  apply h

example (x y : ℝ) : x ^ 2 + 2 * y = x ^ 2 + 2 * y := by
  rfl

example (x y : ℝ) (Bob : x = 2) : x + y = 2 + y := by
  rewrite [Bob]
  rfl -- note that we could instead do rw [Bob] and this would take care of rfl.

example (x y : ℝ) : (x + y)^3 = x^3 + 3*x^2*y + 3*x*y^2 + y^3 := by
  ring_nf -- sets both sides of equation to expanded normal form and checks reflexivity

example (x y : ℝ) : ∃ (c : ℝ), (x + y)^4 = x^4 + 4*x^3*y + c*x^2*y^2 + 4*x*y^3 + y^4 := by
  use 6
  ring_nf

example : ∀ ε : ℝ, ε > 0 → (ε + 1)^2 = (ε + 1)^2 := by
  intro e -- fix e(psilon)
  intro he -- suppose e is such that e>0
  rfl

-- If f(x)=x^2, then f(t)=t^2.
example (t : ℝ) (t_pos : t > 0) (f : ℝ → ℝ) (hf : ∀ x > 0, f (x) = x^2) : f (t) = t^2 := by
  specialize hf t -- uses t in hypothesis hf
  specialize hf t_pos -- makes it so that the t in hf is positive
  apply hf

-- If there exists a point where f equals 2, then there exists a point where f^2 equals 4.
example (f : ℝ → ℝ) (h : ∃ c : ℝ, f c = 2) : ∃ x : ℝ, (f x) ^ 2 = 4 := by
  choose c hc using h -- create hypothesis about c using h, naming it hc
  use c
  rewrite [hc]
  ring_nf

-- Let f:R to R, and suppose there exists a real a such that f(a)=3, and also for any x>0, f(x+1)=f(x)+9.
-- Then there exists a real b such that for all y>0, f(y+1)^2=(f(y)+(f(b))^2)^2.
example (f : ℝ → ℝ) (h_existential : ∃ (a : ℝ), f (a) = 3) (h_universal : ∀ x > 0, f (x + 1) = f (x) + 9) : ∃ (b : ℝ), ∀ y > 0, f (y + 1)^2 = (f (y) + (f b)^2)^2 := by
  choose a ha_e using h_existential
  use a
  intro y
  intro hy
  rewrite [ha_e]
  rewrite [h_universal]
  ring_nf
  apply hy

-- Cheat sheet:
-- ∀+Goal: intro
-- ∀+Hypothesis : specialize
-- ∃+Goal : use
-- ∃+Hypothesis : choose


-- Problem Set 1

example (f : ℝ → ℝ) (h : ∀ u, f (u) = 2 * u + 1) : ∃ a, f (3) = a := by
  specialize h 3
  rewrite [h]
  use 7
  ring_nf


example : ∃ c, ∀ x y : ℝ, x ^ 2 + y ^ 2 = 2 → x * y = 1 → (x + y) ^ 2 = c := by
  have huv (u v : ℝ) : (u + v)^2 = (u^2 + v^2) + 2*(u*v) := by
    ring_nf
  use 4
  intro u v
  intro hu hv
  specialize huv u v
  rewrite [hu, hv] at huv
  rewrite [huv]
  ring_nf


example (g : ℝ → ℝ) (h1 : ∀ x, g (x + 1) = g (x) + 3) (h2 : g (0) = 5) : g (1) = 8 := by
  specialize h1 0
  rewrite [h2] at h1
  ring_nf at h1
  exact h1


example (g : ℝ → ℝ) (h1 : ∀ x, g (x + 1) = g (x) + 3) (h2 : g (0) = 5) : g (2) = 11 := by
  have h3 : g (0 + 1) = g (0) + 3 := by
    apply h1 0
  specialize h1 1
  ring_nf at h3
  rewrite [h3, h2] at h1
  ring_nf at h1
  exact h1
