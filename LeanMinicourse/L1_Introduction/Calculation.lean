import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Complex.Trigonometric
import ReaperTac
-- import Paperproof

open Real

/- Directly give the type of the proof -/
example (a : ℝ) : a = a := rfl

/- Directly give the type of the proof -/
example (a b c : ℝ) : a * b * c = a * (b * c) :=
  mul_assoc a b c

/- Construct the proof once is efficient, but is ugly
and non-human -/
example (a b c : ℝ) : a * b * c = b * c * a :=
  (mul_assoc a b c).trans (mul_comm a (b * c))

/- Most of time it is challenging to directy give the proof,
so we choose to prove it interactively and step-by-step.
The keyword `by` will allow you enter tactic mode.
`exact` is a simple tactic that finishes the proof.
-/
example (a b c : ℝ) : a * b * c = a * (b * c) := by
  exact mul_assoc a b c

example (a : ℝ) : a = a := by
  rfl

/- We can also use the `rewrite` tactic to rewrite the goal
You can rewrite either iff statements or equalities.
 -/
example (a b c : ℝ) : a * b * c = b * c * a := by
  rewrite [mul_assoc]
  rewrite [mul_comm]
  exact rfl -- rfl is a tactic that shows `x = x`, a reflexive proof

/- TODEMO -/
/- `rw` is a tactic combining `rewrite` and `rfl`, it tries to
apply `rfl` immediately after `rewrite` -/
example (a b c : ℝ) : a * b * c = b * c * a := by
  rw [mul_assoc]
  rw [mul_comm]
  -- rw [mul_comm, mul_assoc]

/- Use fact from local contexts `h` `h'` -/
example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h']
  rw [← mul_assoc]
  rw [h]
  rw [mul_assoc]


/- TODEMO -/
/- A `calc` block allows you to proof an equality
or inequality step by step. -/
example (a b : ℝ) : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      rw [mul_add, add_mul, add_mul]
    _ = a * a + (b * a + a * b) + b * b := by
      rw [← add_assoc, add_assoc (a * a)]
    _ = a * a + 2 * (a * b) + b * b := by
      rw [mul_comm b a, ← two_mul]

/- `ring` is a tactic that can solve equations involving rings
First fact about ℝ, it is a ring. -/
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  ring

-- #leansearch "Real.tan is equal to sin div by cos"
#check tan_eq_sin_div_cos

/- TODO -/
lemma tan_mul_eq_sin_mul_div_cos_mul {α β : ℝ} : tan α * tan β = (sin α * sin β) / (cos α * cos β) := by
  calc
      tan α * tan β = (sin α / cos α) * (sin β / cos β) := by
        rw [tan_eq_sin_div_cos, tan_eq_sin_div_cos]
      _ = (sin α * sin β) / (cos α * cos β) := by
        rw [mul_comm_div, div_div, mul_div, mul_comm (cos α)]

/- TODEMO -/
/- Here is a harder theorem, and an interesting property for real number. -/
lemma div_eq_of_eq_mul₀ {a b c : ℝ} (h : c ≠ 0) : a / b = c → a = c * b := by
  intro h₁
  rw [← h₁] at h
  rw [div_ne_zero_iff] at h
  have := h.right
  rw [div_eq_iff this] at h₁
  exact h₁


/- `field_simp` is a carefully crafted tactic to solve problem on field. -/
lemma div_eq_of_eq_mul₀' {a b c : ℝ} (h : b ≠ 0) : a / b = c → a = c * b := by
  intro h₁
  field_simp at h₁
  exact h₁

#leansearch "cos (a+b)"
-- #leansearch "cos (a-b)"

-- #herald "Real if a / b = c then a = b * c."
/-- 2024 Gaokao Xinkebiao I - 4:  -/
theorem gaokao_triangle (α β m : ℝ) (h₁ : cos (α + β) = m) (h₂ : tan α * tan β = 2) :
  cos (α - β) = -3 * m := by
  /- We can use a `have` block to prove some lemmas -/
  have : sin α * sin β = 2 * cos α * cos β := by
    rw [tan_mul_eq_sin_mul_div_cos_mul] at h₂
    rw [mul_assoc 2]
    apply div_eq_of_eq_mul₀
    simp
    exact h₂
  rw [cos_add] at h₁
  rw [this] at h₁
  rw [cos_sub]
  rw [this]
  rw [← h₁]
  ring
