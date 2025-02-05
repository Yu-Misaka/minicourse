import Mathlib
import ReaperTac

open Real

/- Directly give the type of the proof -/
example (a b c : ℝ) : a * b * c = a * (b * c) :=
  mul_assoc a b c

/- Most of time it is challenging to directy give the proof,
so we choose to prove it interactively and step-by-step. This
is a tactic mode. -/
example (a b c : ℝ) : a * b * c = a * (b * c) := by
  exact mul_assoc a b c

/- We can also use the `rewrite` tactic to rewrite the goal -/
example (a b c : ℝ) : a * b * c = b * c * a := by
  rewrite [mul_assoc]
  rewrite [mul_comm]
  exact rfl -- rfl is a tactic that shows `x = x`, a reflexive proof

/- `rw` is a tactic combining `rewrite` and `rfl`, it tries to
apply `rfl` immediately after `rewrite` -/
example (a b c : ℝ) : a * b * c = b * c * a := by
  rw [mul_assoc]
  rw [mul_comm]
  -- rw [mul_comm, mul_assoc]

/- A `calc` block allows you to proof an inequality step by step. -/
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      rw [mul_add, add_mul, add_mul]
    _ = a * a + (b * a + a * b) + b * b := by
      rw [← add_assoc, add_assoc (a * a)]
    _ = a * a + 2 * (a * b) + b * b := by
      rw [mul_comm b a, ← two_mul]

/- `ring` is a tactic that can solve equations involving rings -/
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  ring

/- Here is a harder theorem, and an interesting property for real number. -/
lemma div_eq_of_eq_mul₀ {a b c : ℝ} (h : c ≠ 0) : a / b = c → a = c * b := by
  intro h₁
  rw [← h₁] at h
  rw [div_ne_zero_iff] at h
  have := h.right
  rw [(div_eq_iff this)] at h₁
  exact h₁

/-
1. introduce rw
3. introduce ring
4. introduce have
-/

#leansearch "Real.tan is equal to sin div by cos"

-- #herald "Real if a / b = c then a = b * c."
/-- 2024 Gaokao Xinkebiao I - 4:  -/
theorem gaokao_triangle (α β m : ℝ) (h₁ : cos (α + β) = m) (h₂ : tan α * tan β = 2) :
  cos (α - β) = -3 * m := by
  have : tan α * tan β = (sin α * sin β) / (cos α * cos β) := by
    calc
      tan α * tan β = (sin α / cos α) * (sin β / cos β) := by
        rw [tan_eq_sin_div_cos, tan_eq_sin_div_cos]
      _ = (sin α * sin β) / (cos α * cos β) := by
        rw [mul_comm_div, div_div, mul_div, mul_comm (cos α)]
  rw [this] at h₂
  apply div_eq_of_eq_mul₀ at h₂
  rw [cos_add] at h₁
  rw [h₂] at h₁
  rw [cos_sub]
  rw [h₂]
  rw [← h₁]
  ring
  simp
