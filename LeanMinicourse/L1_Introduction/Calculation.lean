import Mathlib
import ReaperTac

open Real

#leansearch "Real if a / b = c then a = b * c."



example (a b c : ℝ) : a * b * c = b * c * a := by
  rw [mul_assoc]
  rw [mul_comm]


lemma div_eq_if_eq_mul {a b c : ℝ} (h : c ≠ 0) : a / b = c → a = c * b := by
  intro h₁
  rw [← h₁] at h
  rw [div_ne_zero_iff] at h
  rw [(div_eq_iff h.right)] at h₁
  exact h₁

/-
1. introduce rw
2. introduce simp
3. introduce ring
4. introduce have
-/

-- #herald "Real if a / b = c then a = b * c."
/-- 2024 Gaokao Xinkebiao I - 4:  -/
theorem gaokao_triangle (α β m : ℝ) (h₁ : cos (α + β) = m) (h₂ : tan α * tan β = 2) :
  cos (α - β) = -3 * m := by
  rw [tan_eq_sin_div_cos, tan_eq_sin_div_cos] at h₂
  rw [mul_comm_div, div_div, mul_div] at h₂
  apply div_eq_if_eq_mul at h₂
  rw [cos_add] at h₁
  rw [h₂] at h₁
  rw [cos_sub]
  rw [h₂]
  rw [← h₁]
  ring
  simp
