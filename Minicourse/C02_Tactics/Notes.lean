import Mathlib

example (x : ℝ) : x + 0 = x := by
  simp only [add_zero]

@[simp]
theorem my_pow_two (x : ℝ) : x ^ 2 = x * x := by
  linarith

@[simp]
theorem my_double (x : ℝ) : 2 * x = x + x := by
  linarith

example (x : ℝ) : x ^ 2 = x * x := by simp

example (x : ℝ) : 2 * x = x + x := by simp

example (x : ℝ) : 2 * x^2 = x * x + x ^ 2 := by simp

example (x : ℝ) (x_pos : x > 0) : 2 * x + 1 > x + 1 := by
  linarith

example (x : ℝ) (x_pos : x > 0) : (x > 0 ∧ x ≠ 0) ∨ x = 0 := by
  tauto

example (x : ℝ) (x_pos : x > 0) : (x > 0 ∨ x > 2 ∨ x < 0) := by tauto
