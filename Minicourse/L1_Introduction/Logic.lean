/-
In this section, we will learn how to prove
-/
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Real.StarOrdered

/- The classical definitiion of limit in `ε-δ` language. -/
def epsilon_delta_limit (f : ℝ → ℝ) (l : ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, 0 < |x - a| ∧ |x - a| < δ → |f x - l| < ε

/- Infinite version of limit in `ε-δ` language -/
def epsilon_delta_limit_inf (f : ℝ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x > δ, |f x - l| < ε

/- The limit of `1/x` as `x` approaches ∞ is `0`. -/
theorem limit_of_one_div_x_eq_zero :
  epsilon_delta_limit_inf (fun x => 1 / x) 0 := by
  -- `unfold` to definitively unfold declarations (totally unnessary)
  unfold epsilon_delta_limit_inf
  -- `intro` to introduce free vars in the universal quantifiers
  -- `intro` automatically match the free variables in order
  -- syntax of `∀ ε > 0,` is a short form of `∀ ε, ε > 0 →`,
  -- so we need to introduce both `ε : ℝ` and `hε : ε > 0`
  intro ε hε
  -- `use` to directly specify the var in the existence quantifier,
  -- `∃ δ > 0,` is a short form of `∃ δ, δ > 0 ∧`, so after specify
  -- the value of `δ`, we need to first prove `δ > 0`.
  use 1 / ε
  -- `constructor` to split the `∧` connector
  constructor
  -- `·` to focus on the main goal (unnessary, but for a neat proof)
  -- Here `simp` tactic uses a set of predefined lemmas to simplify
  -- the goal, type `simp?` to see the exact list of lemmas used.
  · simp [hε]
  -- `intro` works the same
  intro x hx
  -- Later we find that `x > 0` is needed for multiple times,
  -- so we can use `have` to prove this fact in the first place.
  have x_pos : x > 0 := by
    -- keyword `trans` represents the transitivity of an operation,
    -- here it means the transitivity of `>`. It works if you want
    -- to prove `a > b` by proving `a > c > b`.
    apply gt_trans hx
    simp [hε]
  simp only [sub_zero]
  -- Enter a `calc` mode to chain multiple inequalities
  calc
    _ = 1 / x := by
      rw [abs_of_pos]
      simp [x_pos]
   _ < ε := by
      -- `gt_iff_lt` means `a > b` is equivalent to `b < a`,
      -- you will need this very often.
      rw [gt_iff_lt] at hx
      -- It takes some time to get mul and div right ...
      rw [div_lt_iff₀ hε] at hx
      rw [mul_comm, ← div_lt_iff₀ x_pos] at hx
      exact hx

/- Use term trick to reduce the length -/
theorem limit_of_one_div_x_eq_zero' :
  epsilon_delta_limit_inf (fun x => 1 / x) 0 := fun ε hε =>
  ⟨1/ε, ⟨by simp [hε], fun x hx => by
    have x_pos : x > 0 := gt_trans hx (by simp [hε])
    rw [sub_zero, abs_of_pos (by simp [x_pos])]
    rw [gt_iff_lt, div_lt_iff₀ hε, mul_comm,
    ← div_lt_iff₀ x_pos] at hx
    exact hx⟩⟩
