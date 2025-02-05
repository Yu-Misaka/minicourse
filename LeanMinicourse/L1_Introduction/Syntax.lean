import Mathlib

open Nat
/-
# Dependent Type theory

A framework for formalizing mathematics and logic reasoning. It is based on the idea that each value has a type.

-/
-- Display the type of your value.
#check 2 + 2
#eval 2 + 2

#check ℕ

#check 2 / 3
#eval 2 / 3
#check 2 - 3 -- Something went wrong here.
#eval 2 - 3

-- Explicitly declare the type of your value.
#check (2 : ℚ)
#eval (2 / 3 : ℚ)
#eval (2 - 3 : ℤ)

-- Define a variable.
def a : ℕ := 2
def b : ℕ := 3

-- You can use existing types to construct new types.
#check List ℕ
#check Finset ℕ
#check Set ℕ
#check ℕ → ℕ

/- Some types are representable, then you can show them. But some are not. -/
def finset_two : Finset ℕ := {1, 2}
#eval finset_two
def list_two : List ℕ := [1, 2]
#eval list_two
def set_two : Set ℕ := {1, 2}
-- #eval set_two -- This will not work.

/- Construct the function type using existing types -/
def g : ℕ → ℕ :=
  fun x => x + 3

/- A more common way is to use `()` to specify the parameter -/
def f (x : ℕ) : ℕ :=
  x + 3

/- You can also define a function with other types -/
def f_real (x : ℝ) :=
  x + 3

#check f
#eval f 3
#check g
#check f_real


/- The most important type in Lean is the Proposition type. This how you can construct theorems. A proof of a proposition is a value of that type. -/

/- This is a very simple proposition. -/
def easy_prop : Prop :=
  2 + 2 = 4

/- Of course we can define more complicated -/

/- These are proofs of propositions. -/
theorem easy : 2 + 2 = 4 :=
  rfl

/-
Note that the type of `easy` is `2 + 2 = 4`. Its value is `rfl`, which is a proof of the proposition.
-/
#check easy

/- The classical definitiion of limit in `ε-δ` language. -/
def epsilon_delta_limit (f : ℝ → ℝ) (l : ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, 0 < |x - a| ∧ |x - a| < δ → |f x - l| < ε

#check epsilon_delta_limit

/-  -/
theorem epsilon_delta_limit_of_f_real : epsilon_delta_limit f_real 3 6 := sorry

#check epsilon_delta_limit_of_f_real

def FermatLastTheorem' :=
  ∀ x y z n : ℕ, n > 2 ∧ x * y * z ≠ 0 → x ^ n + y ^ n ≠ z ^ n

#check FermatLastTheorem'

theorem hard : FermatLastTheorem' :=
  sorry

#check hard


/- Here are some proofs from MIL -/
example : ∀ m n : Nat, Even n → Even (m * n) := fun m n ⟨k, (hk : n = k + k)⟩ ↦
  have hmn : m * n = m * k + m * k := by rw [hk, mul_add]
  show ∃ l, m * n = l + l from ⟨_, hmn⟩

example : ∀ m n : Nat, Even n → Even (m * n) :=
fun m n ⟨k, hk⟩ ↦ ⟨m * k, by rw [hk, mul_add]⟩

example : ∀ m n : Nat, Even n → Even (m * n) := by
  -- Say `m` and `n` are natural numbers, and assume `n = 2 * k`.
  rintro m n ⟨k, hk⟩
  -- We need to prove `m * n` is twice a natural number. Let's show it's twice `m * k`.
  use m * k
  -- Substitute for `n`,
  rw [hk]
  -- and now it's obvious.
  ring

example : ∀ m n : Nat, Even n → Even (m * n) := by
  rintro m n ⟨k, hk⟩; use m * k; rw [hk]; ring

example : ∀ m n : Nat, Even n → Even (m * n) := by
  intros; simp [*, parity_simps]

/-- 2024 Gaokao -/
example {A B : Set ℝ} (h₁ : A = {x | -5 < x ^ 3 ∧ x ^ 3 < 5}) (h₂ : B = {-3, -1, 0, 2, 3}) : A ∩ B = {-1, 0} := by
  ext x
  constructor
  · intro h
    rw [Set.mem_inter_iff] at h
    rcases h with ⟨hA, hB⟩
    simp [h₂] at *
    simp [h₁] at *
    repeat' cases' hB with h_eq hB
    · simp [h_eq] at *; linarith
    · simp [h_eq] at *
    · simp [h_eq] at *
    · simp [h_eq] at *; linarith
    · linarith
  intro h
  simp [h₁, h₂] at *
  cases' h with h h
  all_goals {simp [h]; repeat constructor; linarith; linarith}



#min_imports
