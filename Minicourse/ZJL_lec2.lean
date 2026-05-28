import Mathlib

/-
open Nat

def succ := 1

#check succ
-/

/-
open Real

#check π
-/

/-
open Topology

#check 𝓝 (0 : ℝ)
-/

-- example {a b c d} (h : a ∧ b ∧ c ∧ d) : 1 = 1 := by
--   have := h.2.2.2
--   sorry

-- example {M : Matrix (Fin 2) (Fin 2) ℕ} : M = !![1, 2, 2; 3, 2, 1] := by
--   sorry

-- example {α} {a b : α} [LE α] (h : a = b) : a ≤ b := by
--   sorry

-- example {α} {a b : α} [Preorder α] (h : a = b) : a ≤ b := by
--   exact Std.le_of_eq h

/-
variable {a b c : ℕ} (h : a = b)

theorem d : a + c = b + c := by
  rw [h]
-/
