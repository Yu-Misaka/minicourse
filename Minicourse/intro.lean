import Mathlib

section eval_and_check

#check 1
#check 1 + 1
#eval 1 + 1

#check 1 - 2
#eval 1 - 2

#check 1 / 3
#eval 1 / 3

#check (1 : ℤ) - 2
#eval (1 : ℤ) - 2

#check (1 : ℚ) / 3
#eval (1 : ℚ) / 3

#check 1 + 1 = 2

section internal

open Lean Meta Elab

elab "#stx" "[" t:term "]" : command => do
  logInfo m!"Syntax: {t};\n{repr t}"

elab "#expr" "[" t:term "]" : command =>
  Command.liftTermElabM do
  let t ← Term.elabTerm t none
  let t ← instantiateMVars t
  logInfo m!"Expression: {t}:\n{repr t}"
  let t ← reduce t
  let t ← instantiateMVars t
  logInfo m!"Reduced: {t}:\n{repr t}"

#stx [1 + 1]
#expr [1 + 1]

end internal

end eval_and_check

-- def 名称 : 类型 := 值
def a : ℕ := 1
#check a
#eval a

def f : ℕ → ℕ := fun x ↦ x + 1
#check f
#eval f 1

def f' (x : ℕ) : ℕ := x + 1
#check f'
#eval f' 1

-- def 名称 {隐式参数} [隐式参数] (显式参数) : 类型 := 值
def mul {G : Type*} [Group G] (a b : G) : G := a * b
#check mul
#print mul

variable {G : Type*} [Group G]
def mul' (a b : G) : G := a * b

set_option trace.Meta.synthInstance true
def mul'' (a b : G) : G := a * b

--类型转换
variable {F E C : Type*} [Field F] [Field E] [Field C]
  [Algebra F E] [Algebra E C] {H : IntermediateField F E}

set_option trace.Meta.synthInstance false

-- def mul_1 (a : H) (b : C) : C := a * b

def mul_2 (a : H) (b : C) : C := ((algebraMap E C).comp (algebraMap H E) a) * b

def mul_3 (a : H) (b : C) : C := a • b

-- example {隐式参数} [隐式参数] (显式参数) : 类型 := 值
example (a : H) (b : C) : mul_2 a b = mul_3 a b := sorry

-- theorem 名称 {隐式参数} [隐式参数] (显式参数) : 类型 := 值
--             ↑ 条件1    ↑ 条件2    ↑ 条件3    ↑ 结论  ↑ 证明
theorem eq_2_3 (a : H) (b : C) : mul_2 a b = mul_3 a b := sorry

example (a : H) (b : C) : mul_2 a b = mul_3 a b := by
  unfold mul_2 mul_3
  rw [Algebra.smul_def]
  rfl

example (a : H) (b : C) : mul_2 a b = mul_3 a b := by
  simp [mul_2, mul_3, (Algebra.smul_def _ b).symm]; rfl

example (a : H) (b : C) : mul_2 a b = mul_3 a b := (Algebra.smul_def _ b).symm

-- example : mul_2 = mul_3 := sorry
example : mul_2 (H := H) (C := C) = mul_3 := by
  funext a b
  exact (Algebra.smul_def _ b).symm

example : ∀ a : H, ∀ b : C, mul_2 a b = mul_3 a b := by
  intro a b
  exact (Algebra.smul_def _ b).symm
