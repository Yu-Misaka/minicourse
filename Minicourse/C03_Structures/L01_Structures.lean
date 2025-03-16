import Mathlib

/- 
# Introduction
In this lecture, we first dive into some more advanced tactics. Then explain about general 
organiztion of Lean project.
-/

/- simp
Short hand for simplify
You can manually add `simp` lemmas to let it become more powerful!
-/
example (x : ℝ) : x + 0 = x := by simp

@[simp]
theorem my_real_square (x : ℝ) : x ^ 2 = x * x := by linarith

@[simp]
theorem my_real_two_add (x : ℝ) : 2 * x = x + x := by linarith 

example (x : ℝ) : x ^ 2 = x * x := by simp

example (x : ℝ) : 2 * x ^ 2 = x * x + x * x := by simp

/- linarith
Short hand for linear inequality arithmetics
Use a basic rule set to solve ineqaulity by finding 'counterexample'
-/
example (x : ℝ) (x_pos : x > 0) : 2 * x + 1 > x + 1 := by
  linarith

/- norm_num
Short hand for normalize numerical expressions
Use simplify rules to tackle with + - * ⁻¹ in common number fields
-/
example (x : ℝ) : x ^ 2  + x * x = 2 * x ^ 2 := by norm_num

/- tauto 
Short hand for tautology. It does very good at complex logic connectors
-/
example (x : ℝ) (x_pos : x > 0) : (x > 0 ∧ x ≠ 0) ∨ x = 0 := by tauto

/- omega
Solve integer / natural number problems.
But its current capability is very limited.
-/
example (n : ℕ) : 2 * n = n * 2 := by omega

example (n : ℕ) : n * 2 / 2 = n := by omega

/- aesop 
Search proofs tactic-wise by tree search
-/
example (n : ℕ) : n * 2 / 2 = n := by aesop


/- 

# Structures and typeclasses 
-/
structure Point (α : Type u) where
  x : α
  y : α

def my_point_two_two : Point ℝ := {x := 2, y := 2}

theorem my_point_two_two_eq_two : my_point_two_two.x = 2 := by rfl

/- Positive points -/
structure PositivePoint where
  x : ℚ
  y : ℚ
  x_pos : x > 0
  y_pos : y > 0

/- Addition of points -/
def add_pos_point (p₁ p₂ : PositivePoint) : PositivePoint where
  x := p₁.x + p₂.x
  y := p₂.y + p₂.y
  x_pos := by linarith [p₁.x_pos, p₂.x_pos]
  y_pos := by linarith [p₁.y_pos, p₂.y_pos]
/- Addition of postive points is still positive. -/

/- Structure is one of the fundamental blocks to build mathematics structure.
Only 3 axioms give us a group. Why? -/
structure MyGroup (α : Type u) where
  mul : α → α → α
  one : α
  mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z)
  left_id : ∀ x : α, mul one x = x
  left_inv : ∀ x : α, ∃ y : α, mul y x = one

/- It turns out that the right inverse exists and equals to left inverse -/
theorem my_left_inv_eq_right_inv (hG : MyGroup α) : 
  ∀ x : α, ∃ y : α, hG.mul y x = hG.one ∧ hG.mul x y = hG.one:= by
  intro x
  obtain ⟨y, hy⟩ := hG.left_inv x
  use y
  constructor
  · exact hy
  obtain ⟨z, hz⟩ := hG.left_inv (hG.mul x y)
  have hz' := hz
  rw [← hG.left_id y] at hz
  nth_rw 1 [← hy] at hz
  rw [hG.mul_assoc y] at hz
  rw [← hG.mul_assoc x] at hz
  rw [← hG.mul_assoc z] at hz
  rw [hz'] at hz
  rw [hG.left_id] at hz
  exact hz

/- And right identity exists and equals to left identity -/
theorem my_left_id_eq_right_id (hG : MyGroup α) :
  ∀ x : α, hG.mul hG.one x = x ∧ hG.mul x hG.one = x := by
  intro x
  constructor
  · exact hG.left_id x
  obtain ⟨y, h_left, h_right⟩ := my_left_inv_eq_right_inv hG x
  rw [← h_left]
  rw [← hG.mul_assoc]
  rw [h_right]
  exact hG.left_id x

/- We can define functions for this structure -/
def square (hG : MyGroup α) (x : α) : α := hG.mul x x

/- Now if we want to 'realize' this group, what will happen? -/
def int_add_mygroup : MyGroup ℤ where
  mul := Int.add
  one := 0
  mul_assoc := add_assoc
  left_id := zero_add
  left_inv := by
    intro x
    use -x
    simp

/- It is quite cumbersome because we need to supply the proof each time we do definition!
--> We need a way to 'register' our proof.
--> Here we will get type class in Lean
-/
#eval square {mul:=Int.add, one:=0, mul_assoc:=add_assoc, left_id:=zero_add, left_inv:=by intro x; use -x; simp} 2

theorem square_one (hG : MyGroup α) (x : α) : square hG x = x := by sorry

/- Change `structure` to `class` -/
class MyGroupClass (α : Type u) where
  mul : α → α → α
  one : α
  mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z)
  left_id : ∀ x : α, mul one x = x
  left_inv : ∀ x : α, ∃ y : α, mul y x = one

/- Supply the proof once by `instance`. Then it will be registered in Lean -/
instance : MyGroupClass ℤ where
  mul := Int.add
  one := 0
  mul_assoc := add_assoc
  left_id := zero_add
  left_inv := by
    intro x
    use -x
    simp

#synth MyGroupClass ℤ

/- Tell Lean to look for `MyGroupClass` instance for type `α` -/
def square_class [inst : MyGroupClass α] (x : α) : α := inst.mul x x

def cubic_class [inst : MyGroupClass α] (x : α) : α := inst.mul x (inst.mul x x)

#eval square_class (2 : ℤ)
#eval cubic_class (3 : ℤ)

theorem square_class_one [MyGroupClass α] (x : α) : square_class x = x := by sorry

/- In Programming context, type classes are used to realize polymorphism -/
#check ToString

instance : ToString (Point ℕ) where
  toString p := s!"x is {p.x} and y is {p.y}"

instance [ToString α] : ToString (Point α) where
  toString p := s!"x is {p.x} and y is {p.y}"

instance : ToString (PositivePoint) where
  toString p := s!"x is {p.x} and y is {p.y}"

instance : ToString (MyGroup α) where
  toString _ := "This is a user-defined group"

/- Same function but triggered different realizations. This method allows you organize
structures efficiently in large programs. -/
#eval toString (Point.mk 1 2)
#eval toString (PositivePoint.mk 1 2 (by simp) (by simp))
#eval toString int_add_mygroup

/-
Now you have structures / type classes to construct new mathematic object. 
How can you organize them neatly?
Use sections and namespaces
-/


class ArithProg (a : ℕ → α) [AddCommGroup α] where
  equal_diff : ∀ n, a (n + 2) - a (n + 1) = a (n + 1) - a n

namespace ArithProg

variable {α : Type} [AddCommGroup α]
variable {a : ℕ → α} [inst : ArithProg a]

local notation "d" => a 1 - a 0

theorem comm_diff : ∀ n, a (n + 1) - a n = d := by
  intro n
  induction' n with k hk
  · simp
  rw [← hk]
  exact inst.equal_diff k

theorem formula : ∀ n, a n = a 0 + n • d := by
  intro n
  induction' n with k hk
  · simp
  rw [add_smul, ← add_assoc, ← hk, one_smul]
  rw [← comm_diff k]
  abel

local notation "S" n:max => ∑ i ∈ Finset.range n, a i

set_option diagnostics true

theorem sum_formula : ∀ n, S n = n • a 0 + (n * (n - 1) / 2) • d := by
  intro n
  induction' n with k hk
  · simp
  rw [Finset.sum_range_succ, hk]
  rw [formula (a := a) k]
  sorry  

end ArithProg

open ArithProg

def b (n : ℕ) : ℝ := n

instance : ArithProg b where
  equal_diff n := by simp [b]; norm_num

#check formula (a := b)
#check sum_formula (a := b)

