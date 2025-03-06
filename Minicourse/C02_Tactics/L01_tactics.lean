import Mathlib

/- 
# Introduction
In this lecture, we first dive into some more advanced tactics. Then explain about general 
organiztion of Lean project.
-/

/- simp -/

/- linarith -/
example (x : ℝ) (x_pos : x > 0) : 2 * x + 1 > x + 1 := by
  linarith

/- norm_num -/

/- tauto -/
example (x : ℝ) (x_pos : x > 0) : (x > 0 ∧ x ≠ 0) ∨ x = 0 := by tauto

/- omega -/
example (n : ℕ) : 2 * n = n * 2 := by omega

example (n : ℕ) : n * 2 / 2 = n := by omega

/- aesop -/

/- Structures and typeclasses -/
structure Point (α : Type u) where
  x : α
  y : α

def my_point_two_two : Point ℝ := {x := 2, y := 2}

theorem my_point_two_two_eq_two : my_point_two_two.x = 2 := by rfl

/- Positive points -/
structure PositivePoint where
  x : ℝ
  y : ℝ
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


