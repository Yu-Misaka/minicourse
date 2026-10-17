import Mathlib

-- 同学们写agent以后更多遇到的是命令行交互

-- # 没有加入编译target

-- example : 1 = 2 := by rfl

-- `lake env lean Minicourse/1017_hack.lean`
-- `lake build Minicourse.1017_hack`
-- `lake exe mk_all`

-- # lake build的消息等级

#check 1
example : 1 = 2 := by sorry
-- example : 1 = 2 := rfl

-- # sorry的不同写法/出现

lemma sorry1 : 1 = 2 := by sorry
lemma sorry2 : 1 = 2 := by admit
lemma sorry3 : 1 = 2 := by
  stop
  rfl
lemma sorry4 : 1 = 2 := sorryAx _ true

set_option warn.sorry false in
lemma sorry5 : 1 = 2 := sorry

#print axioms sorry5


lemma sorry6 : 1 = 2 := by
  apply?

-- # print axioms

#check propext
#check Classical.choice
#check Quot.sound

#print axioms sorry5

set_option pp.all true

#check sorry5
