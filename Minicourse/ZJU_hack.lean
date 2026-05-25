import Mathlib

-- 同学们写agent以后更多遇到的是命令行交互

-- # 没有加入编译target

-- example : 1 = 2 := by rfl

-- `lake env lean Minicourse/ZJU_hack.lean`
-- `lake build Minicourse.ZJU_hack`
-- ``

-- # lake build的消息等级

#check 1
example : 1 = 2 := by sorry
-- example : 1 = 2 := rfl
