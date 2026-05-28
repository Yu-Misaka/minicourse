import Mathlib

-- example : 1 = 2 := rfl

/-!
# Lean 报错作为 LLM 的反馈信号

这一讲面向学 AI 的同学。目标不是训练大家手写复杂 Lean 证明，而是理解：

* 大模型写 Lean 时，Lean 的反馈在说什么；
* 哪些报错只是“表达方式没有对齐”，哪些报错说明“思路可能错了”；
* 为什么 Lean 可以作为 LLM 的 verifier，也可以作为交互式 repair loop 的环境。

昨天我们已经看过：

* `#check` / `#eval`
* 类型、隐式参数、类型类实例
* `sorry`、`admit`、编译 target 和命令行输出

今天的关键词是：

```text
自然语言目标
  ↓
LLM 生成 Lean 代码
  ↓
Lean elaborator / typechecker / tactics 检查
  ↓
报错、goal state、trace、warning
  ↓
LLM 或人类修补
```

Lean 在这里不只是“判卷器”，更像是一个高精度反馈环境。
-/

/-!
## 0. 读报错之前：先看 goal

对 LLM 来说，当前 goal 就像游戏环境的 observation。

如果模型不知道现在的 goal 是什么，它很容易生成看起来合理但完全打不中的 tactic。
-/

example (a b c : ℕ) (h : a + b = c) : b + a = c := by
  -- 光看自然语言：“加法交换一下，再用 h”。
  -- Lean 的关键是：当前 goal 的精确形状是什么？
  rw [Nat.add_comm b a]
  exact h

/-!
课堂上可以让同学先猜：

```lean
example (a b c : ℕ) (h : a + b = c) : b + a = c := by
  exact h
```

为什么不行？

答案不是数学上错了，而是 Lean 现在看到的是：

```text
h : a + b = c
⊢ b + a = c
```

这两个表达式不是同一个表达式。人觉得“显然一样”，Lean 需要你给出
`Nat.add_comm b a` 这一步。
-/

/-!
## 1. 环境类错误：不是数学问题

LLM agent 常常先死在工程层面，而不是证明层面。

常见情况：

* `import` 找不到；
* 文件没有加入 build target；
* Lean / mathlib 版本不匹配；
* 没有拿到 `.lake` 缓存；
* 命令在错误目录运行。

这类错误通常不能说明模型不会证明，只说明环境没有准备好。

昨天的 `ZJL_intro.lean` 和 `ZJL_hack.lean` 已经讲过：

```bash
lake exe cache get
lake build
lake env lean Minicourse/ZJL_errors.lean
```
-/

#check Nat.add_comm
#check List.length_append

/-!
## 2. Unknown identifier：模型“幻觉了名字”

LLM 很容易知道“应该有一个定理叫加零”，但不知道 mathlib 里的精确名字。

把下面的代码取消注释，可以看到 unknown identifier：

```lean
example (n : ℕ) : n + 0 = n := by
  exact Nat.add_zero_right n
```

`Nat.add_zero_right` 这个名字听起来很合理，但 mathlib 里不是这个名字。

正确写法：
-/

example (n : ℕ) : n + 0 = n := by
  exact Nat.add_zero n

example (n : ℕ) : n + 0 = n := by
  simp

/-!
AI 视角：

```text
unknown identifier
```

很多时候是“检索/命名错误”，不一定是数学思路错。

修补方式：

* 用 `#check` 检查名字；
* 用 search 工具找 lemma；
* 让模型不要硬猜名字，而是读当前环境。
-/

#check Nat.add_zero
#check zero_add
#check add_comm

/-!
## 3. Type mismatch：数学上像，Lean 看起来不像

`type mismatch` 是最值得讲的一类错误。

Lean 不是只看“意思差不多”，它会检查表达式的精确类型。

取消注释：

```lean
example : (1 : ℤ) = (1 : ℕ) := by
  rfl
```

这里左边是整数 `ℤ`，右边是自然数 `ℕ`。人知道它们都表示 1，
但 Lean 看到的是两个不同类型里的对象。

可以修成同一个类型：
-/

example : (1 : ℤ) = (1 : ℤ) := by
  rfl

example : ((1 : ℕ) : ℤ) = (1 : ℤ) := by
  norm_num

example : ((1 : ℤ) : ℚ) = (1 : ℚ) := by
  norm_num

/-!
再看一个更像 LLM 会写错的例子。

取消注释：

```lean
example (n : ℕ) : (n : ℤ) + 1 = n + 1 := by
  rfl
```

右边的 `n + 1` 乍看像自然数加法，但因为等号左边在 `ℤ` 里，
Lean 会尝试理解所有项的类型。这里很容易出现 coercion 没写清楚的问题。

更稳的写法是把类型标清楚：
-/

example (n : ℕ) : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by
  norm_num

/-!
AI 视角：

```text
type mismatch
```

常见含义：

* 少了类型标注；
* coercion 没对齐；
* 隐式参数被 Lean 猜成了另一个东西；
* 模型用了“数学上相同”但“定义上不同”的表达。

这类错误经常是“小修”，不是思路错。
-/

/-!
## 4. Failed to synthesize instance：缺少结构

Lean 的很多符号不是对所有类型都有意义。

例如 `a * b` 需要知道这个类型上有乘法。

取消注释：

```lean
def badMul {G : Type} (a b : G) := a * b
```

Lean 会说它无法合成类似 `[Mul G]` 的实例。

正确写法：
-/

def goodMul {G : Type} [Mul G] (a b : G) := a * b

#check goodMul

variable {G : Type} [Group G]

example (a b : G) : goodMul a b = a * b := by
  rfl

/-!
这个报错和昨天讲的类型类实例有关。

AI 视角：

```text
failed to synthesize
```

通常表示：

* 不是证明目标错；
* 而是上下文里缺少某种“结构假设”；
* LLM 可能忘了写 `[Group G]`、`[Ring R]`、`[TopologicalSpace X]` 等。

这类错误对 agent 很重要，因为它告诉模型：

```text
你现在使用了一个需要前提的操作，但你没有提供前提。
```
-/

/-!
## 5. `rw` 没找到 pattern：tactic 知道方向，但没打中目标

`rw [h]` 不是“用 h 做点什么”，而是在当前目标里寻找和 h 左边匹配的 pattern。
-/

example (a b c : ℕ) (h : a + b = c) : a + b + 1 = c + 1 := by
  rw [h]

/-!
取消注释：

```lean
example (a b c : ℕ) (h : a + b = c) : b + a + 1 = c + 1 := by
  rw [h]
```

为什么不行？

当前目标里出现的是 `b + a`，而 `h` 的左边是 `a + b`。
人知道二者相等，但 `rw` 不会自动先用交换律。

修法：
-/

example (a b c : ℕ) (h : a + b = c) : b + a + 1 = c + 1 := by
  rw [Nat.add_comm b a]
  rw [h]

example (a b c : ℕ) (h : a + b = c) : b + a + 1 = c + 1 := by
  rw [Nat.add_comm b a, h]

/-!
再看 rewrite 方向。
-/

example (a b c : ℕ) (h : c = a + b) : b + a + 1 = c + 1 := by
  rw [Nat.add_comm b a]
  rw [← h]

/-!
AI 视角：

```text
rw tactic failed, did not find instance of the pattern
```

常见含义：

* lemma 是对的，但目标形状没对上；
* 方向错了，需要 `← h`；
* 需要先 `simp`、`ring`、`rw [add_comm]` 改变目标形状；
* 模型对当前 goal 的 observation 不够精确。
-/

/-!
## 6. `simp`：好用，但不是魔法

`simp` 做的是按 simp lemma 化简。它很强，但不是“自动证明一切”。
-/

example (xs : List ℕ) : (xs ++ []).length = xs.length := by
  simp

example (xs ys : List ℕ) : (xs ++ ys).length = xs.length + ys.length := by
  simp

example (a b c : ℕ) (h : a = b) : a + c = b + c := by
  simp [h]

/-!
取消注释：

```lean
example (a b c : ℕ) (h : a + b = c) : b + a = c := by
  simp [h]
```

这里 `simp [h]` 不一定能自动想到要用加法交换律把 `b + a` 变成 `a + b`。
更明确的写法：
-/

example (a b c : ℕ) (h : a + b = c) : b + a = c := by
  rw [Nat.add_comm b a]
  exact h

/-!
AI 视角：

```text
simp made no progress
simp failed
simp timeout
```

大概可以这样判断：

* `simp` 没进展：目标不是化简型，可能需要 rewrite、引入 lemma 或变换结构；
* `simp [h]` 失败：h 的方向或目标形状可能不适合；
* `simp only [...]` 更可控，适合 agent 缩小搜索空间；
* `simp [everything]` 看起来聪明，但很容易把搜索空间炸开。
-/

/-!
## 7. 超时：搜索空间爆了，不一定是定理假

Lean 里常见的超时来源：

* `simp` 使用了太大的 simp 集；
* `aesop` / `grind` / `omega` 等自动化搜索太大；
* typeclass search 找实例太深；
* definitional equality，也就是 `isDefEq`，展开定义时太复杂；
* LLM 把大量无关 lemma 塞进 tactic。

这段不要真的运行，只作为课堂材料：

```lean
set_option maxHeartbeats 1000 in
example (a b c d e f : ℕ)
    (h₁ : a = b) (h₂ : b = c) (h₃ : c = d)
    (h₄ : d = e) (h₅ : e = f) : a = f := by
  aesop
```

有时自动化能解，有时会因为搜索预算太低而失败。

更稳定的 proof 通常更像这样：
-/

example (a b c d e f : ℕ)
    (h₁ : a = b) (h₂ : b = c) (h₃ : c = d)
    (h₄ : d = e) (h₅ : e = f) : a = f := by
  calc
    a = b := h₁
    _ = c := h₂
    _ = d := h₃
    _ = e := h₄
    _ = f := h₅

/-!
AI 视角：

```text
timeout
maximum recursion depth has been reached
maximum heartbeats exceeded
```

这不等于数学命题是假的。

它通常表示：

* 搜索策略太粗暴；
* 缺少中间 lemma；
* 需要把大目标拆小；
* 需要限制自动化使用的 lemma；
* 需要从“让 Lean 搜”改成“告诉 Lean 路线”。
-/

/-!
## 8. `sorry`：最危险的是“看起来成功”

昨天已经讲过 `sorry`、`admit` 和 `sorryAx`。

对 LLM verifier 来说，最危险的不是报错，而是代码“编译了”，但没有真的证明。
-/

theorem realProof : 1 + 1 = 2 := by
  norm_num

/-!
取消注释：

```lean
theorem fakeProof : 1 = 2 := by
  sorry
```

Lean 会给 warning，但如果系统只看 exit code，或者关掉 warning，就可能误判。

例如：

```lean
set_option warn.sorry false in
theorem fakeProofSilent : 1 = 2 := by
  sorry
```

所以 agent 不能只问“能不能 build”，还要问：

* 有没有 `sorry` / `admit` / `sorryAx`？
* `#print axioms theoremName` 里有没有非预期公理？
* 是否只使用了允许的公理，比如 `propext`、`Classical.choice`、`Quot.sound`？
-/

#print axioms realProof

/-!
## 9. 小修还是思路错？

可以给学生一个简单判断表。

比较像“小修”的错误：

```text
unknown identifier
type mismatch 但只差类型标注/coercion
rw 没找到 pattern，但目标明显接近
failed to synthesize instance，但明显缺一个结构假设
simp 没进展，但可以先改写目标
```

比较像“思路可能错了”的错误：

```text
模型反复使用不存在的 theorem
把 lemma 的方向用反了，而且修正后目标仍然不接近
目标根本不能由已有假设推出
自动化反复超时，没有任何中间目标变小
证明依赖 sorry/admit/sorryAx
```

更 AI 一点的说法：

```text
Lean error is not just failure.
It is structured feedback about where the model's internal plan diverges
from the formal environment.
```
-/

/-!
## 10. 一个课堂练习：让学生当 verifier

下面这些例子都放在注释里。课堂上可以逐个取消注释，让学生判断：

1. 这是什么类型的错误？
2. 这说明 LLM 哪里没对齐？
3. 应该给模型什么反馈？
4. 这是小修，还是思路错？

```lean
-- A. unknown identifier
example (n : ℕ) : n + 0 = n := by
  exact Nat.add_zero_right n

-- B. type mismatch
example : (1 : ℤ) = (1 : ℕ) := by
  rfl

-- C. failed to synthesize instance
def badMul {G : Type} (a b : G) := a * b

-- D. rw 没找到 pattern
example (a b c : ℕ) (h : a + b = c) : b + a = c := by
  rw [h]

-- E. 方向错
example (a b c : ℕ) (h : c = a + b) : a + b = c := by
  rw [h]

-- F. 看起来证明了，其实用了 sorry
theorem fake : 1 = 2 := by
  sorry
```

参考修法：
-/

example (n : ℕ) : n + 0 = n := by
  exact Nat.add_zero n

example : ((1 : ℕ) : ℤ) = 1 := by
  norm_num

def fixedMul {G : Type} [Mul G] (a b : G) := a * b

example (a b c : ℕ) (h : a + b = c) : b + a = c := by
  rw [Nat.add_comm b a]
  exact h

example (a b c : ℕ) (h : c = a + b) : a + b = c := by
  exact h.symm

theorem fixed : 1 + 1 = 2 := by
  norm_num

/-!
## 11. 收束：Lean 在 AI 里的角色

最后可以把 Lean + LLM 的应用分成三种：

1. **Verifier**

   LLM 生成证明，Lean 检查真假。

2. **Interactive repair loop**

   LLM 读 Lean 的报错、goal state、trace，然后修补代码。

3. **Search / planning assistant**

   LLM 不一定直接完成证明，而是帮助找 lemma、拆目标、提出下一步。

这节课的核心 takeaway：

```text
Lean 对 AI 的价值，不只是“证明数学题”。
它提供了一种机器可读、可验证、可迭代的严格反馈。
```
-/
