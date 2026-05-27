import Mathlib

/-!
# Lean x LLM pipeline: 看报错，理解模型在做什么

这份讲义给学 AI 的同学准备。
默认听众不需要会独立写很多 Lean，也不要求有很多数学背景；
重点是理解：

1. 为什么 Lean 适合和大模型做交互；
2. 为什么 Lean 的报错不是“单纯报错”，而是高质量反馈；
3. 如何从报错中判断：模型是思路错了，还是只差一个局部修补。

一个核心观点：

> 对 LLM 来说，Lean 的价值不只是 verifier，
> 更是一个会持续返回结构化反馈的 environment。

可以把流程想成：

`自然语言目标 -> LLM 生成 Lean -> Lean 返回错误/goal -> LLM 修补 -> 重复`

所以这一讲不追求“做很多题”，而是追求：

> 学会读 Lean 的失败类型。
-/

/-!
## 0. 先给一个错误分层的心智模型

从 AI 视角看，Lean 报错大概可以分成四层：

1. 语言表面错误
   - parser error
   - unknown identifier
   - invalid field notation

2. 局部步骤错误
   - `rw` 找不到 pattern
   - `apply` 不匹配
   - `exact` 给出的项类型不对

3. 全局思路错误
   - 反复 `type mismatch`
   - 定理方向不对
   - 目标 shape 和使用的 lemma 根本不匹配

4. 搜索/性能错误
   - `simp` 超时
   - `aesop` 超时
   - `isDefEq` 超时
   - heartbeats exhausted

重要的是：这四类错误不代表同一种失败。
对模型能力的判断也完全不同。
-/

section Warmup

#check 1 + 1 = 2
#check Nat.succ
#check List.map

example : 1 + 1 = 2 := by norm_num

/- 昨天已经讲过：绿色不等于真的证明了。 -/
theorem fake_proof : 1 = 2 := by
  sorry

#print axioms fake_proof

end Warmup

/-!
## 1. 项目级 / pipeline 级问题

这类问题常常不是“证明思路错”，而是 harness 没搭好。
对 agent 来说尤其重要，因为很多失败根本发生在“进入证明之前”。

常见现象：

1. `unknown module prefix`
   - `import` 路径不对
   - 文件不在项目里

2. 命令行能跑，编辑器不能跑
   - toolchain / cache / target 不一致

3. `lake build` 找不到目标
   - 文件名、模块名、目录结构不一致

4. LLM 只看到了一条 build log，但没分清是 parser、elaboration 还是 tactic error

这一类问题对 AI 来说说明：

> 模型可能还没开始“推理”，只是没有站在正确的环境里。
-/

-- 这些命令不在 Lean 里执行；写在讲义里做提醒。
-- `lake env lean Minicourse/ZJL_pipeline.lean`
-- `lake build Minicourse.ZJL_pipeline`
-- `lake exe mk_all`

/-!
## 2. 语言表面错误：模型先得把 Lean 说对

这一层更像“会不会说 Lean 这门语言”。
它还没有触及数学推理本身。
-/

section SurfaceErrors

/-!
### 2.1 unknown identifier

最常见来源：
1. 拼错名字；
2. 没有 `open` 对应 namespace；
3. 缺少 `import`；
4. 模型幻觉了一个并不存在的 lemma。

这类错误通常不说明数学思路错，只说明：
模型对 Lean / mathlib 的词表不稳。
-/

-- 取消注释看看：
-- #check Nat.succc
-- error: unknown constant 'Nat.succc'

#check Nat.succ

example : Nat.succ 3 = 4 := by rfl

/-!
### 2.2 parser error / 语法错误

这类错误一般也不代表数学思路错，而是输出格式坏了。
在 LLM 系统里，这通常意味着：

1. prompt 没约束好格式；
2. 模型把 tactic / term mode 混在一起；
3. 复制了自然语言说明进代码。
-/

-- 取消注释看看：
-- example : 1 = 1 := by
--   exact
--
-- 这里 `exact` 后面缺东西，Lean 会直接报语法/解析相关错误。

example : 1 = 1 := by
  exact rfl

/-!
### 2.3 invalid field notation

很多对象没有你以为的字段。
这类错误常见于模型把“概念上像成员”的东西写成 `.field`。
-/

structure MyPoint where
  x : Nat
  y : Nat

def p : MyPoint := ⟨1, 2⟩

#check p.x

-- 取消注释看看：
-- #check p.z
-- error: invalid field `z`, the environment does not contain `MyPoint.z`

end SurfaceErrors

/-!
## 3. elaboration / type checking 错误

这一层开始真正接近“模型理解对象了吗”。

比起 parser error，这些报错已经更有信息量：
Lean 成功读懂了句法，但无法把你的表达式拼成一个合法对象。
-/

section TypeErrors

/-!
### 3.1 最典型：type mismatch

这是最值得拿来分析模型能力的一类错误。

它有两种常见来源：

1. 局部写法问题
   - 把 `Nat` 当 `Int`
   - 漏了 coercion / type annotation
   - 用错了函数参数顺序

2. 更深层的思路问题
   - 目标本来需要一个 proof，模型却给了一个 data
   - 目标是 `a ≤ b`，模型却在构造 `a = b`
   - 想用的 lemma 根本不适用当前目标

所以 `type mismatch` 不能一概而论；
要看它到底发生在什么位置、反复出现没有。
-/

-- 取消注释看看：
-- example : 1 = 2 := by
--   exact rfl
--
-- 这里 `rfl` 的类型是 `?x = ?x`，和目标 `1 = 2` 不匹配。

-- 取消注释看看：
-- #check Nat.succ "hello"
-- `Nat.succ` 需要 `Nat`，但这里给了字符串。

example : 1 = 1 := by
  exact rfl

example : Nat.succ 3 = 4 := by
  rfl

/-!
### 3.2 application type mismatch / 参数顺序不对

这类错误在 LLM 输出里很常见：
模型记得 lemma 名字，但记错了它的参数顺序或隐式参数结构。
-/

def add1 : Nat → Nat := fun n ↦ n + 1

#check add1

-- 取消注释看看：
-- #check add1 3 4
-- 给了太多参数。

example : add1 4 = 5 := by
  rfl

/-!
### 3.3 failed to synthesize instance

这一类对 AI 同学很重要，因为它往往不是“定理错了”，而是：

> Lean 需要某种结构/实例，但当前上下文里没有。

比如要比较大小，可能需要 `LT α`；
要写 `+`，可能需要 `Add α`；
要用 `simp` 里某些数值规则，可能需要更强的 algebraic structure。

它反映的是：模型对 typeclass 依赖图是否敏感。
-/

class HasFoo (α : Type*) where
  foo : α → α

def useFoo {α : Type*} [HasFoo α] (a : α) : α := HasFoo.foo a

instance : HasFoo Nat where
  foo n := n + 10

example : useFoo 1 = 11 := by
  rfl

-- 取消注释看看：
-- #check useFoo true
-- error: failed to synthesize HasFoo Bool

/-!
### 3.4 coercion / 类型标注不足

在很多“看起来很像”的类型之间，Lean 不一定会自动猜到你想要哪个。
这类错误对 LLM 很容易产生，因为模型会把自然语言中的“1/3”
想成一个统一对象，但在 Lean 里它可能落在 `Nat`、`Int`、`Rat`、`Real` 的不同世界。
-/

#check 1 / 3
#eval 1 / 3
#check (1 : ℚ) / 3
#eval (1 : ℚ) / 3

example : (1 : ℚ) / 3 + 1 / 3 = 2 / 3 := by
  norm_num

end TypeErrors

/-!
## 4. tactic 级错误：模型大方向也许对，但这一步走不通

这类错误最适合说明：

> LLM 会“想到一个 tactic 名字”，
> 但不知道当前 goal 的 shape 是否真的允许这么做。
-/

section TacticErrors

variable (a b c : Nat)

/-!
### 4.1 `rw` 找不到 pattern

这是最经典的局部步骤错误之一。

通常不代表整个 theorem 错了，而是：
1. 你想 rewrite 的那个子式根本不在当前目标里；
2. 它在，但方向错了；
3. 它在更深的定义展开之后，要先 `unfold` / `simp` / `change`。

所以这类错误经常说明：

> 模型有“局部动作幻觉”，以为当前目标长成了某个样子。
-/

example : a + b = b + a := by
  rw [Nat.add_comm]

-- 取消注释看看：
-- example : a + b = b + a := by
--   rw [Nat.mul_comm]
-- 这里目标里根本没有乘法 pattern。

/-!
### 4.2 rewrite 方向错了

很多时候 lemma 是对的，错的是方向。
对 agent 来说，这比“完全不会”更像可修补错误。
-/

example (h : a = b) : b = a := by
  rw [h]

example (h : a = b) : a = b := by
  exact h

example (h : a = b) : b = a := by
  rw [← h]

/-!
### 4.3 `exact` 失败

`exact t` 的意思是：我声称 `t` 正好就是这个 goal 的证明。
如果失败，说明“这一步完全没对上”。

这有时是思路错，有时只是把某个中间 lemma 用早了。
-/

example (h : a = b) : a = b := by
  exact h

-- 取消注释看看：
-- example (h : a = b) : b = a := by
--   exact h
-- 需要的是 `Eq.symm h`，不是 `h` 本身。

example (h : a = b) : b = a := by
  exact h.symm

/-!
### 4.4 `apply` 失败

`apply` 的失败通常说明：
你给出的 lemma 结论 shape 和当前目标不匹配。

这一类也很适合拿来分析模型：
它可能记住了一个“常见套路”，但没检查前提和结论是否真的对齐。
-/

example (h₁ : a = b) (h₂ : b = c) : a = c := by
  apply Eq.trans
  · exact h₁
  · exact h₂

-- 取消注释看看：
-- example (h : a = b) : a = b := by
--   apply Nat.succ
-- `Nat.succ` 是个函数，不是能把等式目标拆开的 theorem。

/-!
### 4.5 `constructor` / `left` / `right` 用错对象

这类错误常见于模型只看到了“逻辑连接词”，
却没看清当前 goal 到底是 `∧`、`∨`、`∃` 还是等式。
-/

example (h₁ : a = b) (h₂ : b = c) : a = b ∧ b = c := by
  constructor
  · exact h₁
  · exact h₂

example (h : a = b) : a = b ∨ b = a := by
  left
  exact h

-- 取消注释看看：
-- example (h : a = b) : a = b := by
--   constructor
-- 等式目标不能直接 `constructor`。

end TacticErrors

/-!
## 5. automation 报错：不一定是不会，只是搜得不好

对 AI 同学，这一节特别重要。
因为它说明：

> “模型没证出来” 不一定代表它不懂，
> 也可能只是自动化策略太粗糙，搜索空间炸了。
-/

section AutomationErrors

/-!
### 5.1 `simp` 没有化掉目标

这通常不叫“报错”，但在交互里是很常见的失败：
你按了 `simp`，目标还在。

这往往说明：
1. 你缺少合适的 simp lemma；
2. 目标不是纯粹的化简问题；
3. 需要先把表达式改写到 `simp` 熟悉的形状。
-/

def double (n : Nat) : Nat := n + n

example (n : Nat) : double n = n + n := by
  simp [double]

-- 如果不展开定义，`simp` 未必知道 `double` 该怎么处理。

/-!
### 5.2 `simp` 方向不对：你以为它会“证明”，但它只会“化简”

很多 LLM 喜欢乱用 `simp`，因为它名字看起来像万能按钮。
但 `simp` 更像 rule-based simplifier，不是通用搜索器。
-/

example (n : Nat) : n + 0 = n := by
  simp

example (n : Nat) : n + 1 = Nat.succ n := by
  simp

example (n : Nat) : n + n = double n := by
  simp [double]

/-!
### 5.3 `aesop` / `simp` / `omega` 超时

超时类错误更接近“搜索策略坏了”，而不是“命题一定假”。

在 agent 系统里，这意味着可以考虑：
1. 先做 `have`，把大目标拆小；
2. 先 `rw` 或 `simp` 成更标准的形状；
3. 指定更少的 lemma；
4. 给 type annotation，减少 elaboration 压力；
5. 降低自动化，改成人工分步。

下面给一个非常温和的例子：即使目标是真的，
盲目依赖自动化也不是最好策略。
-/

example (m n : Nat) (h : m = n) : m + 1 = n + 1 := by
  simp [h]

example (m n : Nat) (h : m = n) : Nat.succ m = Nat.succ n := by
  aesop

/-!
### 5.4 `isDefEq` timeout / heartbeats exhausted

这一类最“工程化”，但和 LLM 很相关。

`isDefEq` 可以粗略理解成 Lean 在尝试判断：

> 两个看起来不完全一样的表达式，能不能通过展开定义、化简隐式参数、
> 插入 coercion、归约等方式，视为“本质相同”。

如果这一步超时，常见原因有：
1. 表达式太大；
2. coercion / instance search 太复杂；
3. 目标 shape 不清楚，Lean 在猜太多东西；
4. 模型给了“几乎对”的项，但 Lean 为了补完细节付出巨大代价。

这类错误往往不是“数学观念错”，而是：

> 输出过于含糊，给 elaborator 留了太多搜索空间。

实战中的缓解方式：
1. 加类型标注；
2. 先 `change` / `show` 明确目标形状；
3. 先写中间 `have`；
4. 少让 Lean 猜隐式参数；
5. 减少巨大的 `simp` / `rw` 链条。
-/

example : ((1 : ℚ) / 3) + 1 / 3 = 2 / 3 := by
  norm_num

example : ((1 : ℤ) : ℚ) = 1 := by
  norm_num

-- 课堂里可以现场演示一些“去掉类型标注后更容易混乱”的例子。

end AutomationErrors

/-!
## 6. 典型“修补动作”

当 Lean 给出反馈后，LLM 或人类通常会做下面几类修补。
这些动作本身就很适合作为 agent 的 action space。
-/

section RepairMoves

variable {α : Type*} (f g : α → α) (x : α)

/-!
### 6.1 `change`

把目标改写成一个定义上等价、但更好操作的形状。
-/

example : id x = x := by
  change x = x
  rfl

/-!
### 6.2 `show`

告诉 Lean：“我现在要把目标看成这个形状。”
这能减轻 elaboration 的猜测压力。
-/

example (h : x = x) : x = x := by
  show x = x
  exact h

/-!
### 6.3 `have`

先造一个中间结论，再用它解决主目标。
这通常能显著降低自动化和 unification 的压力。
-/

example (h : f x = g x) : f x = g x := by
  have hx : f x = g x := h
  exact hx

/-!
### 6.4 `simpa`

很多时候最后一步不是“重新证明”，而是“把已有结论整理成当前目标”。
-/

example (m n : Nat) (h : m = n) : m + 1 = n + 1 := by
  simp [h]

end RepairMoves

/-!
## 7. 从报错反推模型能力

如果我们把 Lean 当成 LLM 的 evaluator，那么不能只看：

> 最后过没过。

还应该看：

1. 它主要卡在哪一层？
   - 语言表面？
   - typeclass / elaboration？
   - tactic 局部动作？
   - 搜索性能？

2. 它会不会利用反馈？
   - 报 `unknown identifier` 后会不会改名字？
   - 报 `rw` 无 pattern 后会不会先 reshape goal？
   - 报 instance synthesis 失败后会不会补类型信息？

3. 它的失败是一次性的，还是重复性的？
   - 一次修好：更像局部 patch
   - 来回震荡：更像没有稳定的语义模型

所以对 AI 研究来说，Lean 的价值不只是“答案能验真”；
还在于：

> 它把失败模式暴露得很细。
-/

/-!
## 8. 一个可以带着学生记住的总结

1. parser/name error
   - 更像“不会说 Lean”

2. `rw` / `apply` / `exact` 失败
   - 更像“这一步没对上”

3. 反复 `type mismatch`
   - 可能是局部写法错，也可能是思路错

4. `simp` / `aesop` / `isDefEq` 超时
   - 更像“搜索或 elaboration 策略出了问题”

5. 能不能根据错误继续修
   - 这往往比“一次生成对答案”更能体现 agent 能力
-/

section TinyDemos

/- 这些例子都很短，适合课堂现场切换。 -/

example (a b : Nat) (h : a = b) : b = a := by
  exact h.symm

example (a b : Nat) : a + b = b + a := by
  rw [Nat.add_comm]

example (a : Nat) : double a = a + a := by
  simp [double]

example (a b c : Nat) (h₁ : a = b) (h₂ : b = c) : a = c := by
  exact Eq.trans h₁ h₂

example : ((1 : ℚ) / 3) + 1 / 3 = 2 / 3 := by
  norm_num

end TinyDemos
