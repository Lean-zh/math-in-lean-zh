import MIL.Common
import Mathlib.Data.Real.Basic
/- TEXT:
计算
-----------

通常我们学习数学计算时并不将其视为证明。
但是，当我们像 Lean 要求的那样验证计算中的每一步时，最终的结果就是一个证明，我们在证明了算式的左侧等于右侧。

.. index:: rewrite, rw, tactics ; rw and rewrite

在 Lean 中，陈述一个定理等同于设立证明该定理的目标。Lean 提供了重写（rewrite）策略 ``rw``，它会使用一个等式，``rw`` 在 **目标** 中找到符合等式左侧的部分，然后将这部分替换为等式右侧。例如：
如果 ``a``、 ``b`` 和 ``c`` 是实数，那么 ``mul_assoc a b c`` 是等式 ``a * b * c = a * (b * c)``,
而 ``mul_comm a b`` 是等式 ``a * b = b * a``。 你想运用这些等式时可以只引用它们的名字。
在 Lean 中，乘法左结合，因此 ``mul_assoc`` 的左侧也可以写成 ``(a * b) * c``，但是没必要写括号就最好不写。

让我们尝试一下 ``rw``。

.. index:: real numbers
TEXT. -/
-- An example.
-- QUOTE:
example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc b a c]
-- QUOTE.

/- TEXT:
教材源码里的 ``import`` 行从 Mathlib 中导入了实数理论，以及有用的自动化功能。为简洁计正文中省略，如果你想自己试着运行例子，你可以查询源码来了解。

``ℝ`` 字符通过 ``\R`` 或 ``\real`` 输入，然后按下空格或 Tab 键。
当阅读 Lean 文件时，如果你将光标悬停在一个符号上，VS Code 将显示用于输入该符号的语法。
如果你想查看所有可用的缩写，可以按下 Ctrl-Shift-P，然后输入 abbreviations 来访问 ``Lean 4: Show all abbreviations`` 命令。
如果您的键盘上没有方便使用的反斜杠，可以通过更改 ``lean4.input.leader`` 设置来改变前导字符。

.. index:: proof state, local context, goal

当光标位于策略证明的中间时，Lean 会在 *Lean Infoview* 窗口中报告当前的 **证明状态** 。
当你将光标移到证明的每一步时，你可以看到状态的变化。Lean 中的典型证明状态可能如下所示：
.. code-block::

    1 goal
    x y : ℕ,
    h₁ : Prime x,
    h₂ : ¬Even x,
    h₃ : y > x
    ⊢ y ≥ 4

``⊢`` 前面的部分是当前位置处我们所拥有的对象和假设，称为 **语境（context）** 。
在这个例子中，语境包括两个对象，自然数 ``x`` 和 ``y``；包括三个假设，分别具有标识符 ``h₁`` 、 ``h₂`` 和 ``h₃`` （下标用 ``\1``、``\2`` …… 键入）。
Lean 的语法要求在语境中每个假设都拥有一个名字，叫什么都可以，比如不下标的 ``h1`` 也可以（实际上这是类型论的要求，例如本例中 ``h₁`` 这个"名字"其实标记着类型为命题 ``Prime x`` 的项。），或者 ``foo``、 ``bar`` 和 ``baz``。
最后一行用 ``⊢`` 标记的代表 **目标（goal）** ，即要证明的事实。对于目标这个词，一些人有时人们使用 **目的（target）** 表示要证明的事实，使用 **目标（goal）** 表示语境和目的（target）的组合，不过在特定上下文中不致混淆。

接下来做一些练习！用 ``rw`` 策略替换掉下面的 ``sorry`` 。
为此再告诉你一个新技巧：你可以用左箭头 ``←`` （ ``\l`` ）来调转一个等式的方向，从而让 ``rw`` 从另一边做替换操作。例如，``rw ← mul_assoc a b c`` 会把目标里的 ``a * (b * c)`` 替换成 ``a * b * c`` 。注意这里指的是 ``mul_assoc`` 等式的从右到左，它与目标的左边或右边无关。
TEXT. -/
-- Try these.
-- QUOTE:
example (a b c : ℝ) : c * b * a = b * (a * c) := by
  sorry

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (a b c : ℝ) : c * b * a = b * (a * c) := by
  rw [mul_comm c b]
  rw [mul_assoc b c a]
  rw [mul_comm c a]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc a b c]
  rw [mul_comm a b]
  rw [mul_assoc b a c]

/- TEXT:
你也可以不带参数使用诸如 ``mul_assoc`` 或者 ``mul_comm`` 这些等式。这些情况下重写策略会识别它在目标中匹配到的第一个模式。
TEXT. -/
-- An example.
-- QUOTE:
example (a b c : ℝ) : a * b * c = b * c * a := by
  rw [mul_assoc]
  rw [mul_comm]
-- QUOTE.

/- TEXT:
你还可以只提供一部分参数，例如 ``mul_comm a`` 识别所有形如 ``a * ?`` 的模式然后重写为 ``? * a`` 。下面的练习中你可以试试在第一个里面不给参数，第二个里面只给一个参数。
TEXT. -/
/- Try doing the first of these without providing any arguments at all,
   and the second with only one argument. -/
-- QUOTE:
example (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  sorry

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  rw [mul_comm]
  rw [mul_assoc]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc]
  rw [mul_comm a]
  rw [mul_assoc]

/- TEXT:
你也可以 ``rw`` 局部语境里的条件：
TEXT. -/
-- Using facts from the local context.
-- QUOTE:
example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h']
  rw [← mul_assoc]
  rw [h]
  rw [mul_assoc]
-- QUOTE.

/- TEXT:
试试看：
（第二个练习里面你可以使用定理 ``sub_self``，``sub_self a`` 代表等式 ``a - a = 0``。）
TEXT. -/
-- QUOTE:
example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  sorry

example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  rw [mul_assoc a]
  rw [h]
  rw [← mul_assoc]

example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  rw [hyp]
  rw [hyp']
  rw [mul_comm]
  rw [sub_self]

/- TEXT:
现在我们介绍 Lean 的一些有用的特性. 首先，通过在方括号内列出相关等式，可以用一行重写执行多个命令。
TEXT. -/
-- QUOTE:
example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h', ← mul_assoc, h, mul_assoc]
-- QUOTE.

/- TEXT:
将光标放在 rewrite 列表中的任意逗号后，仍然可以看到进度。

另一个技巧是我们可以在例子或定理之外一次性地声明变量. 当 Lean 在定理的陈述中看到它们时，它会自动将它们包含进来。
TEXT. -/
section

-- QUOTE:
variable (a b c d e f : ℝ)

example (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h', ← mul_assoc, h, mul_assoc]
-- QUOTE.

end

/- TEXT:
检查上述证明开头的策略状态，可以发现 Lean 确实包含了相关变量，而忽略了声明中没有出现的 g。我们可以把声明的范围放在一个 ``section ... end`` 块中做成类似其他编程语言中局部变量的效果. 最后，回顾一下第一章，Lean为我们提供了一个命令来确定表达式的类型：
TEXT. -/
-- QUOTE:
section
variable (a b c : ℝ)

#check a
#check a + b
#check (a : ℝ)
#check mul_comm a b
#check (mul_comm a b : a * b = b * a)
#check mul_assoc c a b
#check mul_comm a
#check mul_comm

end
-- QUOTE.

/- TEXT:
``#check`` 命令对对象和命题都有效。在响应命令 ``#check a`` 时，Lean 报告 ``a`` 的类型为 ``ℝ``。作为对命令 ``#check mul_comm a b`` 的响应，Lean报告 ``mul_comm a b`` 是事实 ``a * b = b * a`` 的证明。命令 ``#check (a : ℝ)`` 表明我们期望 ``a`` 的类型是 ``ℝ``，如果不是这样，Lean 将引发一个错误。稍后我们将解释最后三个 ``#check`` 命令的输出，你可以尝试自己写一些 ``#check`` 命令。

我们再举几个例子。定理 ``two_mul a`` 表示 ``2 * a = a + a``。定理 ``add_mul`` 和 ``mul_add`` 表示乘法对加法的分配律，定理 ``add_assoc`` 表示加法的结合律。使用 ``#check`` 命令查看精确的语句。

.. index:: calc, tactics ; calc

TEXT. -/
section
variable (a b : ℝ)

-- QUOTE:
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  rw [mul_add, add_mul, add_mul]
  rw [← add_assoc, add_assoc (a * a)]
  rw [mul_comm b a, ← two_mul]
-- QUOTE.

/- TEXT:
虽然可以通过在编辑器中逐步检查来弄清楚这个证明中发生了什么，但很难单独阅读。Lean 使用 ``calc`` 关键字提供了一种更结构化的方法来编写类似这样的证明。
TEXT. -/
-- QUOTE:
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      rw [mul_add, add_mul, add_mul]
    _ = a * a + (b * a + a * b) + b * b := by
      rw [← add_assoc, add_assoc (a * a)]
    _ = a * a + 2 * (a * b) + b * b := by
      rw [mul_comm b a, ← two_mul]
-- QUOTE.

/- TEXT:
请注意，证明 **不** 以 ``by`` 开头：以 ``calc`` 开头的表达式是一个证明项。
``calc`` 表达式也可以在策略证明块中使用，Lean将其解释为使用证明项的结果来解决当前目标的指令。``calc`` 语法必须严格仿照上例格式使用下划线和对齐。Lean 使用缩进来确定策略块或 ``calc`` 块开始和结束的地方。试着改变上面证明中的缩进，看看会发生什么。

编写 ``calc`` 证明的一种方法是首先使用 ``sorry`` 策略填空，确保 Lean 认可中间步骤表达式，然后使用策略对各个步骤进行论证。
TEXT. -/
-- QUOTE:
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      sorry
    _ = a * a + (b * a + a * b) + b * b := by
      sorry
    _ = a * a + 2 * (a * b) + b * b := by
      sorry
-- QUOTE.

end

/- TEXT:
试试用两种方法证明以下等式：只用 ``rw`` 和用更结构化的 ``calc`` 。
TEXT. -/
-- Try these. For the second, use the theorems listed underneath.
section
variable (a b c d : ℝ)

-- QUOTE:
example : (a + b) * (c + d) = a * c + a * d + b * c + b * d := by
  sorry
-- QUOTE.

/- TEXT:
接下来的练习有点挑战性。你可以用下列的定理。
TEXT. -/
-- QUOTE:
example (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  sorry

#check pow_two a
#check mul_sub a b c
#check add_mul a b c
#check add_sub a b c
#check sub_sub a b c
#check add_zero a
-- QUOTE.

end

/- TEXT:
.. index:: rw, tactics ; rw and rewrite
我们还可以在语句集中的假设中执行重写。例如，``rw [mul_comm a b] at hyp`` 将假设 ``hyp`` 中的 ``a * b`` 替换为 ``b * a`` 。
TEXT. -/
-- Examples.

section
variable (a b c d : ℝ)

-- QUOTE:
example (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp'] at hyp
  rw [mul_comm d a] at hyp
  rw [← two_mul (a * d)] at hyp
  rw [← mul_assoc 2 a d] at hyp
  exact hyp
-- QUOTE.

/- TEXT:
.. index:: exact, tactics ; exact

最后一步中 ``exact`` 策略使用 ``hyp`` 来解决目标的原理是，到此 ``hyp`` 不就是目标本身了吗！（Exactly!）

.. index:: ring (tactic), tactics ; ring

最后我们介绍一个 Mathlib 提供的强力自动化工具 ``ring`` 策略，它专门用来解决交换环中的等式，只要这些等式是完全由环公理导出的而不涉及别的假设。
TEXT. -/
-- QUOTE:
example : c * b * a = b * (a * c) := by
  ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring
-- QUOTE.

end

/- TEXT:
``ring`` 策略通过 ``import Mathlib.Data.Real.Basic`` 导入，但下一节会看到它不止可以用在实数的计算上。它还可以通过 ``import Mathlib.Tactic`` 导入。对于其他常见的代数结构也有类似的策略。

``rw`` 有一种叫做 ``nth_rewrite`` 的变体，如果目标中存在多处匹配，``nth_rw`` 允许你指出想要实施替换的位置。匹配项从 1 开始计数，在下面的例子中 ``nth_rewrite 2 [h]`` 用 ``c`` 替换了第二个 ``a + b``。
EXAMPLES: -/
-- QUOTE:
example (a b c : ℕ) (h : a + b = c) : (a + b) * (a + b) = a * c + b * c := by
  nth_rw 2 [h]
  rw [add_mul]
-- QUOTE.
