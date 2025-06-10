import MIL.Common

open Nat

-- SOLUTIONS:
-- There are no exercises in this section.
/- TEXT:
概述
--------

简言之，Lean 是用于构建复杂表达式的工具，它基于一种称为 **依值类型论（Dependent type theory）** 的形式语言。

.. index:: check, commands ; check

每个表达式都有一个 **类型（Type）**，你可以使用 `#check` 命令来打印它。一些数学对象表达式的类型可能是像 `ℕ` 或 `ℕ → ℕ` 这样的。
TEXT. -/
-- These are pieces of data.
-- QUOTE:
#check 2 + 2

def f (x : ℕ) :=
  x + 3

#check f
-- QUOTE.

/- TEXT:
数学命题的类型是 `Prop`。
TEXT. -/
-- These are propositions, of type `Prop`.
-- QUOTE:
#check 2 + 2 = 4

def FermatLastTheorem :=
  ∀ x y z n : ℕ, n > 2 ∧ x * y * z ≠ 0 → x ^ n + y ^ n ≠ z ^ n

#check FermatLastTheorem
-- QUOTE.

/- TEXT:
设命题 `P` 类型为 `Prop`，你可以构造类型为 `P` 的表达式，它们是命题 `P` 的证明。
TEXT. -/
-- These are proofs of propositions.
-- QUOTE:
theorem easy : 2 + 2 = 4 :=
  rfl

#check easy

theorem hard : FermatLastTheorem :=
  sorry

#check hard
-- QUOTE.

/- TEXT:
如果你设法构建了一个类型为 ``FermatLastTheorem`` 的表达式，并且 Lean 接受它作为该类型的项，那么你已经干了一件伟大的事。
（使用 ``sorry`` 是作弊，Lean 知道这一点。）所以现在你知道了游戏目标。剩下要学习的只有规则了。

- Kevin Buzzard 正在领导这件伟大的事，详见：`The Fermat's Last Theorem Project <https://leanprover-community.github.io/blog/posts/FLT-announcement/>`_

本书配套教程 `Theorem Proving in Lean <https://leanprover.github.io/theorem_proving_in_lean4/>`_，中文版 `Lean 中的定理证明 <https://www.leanprover.cn/tp-lean-zh/>`_，提供了对Lean的基础逻辑框架和核心语法更全面的介绍。 Lean 中的定理证明适用于那些在使用新洗碗机之前更喜欢从头到尾阅读用户手册的人。
如果你是那种更喜欢先动手尝试，以后再弄清细节的人，那么从本书开始更合适，需要时随时可以回去参考 Lean 中的定理证明。

Lean 形式化数学与 Lean 中的定理证明的另一个区别在于，本书更加强调 **证明策略(Tactics)** 的使用。
考虑到我们试图构建复杂表达式，Lean 提供了两种方法：直接构造表达式本身，或者向 Lean 提供 *指令*，告诉它如何构建这些表达式。
例如，下面构造的证明表达式在说明，如果 ``n`` 是偶数，则 ``m * n`` 也是偶数：
TEXT. -/
-- Here are some proofs.
-- QUOTE:
example : ∀ m n : Nat, Even n → Even (m * n) := fun m n ⟨k, (hk : n = k + k)⟩ ↦
  have hmn : m * n = m * k + m * k := by rw [hk, mul_add]
  show ∃ l, m * n = l + l from ⟨_, hmn⟩
-- QUOTE.

/- TEXT:
这个 **证明项** 可以压缩成一行：
TEXT. -/
-- QUOTE:
example : ∀ m n : Nat, Even n → Even (m * n) :=
fun m n ⟨k, hk⟩ ↦ ⟨m * k, by rw [hk, mul_add]⟩
-- QUOTE.

/- TEXT:
以下是同一定理的策略式证明，其中以 ``--`` 开头的行是注释，因此被 Lean 忽略：
TEXT. -/
-- QUOTE:
example : ∀ m n : Nat, Even n → Even (m * n) := by
  -- 设 `m` 和 `n` 是自然数，设 `n = 2 * k`
  rintro m n ⟨k, hk⟩
  -- 需证 `m * n` 是某自然数的两倍。那就设它是 `m * k` 的两倍吧
  use m * k
  -- 代入 `n`
  rw [hk]
  -- 剩下的就很显然了
  ring
-- QUOTE.

/- TEXT:
当你在 VS Code 中输入上述证明的每一行时，Lean 会在一个单独的窗口中显示 **证明状态**，告诉你已经建立了哪些事实，以及要证明你的定理还需要完成什么任务。
你可以通过逐行逐步骤回顾证明，因为 Lean 将继续显示光标所在点的证明状态。
本例中，证明的第一行引入了 ``m`` 和 ``n`` （此时可以重命名它们，如果我们想的话），并且将假设 ``Even n`` 分解为 ``k`` 和假设 ``n = 2 * k``.
第二行， ``use m * k``, 声明我们将通过证明 ``m * n = 2 * (m * k)`` 来证明 ``m * n`` 是偶数。
下一行使用了 ``rw`` 策略（rewrite的缩写）在目标中将 ``n`` 替换为 ``2 * k``，得到的新目标 ``m * (2 * k) = 2 * (m * k)`` 最终被 ``ring`` 策略解决。

逐步构建证明并获得增量反馈的能力非常强大。因此，策略证明通常比编写证明项更容易也更快。两者之间没有明显的区别：策略证明可以插入到证明项中，
就像我们在上面的例子中使用短语 ``by rw [hk, mul_left_comm]`` 一样。我们还将看到，反之，将一个简短的证明项插入到策略证明中通常也很有用。
虽然如此，但在这本书中，我们会把重点放在策略的使用上。

在我们的例子中，策略证明也可以简化为一行：
TEXT. -/
-- QUOTE:
example : ∀ m n : Nat, Even n → Even (m * n) := by
  rintro m n ⟨k, hk⟩; use m * k; rw [hk]; ring
-- QUOTE.

/- TEXT:
在这里，我们使用策略来执行每个细节证明步骤。但是 Lean 提供实质性的自动化，并且可以证明更长的计算和更大的推理步骤。
例如，我们可以使用特定的规则调用 Lean 的化简器，用于化简关于奇偶性的语句，以自动证明我们的定理。
TEXT. -/
-- QUOTE:
example : ∀ m n : Nat, Even n → Even (m * n) := by
  intros; simp [*, parity_simps]
-- QUOTE.

/- TEXT:
两本入门教程之间的另一个重大区别是，Lean 中的定理证明仅依赖于 Lean 内核以及其内置的策略，而 Lean 形式化数学建立在 Lean 强大且不断增长的库 *Mathlib* 的基础上。
因此，我们会向您展示如何使用库中的一些数学对象和定理，以及一些非常有用的策略。
这本书无意用于对库进行完整描述； `社区 <https://leanprover-community.github.io/>`_ 网页包含了详尽的文档。
不如说，本入门教程是向您介绍形式化背后的思维风格，让您可以轻松浏览库并自行查找内容。

交互式定理证明可能会令人沮丧，学习曲线很陡峭。但是 Lean 社区非常欢迎新人，而且任何时间都有人在 `Lean Zulip 聊天群 <https://leanprover.zulipchat.com/>`_ 上在线回答问题。
我们希望能在那里见到你，并且毫无疑问，很快你也将能够回答这类问题并为 *Mathlib* 的发展做出贡献。

因此，如果你选择接受这个任务，你的使命如下：投入其中，尝试练习，有问题就来 Zulip 提问，并享受乐趣。
但要注意：交互式定理证明将挑战你以全新的方式思考数学和进行数学推理。这可能改变你的生活。

*致谢.* Acknowledgments. We are grateful to Gabriel Ebner for setting up the
infrastructure for running this tutorial in VS Code,
and to Kim Morrison and Mario Carneiro for help porting it from Lean 4.
We are also grateful for help and corrections from
Takeshi Abe,
Julian Berman, Alex Best, Thomas Browning,
Bulwi Cha, Hanson Char, Bryan Gin-ge Chen, Steven Clontz, Mauricio Collaris, Johan Commelin,
Mark Czubin,
Alexandru Duca,
Pierpaolo Frasa,
Denis Gorbachev, Winston de Greef, Mathieu Guay-Paquet,
Marc Huisinga,
Benjamin Jones,
Julian Külshammer,
Victor Liu, Jimmy Lu,
Martin C. Martin, Giovanni Mascellani, John McDowell, Isaiah Mindich, Hunter Monroe,
Pietro Monticone,
Oliver Nash, Emanuelle Natale,
Pim Otte,
Bartosz Piotrowski,
Nicolas Rolland, Keith Rush,
Yannick Seurin, Guilherme Silva,
Pedro Sánchez Terraf, Matthew Toohey, Alistair Tucker,
Floris van Doorn,
Eric Wieser,
and others.
Our work has been partially supported by the Hoskinson Center for
Formal Mathematics.

感谢 `Lean-zh 中文社区<https://www.leanprover.cn/>`_ 的伙伴们参与译本的创作和校对。
TEXT. -/
