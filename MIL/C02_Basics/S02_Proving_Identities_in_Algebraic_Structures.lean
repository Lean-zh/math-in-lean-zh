-- BOTH:
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Real.Basic
import MIL.Common

/- TEXT:
.. _proving_identities_in_algebraic_structures:

证明代数结构中的等式
------------------------------------------

.. index:: ring (algebraic structure)

数学中，环由一个对象集合 :math:`R`、运算 :math:`+` :math:`\times`、常数 :math:`0` 和 :math:`1`、求逆运算 :math:`x \mapsto -x` 构成，并满足：

- :math:`R` 与 :math:`+` 构成 **阿贝尔群** ，:math:`0` 是加法单位元，负数是逆。
- :math:`1` 是乘法单位元，乘法满足结合律和对加法的分配律。

在 Lean 中，一组对象被表示为 **类型** ``R``。环公理如下：
TEXT. -/
section
-- QUOTE:
variable (R : Type*) [Ring R]

#check (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))
#check (add_comm : ∀ a b : R, a + b = b + a)
#check (zero_add : ∀ a : R, 0 + a = a)
#check (neg_add_cancel : ∀ a : R, -a + a = 0)
#check (mul_assoc : ∀ a b c : R, a * b * c = a * (b * c))
#check (mul_one : ∀ a : R, a * 1 = a)
#check (one_mul : ∀ a : R, 1 * a = a)
#check (mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c)
#check (add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c)
-- QUOTE.

end

/- TEXT:
一会儿再讲第一行的方括号是什么意思，现在你只需要知道我们声明了一个类型 ``R`` 和 ``R`` 上的环结构。这样我们就可以表示一般的环中的元素并使用环的定理库。

前一节用过上面的一些定理，所以你应该感觉很熟悉。Lean 不止能在例如自然数和整数这样具体的数学结构上证明东西，也可以在环这样抽象的公理化的结构上证明东西。Lean 支持抽象和具体结构的 **通用推理** ，并且有能力识别符合公理的实例。任何关于环的定理都可以应用于具体的环，如整数 ``ℤ``、有理数 ``ℚ``、复数 ``ℂ``，和抽象的环，如任何有序环或任何域。

.. index:: commutative ring

然而，并不是所有实数的重要性质在任意环中都成立。例如，实数乘法是可交换的，但一般情况下并不成立。例如实数矩阵构成的环的乘法通常不能交换。如果我们声明 ``R`` 是一个 **交换环** ``CommRing``，那么上一节中的所有关于 ``ℝ`` 的定理在 ``R`` 中仍然成立。
TEXT. -/
section
-- QUOTE:
variable (R : Type*) [CommRing R]
variable (a b c d : R)

example : c * b * a = b * (a * c) := by ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring
-- QUOTE.

end

/- TEXT:
别的证明也都不需要变，你可以自己试试看。当证明很短时，比如你只用了一个 ``ring`` 或者 ``linarith`` 或者 ``sorry``，你可以把它们写进 ``by`` 的同一行里。好的证明写手需要平衡简洁性和可读性。

本节里面我们会证明更多环定理，它们基本上都在 Mathlib 里面，看完这一节你会对 Mathlib 里面的东西更熟悉。同时这也是训练你的证明能力。

.. index:: namespace, open, command ; open

Lean 提供了类似于别的编程语言中的 “局域变量” 的变量名组织机制。通过命令 ``namespace bar`` 创建一个 **命名空间** ``bar`` 并引入定义或者定理 ``foo``，你在命名空间外面引用它时全名为 ``bar.foo``。命令 ``open bar`` 可以 **打开** 这个命名空间，此时你可以用短名字 ``foo``。下面我们为了不与 Mathlib 中的定理名冲突，我们打开一个名为 ``MyRing`` 的命名空间。

下面的例子证明了 ``add_zero`` 和 ``add_right_neg``，所以它们不需要作为环公理。
TEXT. -/
-- QUOTE:
namespace MyRing
variable {R : Type*} [Ring R]

theorem add_zero (a : R) : a + 0 = a := by rw [add_comm, zero_add]

theorem add_right_neg (a : R) : a + -a = 0 := by rw [add_comm, neg_add_cancel]

#check MyRing.add_zero
#check add_zero

end MyRing
-- QUOTE.

/- TEXT:
我们重新证明了库中的定理，但是我们可以继续使用库中的版本。但是下面的练习中请不要作弊，我们只能用我们之前证明过的定理。

（如果你仔细注意的话，你可能已经注意到我们把 ``(R: Type*)`` 中的圆括号改成了 ``{R: Type*}`` 中的花括号。这里声明 ``R`` 是一个 **隐式参数（implicit argument）** 。稍后会解释这意味着什么。）

下面这个定理很有用：
TEXT. -/
-- BOTH:
namespace MyRing
variable {R : Type*} [Ring R]

-- EXAMPLES:
-- QUOTE:
theorem neg_add_cancel_left (a b : R) : -a + (a + b) = b := by
  rw [← add_assoc, neg_add_cancel, zero_add]
-- QUOTE.

/- TEXT:
证明它的配套版本：
TEXT. -/
-- Prove these:
-- QUOTE:
theorem add_neg_cancel_right (a b : R) : a + b + -b = a := by
  sorry
-- QUOTE.

-- SOLUTIONS:
theorem add_neg_cancel_rightαα (a b : R) : a + b + -b = a := by
  rw [add_assoc, add_right_neg, add_zero]

/- TEXT:
然后用它们证明下面几个（最佳方案仅需三次重写）：
TEXT. -/
-- QUOTE:
theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  sorry

theorem add_right_cancel {a b c : R} (h : a + b = c + b) : a = c := by
  sorry
-- QUOTE.

-- SOLUTIONS:
theorem add_left_cancelαα {a b c : R} (h : a + b = a + c) : b = c := by
  rw [← neg_add_cancel_left a b, h, neg_add_cancel_left]

theorem add_right_cancelαα {a b c : R} (h : a + b = c + b) : a = c := by
  rw [← add_neg_cancel_right a b, h, add_neg_cancel_right]

/- TEXT:
.. index:: implicit argument

现在解释一下花括号的意思。
假设你现在语句集里面拥有变量 ``a``、``b``、``c`` 和一个假设 ``h : a + b = a + c``，
然后你想得到结论 ``b = c``。
在Lean中，定理可以应用于假设和事实，就像将它们应用于对象一样，
因此你可能会认为 ``add_left_cancel a b c h`` 是事实 ``b = c`` 的证明。
但其实明确地写出 ``a b c`` 是多余的，因为假设 ``h`` 的形式就限定了它们正是我们想使用的对象。
现下输入几个额外的字符并不麻烦，但是更复杂的表达式中就会很繁琐。
Lean 支持把参数标记为 **隐式** ，这意味着它们可以且应该被省略，能通过后面的的命题和假设中推断出来。
``{a b c: R}`` 中的花括号正是这种隐式参数标记。
因此根据定理的表述，正确的表达式是 ``add_left_cancel h``。

下面演示个新玩意儿，让我们从环公理中证明 ``a * 0 = 0``。
TEXT. -/
-- QUOTE:
theorem mul_zero (a : R) : a * 0 = 0 := by
  have h : a * 0 + a * 0 = a * 0 + 0 := by
    rw [← mul_add, add_zero, add_zero]
  rw [add_left_cancel h]
-- QUOTE.

/- TEXT:
.. index:: have, tactics ; have

你通过 ``have`` 策略引入了一个辅助性新目标，``a * 0 + a * 0 = a * 0 + 0``，与原始目标具有相同的语境。这个目标下的“子证明”块需要缩进。证出这个子目标之后我们就多了一个新的命题 ``h`` ，可以用于证明原目标。这里我们看到 ``add_left_cancel h`` 的结果恰好就是原目标。

.. index:: apply, tactics ; apply, exact, tactics ; exact

我们同样可以使用 ``apply add_left_cancel h`` 或 ``exact add_left_cancel h`` 来结束证明。``exact`` 策略将能够完整证明当前目标的证明项作为参数，而不创建任何新目标。``apply`` 策略是一种变体，它的论证不一定是一个完整的证明。缺失的部分要么由 Lean 自动推断，要么成为需要证明的新目标。虽然 ``exact`` 策略在技术上是多余的，因为它严格来说不如 ``apply`` 强大，但它增加了可读性。(下一节详细讲解 ``apply`` 策略的用法。)

乘法不一定可交换，所以下面的定理也需要证。
TEXT. -/
-- QUOTE:
theorem zero_mul (a : R) : 0 * a = 0 := by
  sorry
-- QUOTE.

-- SOLUTIONS:
theorem zero_mulαα (a : R) : 0 * a = 0 := by
  have h : 0 * a + 0 * a = 0 * a + 0 := by rw [← add_mul, add_zero, add_zero]
  rw [add_left_cancel h]

/- TEXT:
更多练习：
TEXT. -/
-- QUOTE:
theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
  sorry

theorem eq_neg_of_add_eq_zero {a b : R} (h : a + b = 0) : a = -b := by
  sorry

theorem neg_zero : (-0 : R) = 0 := by
  apply neg_eq_of_add_eq_zero
  rw [add_zero]

theorem neg_neg (a : R) : - -a = a := by
  sorry
-- QUOTE.

-- SOLUTIONS:
theorem neg_eq_of_add_eq_zeroαα {a b : R} (h : a + b = 0) : -a = b := by
  rw [← neg_add_cancel_left a b, h, add_zero]

theorem eq_neg_of_add_eq_zeroαα {a b : R} (h : a + b = 0) : a = -b := by
  symm
  apply neg_eq_of_add_eq_zero
  rw [add_comm, h]

theorem neg_zeroαα : (-0 : R) = 0 := by
  apply neg_eq_of_add_eq_zero
  rw [add_zero]

theorem neg_negαα (a : R) : - -a = a := by
  apply neg_eq_of_add_eq_zero
  rw [neg_add_cancel]

-- BOTH:
end MyRing

/- TEXT:
我们必须在第三个定理中指定 ``(-0 : R)``, 因为 Lean 不知道我们想到的是哪个 ``0``，默认情况下它是自然数。

在 Lean 中，环中减去一个元素等于加上它的加法逆元。
TEXT. -/
-- Examples.
section
variable {R : Type*} [Ring R]

-- QUOTE:
example (a b : R) : a - b = a + -b :=
  sub_eq_add_neg a b
-- QUOTE.

end

/- TEXT:
实数的减法就是被如此 **定义** 的，因此：
TEXT. -/
-- QUOTE:
example (a b : ℝ) : a - b = a + -b :=
  rfl

example (a b : ℝ) : a - b = a + -b := by
  rfl
-- QUOTE.

/- TEXT:
.. index:: rfl, reflexivity, tactics ; refl and reflexivity, definitional equality

``rfl`` 是自反性（reflexivity）的缩写。
第一个例子中当它作为 ``a - b = a + -b`` 的证明项，Lean 展开定义并验证两边是相同的。
第二个例子中 ``rfl`` 策略也是如此。
这是在 Lean 的基础逻辑中所谓的 **定义相等** 的一个例子。
这意味着不仅可以用 ``sub_eq_add_neg`` 重写来替换 ``a - b = a + -b``，
而且在某些情况下，当处理实数时，您可以互换使用方程的两边。
例如，您现在有足够的信息来证明上一节中的 ``self_sub`` 定理:
TEXT. -/
-- BOTH:
namespace MyRing
variable {R : Type*} [Ring R]

-- EXAMPLES:
-- QUOTE:
theorem self_sub (a : R) : a - a = 0 := by
  sorry
-- QUOTE.

-- SOLUTIONS:
theorem self_subαα (a : R) : a - a = 0 := by
  rw [sub_eq_add_neg, add_right_neg]

/- TEXT:
你可以使用 ``rw`` 来证，不过如果不是任意环 ``R`` 而是实数的话，你也可以用 ``apply`` 或者 ``exact``。

Lean 知道 ``1 + 1 = 2`` 对任何环都成立。你可以用它来证明上一节中的定理 ``two_mul``：
TEXT. -/
-- QUOTE:
-- BOTH:
theorem one_add_one_eq_two : 1 + 1 = (2 : R) := by
  norm_num

-- EXAMPLES:
theorem two_mul (a : R) : 2 * a = a + a := by
  sorry
-- QUOTE.

-- SOLUTIONS:
theorem two_mulαα (a : R) : 2 * a = a + a := by
  rw [← one_add_one_eq_two, add_mul, one_mul]

-- BOTH:
end MyRing

/- TEXT:
.. index:: group (algebraic structure)

上面的一些定理并不需要环结构甚至加法交换律，有 **群** 结构就够了，群公理是下面这些：
TEXT. -/
section
-- QUOTE:
variable (A : Type*) [AddGroup A]

#check (add_assoc : ∀ a b c : A, a + b + c = a + (b + c))
#check (zero_add : ∀ a : A, 0 + a = a)
#check (neg_add_cancel : ∀ a : A, -a + a = 0)
-- QUOTE.

end

/- TEXT:
群运算可交换的话习惯上用加号（但是这只是习惯而已，``AddGroup`` 并不真的可交换），否则用乘号。Lean 提供乘法版本 ``Group`` 和加法版本 ``AddGroup`` ，以及它们的可交换版本 ``CommGroup`` 和 ``AddCommGroup``。
TEXT. -/
-- BOTH:
section
-- QUOTE:
variable {G : Type*} [Group G]

-- EXAMPLES:
#check (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
#check (one_mul : ∀ a : G, 1 * a = a)
#check (inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1)
-- QUOTE.

/- TEXT:
试试用这些群公理证明以下命题。你可以引入一些引理。
TEXT. -/
-- BOTH:
namespace MyGroup

-- EXAMPLES:
-- QUOTE:
theorem mul_inv_cancel (a : G) : a * a⁻¹ = 1 := by
  sorry

theorem mul_one (a : G) : a * 1 = a := by
  sorry

theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  sorry
-- QUOTE.

-- SOLUTIONS:
theorem mul_inv_cancelαα (a : G) : a * a⁻¹ = 1 := by
  have h : (a * a⁻¹)⁻¹ * (a * a⁻¹ * (a * a⁻¹)) = 1 := by
    rw [mul_assoc, ← mul_assoc a⁻¹ a, inv_mul_cancel, one_mul, inv_mul_cancel]
  rw [← h, ← mul_assoc, inv_mul_cancel, one_mul]

theorem mul_oneαα (a : G) : a * 1 = a := by
  rw [← inv_mul_cancel a, ← mul_assoc, mul_inv_cancel, one_mul]

theorem mul_inv_revαα (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  rw [← one_mul (b⁻¹ * a⁻¹), ← inv_mul_cancel (a * b), mul_assoc, mul_assoc, ← mul_assoc b b⁻¹,
    mul_inv_cancel, one_mul, mul_inv_cancel, mul_one]

-- BOTH:
end MyGroup

end

/- TEXT:
.. index:: group (tactic), tactics ; group, tactics ; noncomm_ring, tactics ; abel
一步一步用这些定理做证明非常麻烦，所以在这些代数结构上 Mathlib 提供了类似 ``ring`` 的策略：``group`` 用于非交换的乘法群，``abel`` 用于可交换加法群，``noncomm_ring`` 用于非交换环。代数结构 ``Ring`` 和 ``CommRing`` 分别对应的自动化策略被称做 ``noncomm_ring`` 和 ``ring``，这似乎很奇怪。这在一定程度上是由于历史原因，但也因为使用更短的名称来处理交换环的策略更方便，因为它使用得更频繁。

TEXT. -/
