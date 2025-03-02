import Mathlib.Data.Nat.GCD.Basic
import MIL.Common

/- TEXT:
.. _section_induction_and_recursion:

归纳与递归
----------

自然数集 :math:`\mathbb{N} = \{ 0, 1, 2, \ldots \}`
不仅本身具有根本的重要性，而且在新数学对象的构建中也起着核心作用。
Lean 的基础允许我们声明 **归纳类型** ，这些类型由给定的 **构造子** 列表归纳生成。
在 Lean 中，自然数是这样声明的。
OMIT: -/
namespace hidden

-- QUOTE:
inductive Nat where
  | zero : Nat
  | succ (n : Nat) : Nat
-- QUOTE.

end hidden

/- TEXT:
您可以在库中通过输入 ``#check Nat`` 然后 ``Ctrl + 点击`` 标识符 ``Nat`` 来找到它。该命令指定了 ``Nat`` 是由两个构造函数 ``zero ： Nat`` 和 ``succ ： Nat → Nat`` 自然且归纳地生成的数据类型。当然，库中为 ``nat`` 和 ``zero`` 分别引入了记号 ``ℕ`` 和 ``0`` 。（数字会被转换为二进制表示，但现在我们不必担心这些细节。）

对于数学工作者而言，“自然”意味着类型 ``Nat`` 有一个元素 ``zero`` 以及一个单射的后继函数 ``succ`` ，其值域不包含 ``zero`` 。
EXAMPLES: -/
-- QUOTE:
example (n : Nat) : n.succ ≠ Nat.zero :=
  Nat.succ_ne_zero n

example (m n : Nat) (h : m.succ = n.succ) : m = n :=
  Nat.succ.inj h
-- QUOTE.

/- TEXT:
对于数学工作者而言，“归纳”这个词意味着自然数附带有一个归纳证明原则和一个递归定义原则。本节将向您展示如何使用这些原则。

以下是一个阶乘函数的递归定义示例。
BOTH: -/
-- QUOTE:
def fac : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * fac n
-- QUOTE.

/- TEXT:
这种语法需要一些时间来适应。
请注意第一行没有 ``:=`` 。
接下来的两行提供了递归定义的基础情况和归纳步骤。
这些等式是定义性成立的，但也可以通过将名称 ``fac`` 给予 ``simp`` 或 ``rw`` 来手动使用。
EXAMPLES: -/
-- QUOTE:
example : fac 0 = 1 :=
  rfl

example : fac 0 = 1 := by
  rw [fac]

example : fac 0 = 1 := by
  simp [fac]

example (n : ℕ) : fac (n + 1) = (n + 1) * fac n :=
  rfl

example (n : ℕ) : fac (n + 1) = (n + 1) * fac n := by
  rw [fac]

example (n : ℕ) : fac (n + 1) = (n + 1) * fac n := by
  simp [fac]
-- QUOTE.

/- TEXT:
阶乘函数实际上已经在 Mathlib 中定义为 ``Nat.factorial`` 。您可以通过输入 ``#check Nat.factorial`` 并使用 ``Ctrl + 点击`` 跳转到它。为了便于说明，我们在示例中将继续使用 ``fac`` 。定义 ``Nat.factorial`` 前面的注释 ``@[simp]`` 指定定义方程应添加到简化的默认等式数据库中。
归纳法原理指出，我们可以通过证明某个关于自然数的一般性陈述对 0 成立，并且每当它对某个自然数 :math:`n` 成立时，它对 :math:`n + 1` 也成立，从而证明该一般性陈述。因此，在下面的证明中，行 ``induction' n with n ih`` 会产生两个目标：在第一个目标中，我们需要证明  ``0 < fac 0`` ；在第二个目标中，我们有额外的假设  ``ih : 0 < fac n`` ，并且需要证明  ``0 < fac (n + 1)`` 。短语 ``with n ih`` 用于为归纳假设命名变量和假设，您可以为它们选择任何名称。
EXAMPLES: -/
-- QUOTE:
theorem fac_pos (n : ℕ) : 0 < fac n := by
  induction' n with n ih
  · rw [fac]
    exact zero_lt_one
  rw [fac]
  exact mul_pos n.succ_pos ih
-- QUOTE.

/- TEXT:

该 ``induction`` 策略足够智能，能够将依赖于归纳变量的假设作为归纳假设的一部分包含进来。
接下来，我们可以逐步执行一个示例，以具体说明这一过程。
EXAMPLES: -/
-- QUOTE:
theorem dvd_fac {i n : ℕ} (ipos : 0 < i) (ile : i ≤ n) : i ∣ fac n := by
  induction' n with n ih
  · exact absurd ipos (not_lt_of_ge ile)
  rw [fac]
  rcases Nat.of_le_succ ile with h | h
  · apply dvd_mul_of_dvd_right (ih h)
  rw [h]
  apply dvd_mul_right
-- QUOTE.

/- TEXT:
以下示例为阶乘函数提供了一个粗略的下界。
结果发现，从分情况证明入手会更容易些，这样证明的其余部分就从 :math:`n = 1` 的情况开始。
尝试使用 ``pow_succ`` 或 ``pow_succ'`` 通过归纳法完成论证。
BOTH: -/
-- QUOTE:
theorem pow_two_le_fac (n : ℕ) : 2 ^ (n - 1) ≤ fac n := by
  rcases n with _ | n
  · simp [fac]
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  induction' n with n ih
  · simp [fac]
  simp at *
  rw [pow_succ', fac]
  apply Nat.mul_le_mul _ ih
  repeat' apply Nat.succ_le_succ
  apply zero_le

-- BOTH:
-- QUOTE.
/- TEXT:
归纳法常用于证明涉及有限和与乘积的恒等式。
Mathlib 定义了表达式  ``Finset.sum s f`` ，其中 ``s : Finset α`` 是类型为 ``α`` 的元素的有限集合，而 ``f`` 是定义在 ``α`` 上的函数。
 ``f``  的值域可以是任何支持交换、结合加法运算且具有零元素的类型。
如果您导入 ``Algebra.BigOperators.Basic`` 并执行命令  ``open BigOperators`` ，则可以使用更直观的符号  ``∑ x in s, f x`` 。当然，对于有限乘积也有类似的运算和符号。

我们将在下一节以及稍后的章节中讨论 ``Finset`` 类型及其支持的操作。目前，我们仅使用  ``Finset.range n`` ，它表示小于 ``n`` 的自然数的有限集合。
BOTH: -/
section

-- QUOTE:
variable {α : Type*} (s : Finset ℕ) (f : ℕ → ℕ) (n : ℕ)

-- EXAMPLES:
#check Finset.sum s f
#check Finset.prod s f

-- BOTH:
open BigOperators
open Finset

-- EXAMPLES:
example : s.sum f = ∑ x in s, f x :=
  rfl

example : s.prod f = ∏ x in s, f x :=
  rfl

example : (range n).sum f = ∑ x in range n, f x :=
  rfl

example : (range n).prod f = ∏ x in range n, f x :=
  rfl
-- QUOTE.

/- TEXT:
事实 ``Finset.sum_range_zero`` 和 ``Finset.sum_range_succ`` 为求和至 :math:`n` 提供了递归描述，乘积的情况也是如此。
EXAMPLES: -/
-- QUOTE:
example (f : ℕ → ℕ) : ∑ x in range 0, f x = 0 :=
  Finset.sum_range_zero f

example (f : ℕ → ℕ) (n : ℕ) : ∑ x in range n.succ, f x = ∑ x in range n, f x + f n :=
  Finset.sum_range_succ f n

example (f : ℕ → ℕ) : ∏ x in range 0, f x = 1 :=
  Finset.prod_range_zero f

example (f : ℕ → ℕ) (n : ℕ) : ∏ x in range n.succ, f x = (∏ x in range n, f x) * f n :=
  Finset.prod_range_succ f n
-- QUOTE.

/- TEXT:
每对中的第一个恒等式是定义性的，也就是说，您可以将证明替换为 ``rfl`` 。

以下表达的是我们定义为乘积形式的阶乘函数。
EXAMPLES: -/
-- QUOTE:
example (n : ℕ) : fac n = ∏ i in range n, (i + 1) := by
  induction' n with n ih
  · simp [fac, prod_range_zero]
  simp [fac, ih, prod_range_succ, mul_comm]
-- QUOTE.

/- TEXT:
我们将 ``mul_comm`` 作为简化规则包含在内这一事实值得评论。
使用恒等式 ``x * y = y * x`` 进行简化似乎很危险，因为这通常会导致无限循环。
不过，Lean 的简化器足够聪明，能够识别这一点，并且仅在结果项在某些固定但任意的项排序中具有较小值的情况下应用该规则。
下面的示例表明，使用  ``mul_assoc`` 、 ``mul_comm``  和 ``mul_left_comm`` 这三条规则进行简化，能够识别出括号位置和变量顺序不同但实质相同的乘积。
EXAMPLES: -/
-- QUOTE:
example (a b c d e f : ℕ) : a * (b * c * f * (d * e)) = d * (a * f * e) * (c * b) := by
  simp [mul_assoc, mul_comm, mul_left_comm]
-- QUOTE.

/- TEXT:
大致来说，这些规则的作用是将括号向右推移，然后重新排列两边的表达式，直到它们都遵循相同的规范顺序。利用这些规则以及相应的加法规则进行简化，是个很实用的技巧。

回到求和恒等式，我们建议按照以下证明步骤来证明自然数之和（从 1 加到 n）等于 :math:`n (n + 1) / 2`。
证明的第一步是消去分母。
这在形式化恒等式时通常很有用，因为涉及除法的计算通常会有附加条件。
（同样，在可能的情况下避免在自然数上使用减法也是有用的。）
EXAMPLES: -/
-- QUOTE:
theorem sum_id (n : ℕ) : ∑ i in range (n + 1), i = n * (n + 1) / 2 := by
  symm; apply Nat.div_eq_of_eq_mul_right (by norm_num : 0 < 2)
  induction' n with n ih
  · simp
  rw [Finset.sum_range_succ, mul_add 2, ← ih]
  ring
-- QUOTE.

/- TEXT:
我们鼓励您证明类似的平方和恒等式，以及您在网上能找到的其他恒等式。
BOTH: -/
-- QUOTE:
theorem sum_sqr (n : ℕ) : ∑ i in range (n + 1), i ^ 2 = n * (n + 1) * (2 * n + 1) / 6 := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  symm;
  apply Nat.div_eq_of_eq_mul_right (by norm_num : 0 < 6)
  induction' n with n ih
  · simp
  rw [Finset.sum_range_succ, mul_add 6, ← ih]
  ring
-- QUOTE.

-- BOTH:
end

/- TEXT:
在 Lean 的核心库中，加法和乘法本身是通过递归定义来定义的，并且它们的基本性质是通过归纳法来确立的。
如果您喜欢思考诸如基础性的话题，您可能会喜欢证明乘法和加法的交换律和结合律以及乘法对加法的分配律。
您可以在自然数的副本上按照下面的提纲进行操作。
请注意，我们可以对 ``MyNat`` 使用 ``induction`` 策略；
Lean 足够聪明，知道要使用相关的归纳原理（当然，这与 ``Nat`` 的归纳原理相同）。

我们先从加法的交换律讲起。
一个不错的经验法则是，由于加法和乘法都是通过在第二个参数上递归定义的，所以通常在证明中对处于该位置的变量进行归纳证明是有利的。
在证明结合律时，决定使用哪个变量有点棘手。

在没有通常的零、一、加法和乘法符号的情况下书写内容可能会令人困惑。
稍后我们将学习如何定义此类符号。
在命名空间 ``MyNat`` 中工作意味着我们可以写 ``zero`` 和 ``succ`` 而不是 ``MyNat.zero`` 和  ``MyNat.succ`` ，
并且这些名称的解释优先于其他解释。
在命名空间之外，例如下面定义的 ``add`` 的完整名称是 ``MyNat.add`` 。

如果您发现自己确实喜欢这类事情，不妨试着定义截断减法和幂运算，并证明它们的一些性质。
请记住，截断减法在结果为零时会停止。
要定义截断减法，定义一个前驱函数 ``pred`` 会很有用，该函数对任何非零数减一，并将零固定不变。
函数 ``pred`` 可以通过简单的递归实例来定义。
BOTH: -/
-- QUOTE:
inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat

namespace MyNat

def add : MyNat → MyNat → MyNat
  | x, zero => x
  | x, succ y => succ (add x y)

def mul : MyNat → MyNat → MyNat
  | x, zero => zero
  | x, succ y => add (mul x y) x

theorem zero_add (n : MyNat) : add zero n = n := by
  induction' n with n ih
  · rfl
  rw [add, ih]

theorem succ_add (m n : MyNat) : add (succ m) n = succ (add m n) := by
  induction' n with n ih
  · rfl
  rw [add, ih]
  rfl

theorem add_comm (m n : MyNat) : add m n = add n m := by
  induction' n with n ih
  · rw [zero_add]
    rfl
  rw [add, succ_add, ih]

theorem add_assoc (m n k : MyNat) : add (add m n) k = add m (add n k) := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  induction' k with k ih
  · rfl
  rw [add, ih]
  rfl

-- BOTH:
theorem mul_add (m n k : MyNat) : mul m (add n k) = add (mul m n) (mul m k) := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  induction' k with k ih
  · rfl
  rw [add, mul, mul, ih, add_assoc]

-- BOTH:
theorem zero_mul (n : MyNat) : mul zero n = zero := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  induction' n with n ih
  · rfl
  rw [mul, ih]
  rfl

-- BOTH:
theorem succ_mul (m n : MyNat) : mul (succ m) n = add (mul m n) n := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  induction' n with n ih
  · rfl
  rw [mul, mul, ih, add_assoc, add_assoc, add_comm n, succ_add]
  rfl

-- BOTH:
theorem mul_comm (m n : MyNat) : mul m n = mul n m := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  induction' n with n ih
  · rw [zero_mul]
    rfl
  rw [mul, ih, succ_mul]

-- BOTH:
end MyNat
-- QUOTE.
