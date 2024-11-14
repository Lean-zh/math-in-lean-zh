import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S05

/- TEXT:
.. _disjunction:

析取
-----------

.. index:: left, right, tactics ; left, tactics ; right

证明析取 ``A ∨ B`` （ ``\or`` ）的典型方式是证明 ``A`` 或证明 ``B`` 。 ``left`` 策略选择 ``A`` ， ``right`` 策略选择 ``B`` 。
TEXT. -/
-- BOTH:
section

-- QUOTE:
variable {x y : ℝ}

-- EXAMPLES:
example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]
-- QUOTE.

/- TEXT:
我们不能使用匿名构造子来构造“或”的证明，因为 Lean 猜不出来我们在尝试证明哪个分支。作为替代方式，证明项中可以使用 ``Or.inl`` 和 ``Or.inr`` 来做出明确的选择。这里， ``inl`` 是“引入左项”的缩写，而 ``inr`` 是“引入右项”的缩写。
TEXT. -/
-- QUOTE:
example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h
-- QUOTE.

/- TEXT:
通过证明一边或另一边来证明析取似乎很奇怪。实际上，哪种情况成立通常取决于假设中隐含或明确的情况区分。

我们通过 ``rcases`` 策略来使用形如 ``A ∨ B`` 的假设。与在合取或存在量词中使用 ``rcases`` 不同，这里的 ``rcases`` 策略产生 *两个* 目标。它们都有相同的结论，但在第一种情况下，``A`` 被假定为真，而在第二种情况下，``B`` 被假定为真。换句话说，顾名思义， ``rcases`` 策略给出一个分情况证明。像往常一样，我们可以把假设中用到的名字报告给 Lean。下例中我们告诉 Lean 对每个分支都使用名字 ``h`` 。
TEXT. -/
-- QUOTE:
example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  · rw [abs_of_neg h]
    intro h; right; exact h
-- QUOTE.

/- TEXT:
模式从合取情况下的 ``⟨h₀, h₁⟩`` 变成了析取情况下的 ``h₀ | h₁`` 。可以认为，第一种模式匹配包含 ``h₀`` *和* ``h₁`` 的数据，而第二种模式，也就是带竖线的那种，匹配包含 ``h₀`` *或* ``h₁`` 的数据。在这种情况下，因为两个目标分离，我们对两种情况可以使用同样的名字 ``h`` 。

绝对值函数的定义使得我们可以立即证明 ``x ≥ 0`` 蕴含着 ``|x| = x`` (这就是定理 ``abs_of_nonneg``) 而 ``x < 0`` 则蕴含着 ``|x| = -x``（这是 ``abs_of_neg`` ）。表达式 ``le_or_gt 0 x`` 推出 ``0 ≤ x ∨ x < 0`` ，使我们可以将这两种情况分开。

析取也支持专家式模式匹配语法。此时最好用 ``cases`` 策略，因为它允许我们为每个 ``cases`` 命名，并在更接近使用的地方为引入的假设命名。
TEXT. -/
-- QUOTE:
example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h
-- QUOTE.

/- TEXT:
名字 ``inl`` 和 ``inr`` 分别是 "intro left" 和 "intro right" 的缩写。使用 ``cases`` 的好处是你可以以任意顺序证明每种情况；Lean 使用标签找到相关的目标。如果你不在乎这个，你可以使用 ``next`` 或者 ``match`` ，甚至是模式匹配版的 ``have`` 。
TEXT. -/
-- QUOTE:
example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h
-- QUOTE.

/- TEXT:
``match`` 下需要用全称 ``Or.inl`` 和 ``Or.inr`` 来证明析取。本书通常会使用 ``rcases`` 来分割析取的情况。

试着用下面前两个定理证明三角不等式。Mathlib 中它也叫这个名字。
TEXT. -/
-- BOTH:
-- QUOTE:
namespace MyAbs

-- EXAMPLES:
theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  sorry

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  sorry

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  sorry
-- QUOTE.

-- SOLUTIONS:
theorem le_abs_selfαα (x : ℝ) : x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h]
    linarith

theorem neg_le_abs_selfαα (x : ℝ) : -x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
    linarith
  · rw [abs_of_neg h]

theorem abs_addαα (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rcases le_or_gt 0 (x + y) with h | h
  · rw [abs_of_nonneg h]
    linarith [le_abs_self x, le_abs_self y]
  · rw [abs_of_neg h]
    linarith [neg_le_abs_self x, neg_le_abs_self y]

/- TEXT:
如果你喜欢这些“分情况讨论”，可以试试这些。
try these.
TEXT. -/
-- QUOTE:
theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  sorry

theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  sorry
-- QUOTE.

-- SOLUTIONS:
theorem lt_absαα : x < |y| ↔ x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    constructor
    · intro h'
      left
      exact h'
    · intro h'
      rcases h' with h' | h'
      · exact h'
      · linarith
  rw [abs_of_neg h]
  constructor
  · intro h'
    right
    exact h'
  · intro h'
    rcases h' with h' | h'
    · linarith
    · exact h'

theorem abs_ltαα : |x| < y ↔ -y < x ∧ x < y := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
    constructor
    · intro h'
      constructor
      · linarith
      exact h'
    · intro h'
      rcases h' with ⟨h1, h2⟩
      exact h2
  · rw [abs_of_neg h]
    constructor
    · intro h'
      constructor
      · linarith
      · linarith
    · intro h'
      linarith

-- BOTH:
end MyAbs

end

/- TEXT:
你也可以将 ``rcases`` 和 ``rintro`` 与嵌套析取一起使用。当这些功能导致一个真正包含多个目标的情况划分时，每个新目标的模式都会用竖线隔开。
TEXT. -/
-- QUOTE:
example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  · right; exact xgt
-- QUOTE.

/- TEXT:
你仍然可以进行模式嵌套，并使用 ``rfl`` 来替换等式：
TEXT. -/
-- QUOTE:
example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  · rw [mul_comm, mul_assoc]
    apply dvd_mul_right
-- QUOTE.

/- TEXT:
尝试用一行证明下面的内容。使用 ``rcases`` 解包假设并分情况讨论，并使用分号和 ``linarith`` 解决每个分支。
TEXT. -/
-- QUOTE:
example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  rcases h with ⟨x, y, rfl | rfl⟩ <;> linarith [sq_nonneg x, sq_nonneg y]

/- TEXT:
在实数中，等式 ``x * y = 0`` 告诉我们 ``x = 0`` 或 ``y = 0`` 。在 Mathlib 中， 这个事实被命名为 ``eq_zero_or_eq_zero_of_mul_eq_zero`` ，它是展示生产析取的另一个好例子。使用它证明下列命题（使用 ``ring`` 策略简化计算）：
TEXT. -/
-- QUOTE:
example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  sorry

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h' : x ^ 2 - 1 = 0 := by rw [h, sub_self]
  have h'' : (x + 1) * (x - 1) = 0 := by
    rw [← h']
    ring
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h'' with h1 | h1
  · right
    exact eq_neg_iff_add_eq_zero.mpr h1
  · left
    exact eq_of_sub_eq_zero h1

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h' : x ^ 2 - y ^ 2 = 0 := by rw [h, sub_self]
  have h'' : (x + y) * (x - y) = 0 := by
    rw [← h']
    ring
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h'' with h1 | h1
  · right
    exact eq_neg_iff_add_eq_zero.mpr h1
  · left
    exact eq_of_sub_eq_zero h1

/- TEXT:
在任意环 :math:`R` 中，对于元素 :math:`x`, 若存在非零元素 :math:`y` 使得 :math:`x y = 0` ，则我们把 :math:`x` 称为一个 *左零因子*，若存在非零元素 :math:`y` 使得 :math:`y x = 0`, 则我们把 :math:`x` 称为一个 *右零因子*，是左或右零因子的元素称为 *零因子*。定理 ``eq_zero_or_eq_zero_of_mul_eq_zero`` 是说实数中没有非平凡的零因子。具有这一性质的交换环称为 *整环*。你对上面两个定理的证明在任意整环中应同样成立：
TEXT. -/
-- BOTH:
section
-- QUOTE:
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

-- EXAMPLES:
example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  sorry

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h' : x ^ 2 - 1 = 0 := by rw [h, sub_self]
  have h'' : (x + 1) * (x - 1) = 0 := by
    rw [← h']
    ring
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h'' with h1 | h1
  · right
    exact eq_neg_iff_add_eq_zero.mpr h1
  · left
    exact eq_of_sub_eq_zero h1

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h' : x ^ 2 - y ^ 2 = 0 := by rw [h, sub_self]
  have h'' : (x + y) * (x - y) = 0 := by
    rw [← h']
    ring
  rcases eq_zero_or_eq_zero_of_mul_eq_zero h'' with h1 | h1
  · right
    exact eq_neg_iff_add_eq_zero.mpr h1
  · left
    exact eq_of_sub_eq_zero h1

-- BOTH:
end

/- TEXT:
你证明第一个定理时可以不使用乘法交换律。在那种情况下，只需假定 ``R`` 是一个 ``Ring`` 而非 ``CommRing`` 。

.. index:: excluded middle

有时在一个证明中我们想要根据一个语句是否为真来划分情况。对于任何命题 ``P`` ，我们可以使用 ``em P : P ∨ ¬ P`` 。名字 ``em`` 是 "excluded middle (排中律)" 的缩写。
TEXT. -/
-- QUOTE:
example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  · contradiction
-- QUOTE.

/- TEXT:
.. index:: by_cases, tactics ; by_cases

或者，你也可以使用 ``by_cases`` 策略。
TEXT. -/
-- QUOTE:
-- EXAMPLES:
example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction
-- QUOTE.

/- TEXT:
注意到 ``by_cases`` 策略要求你为假设提供一个标签，该标签被用于各个分支，在这个例子中，一个分支是 ``h' : P`` 而另一个是 ``h' : ¬ P`` 。如果你留空， Lean 默认使用标签 ``h`` 。尝试证明如下等价性，使用 ``by_cases`` 解决其中一个方向。
TEXT. -/
-- QUOTE:
example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  constructor
  · intro h
    by_cases h' : P
    · right
      exact h h'
    · left
      exact h'
  rintro (h | h)
  · intro h'
    exact absurd h' h
  · intro
    exact h
