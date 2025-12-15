-- BOTH:
import MIL.Common
import Mathlib.Data.Real.Basic

namespace C02S04

/- TEXT:
.. _more_on_order_and_divisibility:

apply 和 rw 的更多例子
--------------------------------

.. index:: min, max

实数上的 ``min`` 函数是由以下三个事实定义的：
TEXT. -/
-- BOTH:
section
variable (a b c d : ℝ)

-- QUOTE:
#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)
-- QUOTE.

/- TEXT:
你可以想象 ``max`` 也使用了类似的定义方式。

注意到我们使用 ``min a b`` 而不是 ``min (a, b)`` 来将 ``min`` 应用于一对参数 ``a`` 和 ``b`` 。从形式上讲，``min`` 是有两个参数的函数，类型为 ``ℝ → ℝ → ℝ`` ，箭头是右结合的，也就是 ``ℝ → (ℝ → ℝ)``。其实际效果是，如果 ``a`` 和 ``b`` 的类型是 ``ℝ`` ，那么 ``min a`` 的类型是 ``ℝ → ℝ``，而 ``min a b`` 的类型是 ``ℝ``。以这种方式处理多个参数被称为 **柯里化（currying）**，以逻辑学家 Haskell Curry 的名字命名。

在 Lean 中，运算的顺序也可能需要一些时间来适应。函数应用比中缀运算的优先级更高，因此表达式 ``min a b + c`` 被解释为 ``(min a b) + c``。你会习惯的。

使用定理 ``le_antisymm`` ，我们可以证明两个实数如果彼此小于或等于对方，则它们相等。利用这一点和上述的事实，我们可以证明 ``min`` 是可交换的：
TEXT. -/
-- QUOTE:
example : min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    apply min_le_left
-- QUOTE.

/- TEXT:
.. index:: show, tactics ; show

这里我们使用点号来分隔不同目标的证明。我们的用法是不一致的：外层对两个目标都使用点和缩进，而内层只对第一个目标使用点。这两种约定都是合理且有用的。我们还使用了 ``show`` 策略，它只是展示目标，没它也一样，但这样更易于阅读和维护。

你可能觉得这个证明有两段是重复的。避免重复的一种方法是陈述一个局部引理，然后使用它：

TEXT. -/
-- QUOTE:
example : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm
  apply h
  apply h
-- QUOTE.

/- TEXT:
我们将在 :numref:`implication_and_the_universal_quantifier` 中更多地讨论全称量词，但在这里只需说一下，假设 ``h`` 表示对于任意的 ``x`` 和 ``y``，所需的不等式成立，``intro`` 策略引入了任意的 ``x`` 和 ``y`` 来证明结论。在 ``le_antisymm`` 后的第一个 ``apply`` 隐式使用了 ``h a b``，而第二个使用了 ``h b a`` 。

.. index:: repeat, tactics ; repeat

另一个避免重复的方法是使用 ``repeat`` 策略，它将一个策略（或一个块）尽可能多次地应用。
TEXT. -/
-- QUOTE:
example : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left
-- QUOTE.

/- TEXT:
练习。你可以使用刚刚描述的任一技巧来缩短第一个证明。
TEXT. -/
-- QUOTE:
-- BOTH:
example : max a b = max b a := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  apply le_antisymm
  repeat
    apply max_le
    apply le_max_right
    apply le_max_left

-- BOTH:
example : min (min a b) c = min a (min b c) := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  apply le_antisymm
  · apply le_min
    · apply le_trans
      apply min_le_left
      apply min_le_left
    apply le_min
    · apply le_trans
      apply min_le_left
      apply min_le_right
    apply min_le_right
  apply le_min
  · apply le_min
    · apply min_le_left
    apply le_trans
    apply min_le_right
    apply min_le_left
  apply le_trans
  apply min_le_right
  apply min_le_right
-- QUOTE.

/- TEXT:
你还可以尝试证明 ``max`` 的结合律。

有趣的是， ``min`` 在 ``max`` 上的分配律就像乘法对加法的分配律一样，反之亦然。换句话说，在实数上，我们有等式 ``min a (max b c) ≤ max (min a b) (min a c)``，以及将 ``max`` 和 ``min`` 交换后的对应版本。但在下一节中，我们将看到这并 **不** 是从 ``≤`` 的传递性和自反性以及上面列举的 ``min`` 和 ``max`` 的特性推导出来的。我们需要使用实数上的 ``≤`` 是 **全序** 的事实，也就是说，它满足 ``∀ x y，x ≤ y ∨ y ≤ x`` 。这里的析取符号， ``∨`` ，代表“或”。在第一种情况下，我们有 ``min x y = x``，而在第二种情况下，我们有 ``min x y = y``。我们将在 :numref:`disjunction` 中学习如何根据情况来推理，但现在我们只会使用不需要拆分情况的例子。

例子：
TEXT. -/
-- QUOTE:
-- BOTH:
theorem aux : min a b + c ≤ min (a + c) (b + c) := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  apply le_min
  · apply add_le_add_right
    apply min_le_left
  apply add_le_add_right
  apply min_le_right

-- BOTH:
example : min a b + c = min (a + c) (b + c) := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  apply le_antisymm
  · apply aux
  have h : min (a + c) (b + c) = min (a + c) (b + c) - c + c := by rw [sub_add_cancel]
  rw [h]
  apply add_le_add_right
  rw [sub_eq_add_neg]
  apply le_trans
  apply aux
  rw [add_neg_cancel_right, add_neg_cancel_right]
-- QUOTE.

/- TEXT:
显然，``aux`` 提供了证明等式所需的两个不等式中的一个，但巧妙地使用它也能证明另一个方向。
提示，你可以使用定理 ``add_neg_cancel_right`` 和 ``linarith`` 策略。

.. index:: absolute value

Mathlib 库中的三角不等式体现了 Lean 的命名规则：
TEXT. -/
-- QUOTE:
#check (abs_add : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)
-- QUOTE.

/- TEXT:
使用它和 ``add_sub_cancel_right`` 和 ``sub_add_cancel`` 来证明以下变形。最好用三行或更少的代码完成。
TEXT. -/
-- QUOTE:
-- BOTH:
example : |a| - |b| ≤ |a - b| :=
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  calc
    |a| - |b| = |a - b + b| - |b| := by rw [sub_add_cancel]
    _ ≤ |a - b| + |b| - |b| := by
      apply sub_le_sub_right
      apply abs_add
    _ ≤ |a - b| := by rw [add_sub_cancel_right]


-- alternatively
example : |a| - |b| ≤ |a - b| := by
  have h := abs_add (a - b) b
  rw [sub_add_cancel] at h
  linarith

-- BOTH:
end
-- QUOTE.

/- TEXT:

.. index:: divisibility

接下来，我们将考察可整除性 ``x ∣ y`` 。可整除符号 **不** 是你键盘上的普通的竖线，而是通过输入 ``\|`` 获得的 Unicode 字符。Mathlib 在定理名称中使用 ``dvd`` 来指代它。
TEXT. -/
-- BOTH:
section
variable (w x y z : ℕ)

-- QUOTE:
example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
  apply dvd_mul_left
-- QUOTE.

/- TEXT:
在最后一个例子中，对于自然数次幂，应用 ``dvd_mul_left`` 会强制 Lean 将 ``x^2`` 的定义展开为 ``x^1 * x``。

看看你能否找出证明以下内容所需的定理：
TEXT. -/
-- QUOTE:
-- BOTH:
example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  apply dvd_add
  · apply dvd_add
    · apply dvd_mul_of_dvd_right
      apply dvd_mul_right
    apply dvd_mul_left
  rw [pow_two]
  apply dvd_mul_of_dvd_right
  exact h

-- BOTH:
end
-- QUOTE.

/- TEXT:
.. index:: gcd, lcm

就可整除性而言， **最大公约数** （ ``gcd`` ）和最小公倍数（ ``lcm`` ）类似于 ``min`` 和 ``max`` 。 由于每个数都可以整除 ``0``，因此 ``0`` 在可整除性的意义下表现得像是最大的元素：
TEXT. -/
-- BOTH:
section
-- QUOTE:
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)
-- QUOTE.

/- TEXT:
试证明：
TEXT. -/
-- QUOTE:
-- BOTH:
example : Nat.gcd m n = Nat.gcd n m := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  apply dvd_antisymm
  repeat
    apply Nat.dvd_gcd
    apply Nat.gcd_dvd_right
    apply Nat.gcd_dvd_left
-- QUOTE.

-- BOTH:
end

/- TEXT:
提示：你可以使用 ``dvd_antisymm``，但它有通用定理和专门针对自然数的两个版本，Lean 有可能会抱怨这里的歧义。此时你可以使用 ``_root_.dvd_antisymm`` 来明确指定使用通用版本，或者 ``Nat.dvd_antisymm`` 来指定使用自然数版本，任何一个都有效。
TEXT. -/

-- OMIT: fix this: protect `dvd_antisymm`.
