-- BOTH:
import MIL.Common
import Mathlib.Data.Real.Basic

set_option autoImplicit true

namespace C03S02

/- TEXT:
.. _the_existential_quantifier:

存在量词
--------------------------

存在量词 ``∃`` （ ``\ex`` ）用于表示短语“存在” 。Lean 中的形式表达式 ``∃ x : ℝ, 2 < x ∧ x < 3`` 是说存在一个介于2到3之间的实数。（我们将在 :numref:`conjunction_and_biimplication` 探讨合取符号。）证明这种语句的典型方式是给出一个实数并说明它具有语句指出的性质。我们可以用 ``5 / 2`` 输入2.5这个数，或者，当 Lean 无法从上下文推断出我们想输入实数时，用 ``(5 : ℝ) / 2`` 输入，它具有所需的性质，而 ``norm_num`` 策略可以证明它符合描述。

.. index:: use, tactics ; use

我们有一些方式可以把信息聚合在一起。给定一个以存在量词开头的目标，则 ``use`` 策略可用于提供对象，留下证明其属性的目标。
TEXT. -/
-- QUOTE:
example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
  use 5 / 2
  norm_num
-- QUOTE.

/- TEXT:
你不仅可以给 ``use`` 策略提供数据，还可以提供证明：
TEXT. -/
-- QUOTE:
example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
  have h1 : 2 < (5 : ℝ) / 2 := by norm_num
  have h2 : (5 : ℝ) / 2 < 3 := by norm_num
  use 5 / 2, h1, h2
-- QUOTE.

/- TEXT:
事实上， ``use`` 策略同样自动地尝试可用的假设。
TEXT. -/
-- QUOTE:
example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
  have h : 2 < (5 : ℝ) / 2 ∧ (5 : ℝ) / 2 < 3 := by norm_num
  use 5 / 2
-- QUOTE.

/- TEXT:
.. index:: anonymous constructor

或者，我们可以使用 Lean 的 **匿名构造子（anonymous constructor）** 符号来构造涉及存在量词的证明。
TEXT. -/
-- QUOTE:
example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
  have h : 2 < (5 : ℝ) / 2 ∧ (5 : ℝ) / 2 < 3 := by norm_num
  ⟨5 / 2, h⟩
-- QUOTE.

/- TEXT:
这里没有用 ``by`` ，因为这是证明项。左右尖括号，可以分别用 ``\<`` 和 ``\>`` 输入，告诉 Lean 使用任何对当前目标合适的构造方式把给定的数据组织起来。我们可以不在策略模式下使用这种符号：
TEXT. -/
-- QUOTE:
example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
  ⟨5 / 2, by norm_num⟩
-- QUOTE.

/- TEXT:
所以我们现在知道如何证明一个存在语句。但我们要如何 *使用* 它？如果我们知道存在一个具有特定性质的对象，我们就可以为任意一个对象命名并对其进行推理。例如， 回顾上一节的谓词 ``FnUb f a`` 和 ``FnLb f a`` ，它们分别是指 ``a`` 是 ``f`` 的一个上界或下界。我们可以使用存在量词说明 “ ``f`` 是有界的”，而无需指定它的界：
TEXT. -/
-- BOTH:
-- QUOTE:
def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a
-- QUOTE.

/- TEXT:
我们可以使用上一节的定理 ``FnUb_add`` 证明若 ``f`` 和 ``g`` 具有上界，则 ``fun x ↦ f x + g x`` 也有。
TEXT. -/
-- BOTH:
theorem fnUb_add {f g : ℝ → ℝ} {a b : ℝ} (hfa : FnUb f a) (hgb : FnUb g b) :
    FnUb (fun x ↦ f x + g x) (a + b) :=
  fun x ↦ add_le_add (hfa x) (hgb x)

section

-- QUOTE:
variable {f g : ℝ → ℝ}

-- EXAMPLES:
example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  rcases ubf with ⟨a, ubfa⟩
  rcases ubg with ⟨b, ubgb⟩
  use a + b
  apply fnUb_add ubfa ubgb
-- QUOTE.

/- TEXT:
.. index:: cases, tactics ; cases

``rcases`` 策略解包了存在量词中的信息。像 ``⟨a, ubfa⟩`` 这样长得像是一个匿名构造子的记号，称为 **模式（pattern）**，它们描述了我们在解包主参数时期望找到的信息。给出假设 ``ubf``, 即 ``f`` 存在上界，``rcases ubf with ⟨a, ubfa⟩`` 在上下文中添加一个新变量 ``a`` 作为上界，并添加假设 ``ubfa`` ，即该变量有给定的性质。这有点像 ``intro`` ，目标没有变化，但引入了新对象和新假设来证明目标。这是数学推理的一种常规方法：我们解包对象，其存在性被一些假设断言或蕴含，然后使用它论证其他一些东西的存在性。

试着使用这个方法构建下列命题。你可能用到上一节中的一些例子，所以可以给它们起些名字，就像我们对 ``fn_ub_add`` 做的那样，或者你也可以直接把那些论证插入到证明中。
TEXT. -/
-- QUOTE:
example (lbf : FnHasLb f) (lbg : FnHasLb g) : FnHasLb fun x ↦ f x + g x := by
  sorry

example {c : ℝ} (ubf : FnHasUb f) (h : c ≥ 0) : FnHasUb fun x ↦ c * f x := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (lbf : FnHasLb f) (lbg : FnHasLb g) : FnHasLb fun x ↦ f x + g x := by
  rcases lbf with ⟨a, lbfa⟩
  rcases lbg with ⟨b, lbgb⟩
  use a + b
  intro x
  exact add_le_add (lbfa x) (lbgb x)

example {c : ℝ} (ubf : FnHasUb f) (h : c ≥ 0) : FnHasUb fun x ↦ c * f x := by
  rcases ubf with ⟨a, ubfa⟩
  use c * a
  intro x
  exact mul_le_mul_of_nonneg_left (ubfa x) h

/- TEXT:
.. index:: rintro, tactics ; rintro, rcases, tactics ; rcases

``rcases`` 中的 "r" 表示 "recursive（递归）"，因为它允许我们使用任意复杂的模式解包嵌套数据。``rintro`` 策略是 ``intro`` 和 ``rcases`` 的组合：
TEXT. -/
-- QUOTE:
example : FnHasUb f → FnHasUb g → FnHasUb fun x ↦ f x + g x := by
  rintro ⟨a, ubfa⟩ ⟨b, ubgb⟩
  exact ⟨a + b, fnUb_add ubfa ubgb⟩
-- QUOTE.

/- TEXT:
事实上，Lean 也支持表达式和证明项中的模式匹配函数：
TEXT. -/
-- QUOTE:
example : FnHasUb f → FnHasUb g → FnHasUb fun x ↦ f x + g x :=
  fun ⟨a, ubfa⟩ ⟨b, ubgb⟩ ↦ ⟨a + b, fnUb_add ubfa ubgb⟩
-- QUOTE.

-- BOTH:
end

/- TEXT:
在假设中解包信息的任务非常重要，以至于 Lean 和 Mathlib 提供了多种方式实施。例如， ``obtain`` 策略提供提示性语法：
TEXT. -/
-- QUOTE:
example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  obtain ⟨a, ubfa⟩ := ubf
  obtain ⟨b, ubgb⟩ := ubg
  exact ⟨a + b, fnUb_add ubfa ubgb⟩
-- QUOTE.

/- TEXT:
将第一条 ``obtain`` 指令看作是将 ``ubf`` 的“内容”与给定的模式匹配，并将成分赋值给具名变量。``rcases`` 和 ``obtain`` 可以说是在 ``destruct`` 它们的参数，但有一点不同，``rcases`` 在完成后会清除上下文中的 ``ubf``, 而在 ``obtain`` 后它仍然存在。

Lean 还支持与其他函数式编程语言类似的语法：
TEXT. -/
-- QUOTE:
example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  cases ubf
  case intro a ubfa =>
    cases ubg
    case intro b ubgb =>
      exact ⟨a + b, fnUb_add ubfa ubgb⟩

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  cases ubf
  next a ubfa =>
    cases ubg
    next b ubgb =>
      exact ⟨a + b, fnUb_add ubfa ubgb⟩

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  match ubf, ubg with
    | ⟨a, ubfa⟩, ⟨b, ubgb⟩ =>
      exact ⟨a + b, fnUb_add ubfa ubgb⟩

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x :=
  match ubf, ubg with
    | ⟨a, ubfa⟩, ⟨b, ubgb⟩ =>
      ⟨a + b, fnUb_add ubfa ubgb⟩
-- QUOTE.

/- TEXT:
在第一个例子中，如果把光标放在 ``cases ubf`` 后面，就会看到该策略产生了一个目标，Lean 将其标记为 ``intro`` （所选的特定名称来自建立存在性语句证明的公理基元的内部名称）。然后， ``case`` 策略会命名各个组件。第二个例子也是类似的，只是使用了 ``next`` 而非 ``case`` 意味着可以避免提及 ``intro`` 。最后两个例子中的 ``match`` 一词强调了我们在这里做的是计算机科学家所说的“模式匹配”。请注意，第三个证明以 ``by`` 开头，之后的策略版 ``match`` 希望在箭头右侧有一个策略证明。最后一个例子是一个证明项，没有策略。

在本书其余部分，我们将坚持使用 ``rcases``, ``rintros`` 和 ``obtain`` ，作为使用存在量词的首选方式。但看看其他语法也没坏处，尤其是当你有机会与计算机科学家合作时。

为了展示 ``rcases`` 的一种使用方法，我们来证明一个经典的数学结果：若两个整数 ``x`` 和 ``y`` 可以分别写成两个平方数之和，那么它们的乘积 ``x * y`` 也可以。事实上，这个结论对任何交换环都是正确的，而不仅仅适用于整数环。在下一个例子中， ``rcases`` 同时解包了两个存在量词。然后，我们以列表形式向 ``use`` 语句提供将 ``x * y`` 表示为平方和所需的值，并使用 ``ring`` 来验证它们是否有效。
TEXT. -/
section

-- QUOTE:
variable {α : Type*} [CommRing α]

def SumOfSquares (x : α) :=
  ∃ a b, x = a ^ 2 + b ^ 2

theorem sumOfSquares_mul {x y : α} (sosx : SumOfSquares x) (sosy : SumOfSquares y) :
    SumOfSquares (x * y) := by
  rcases sosx with ⟨a, b, xeq⟩
  rcases sosy with ⟨c, d, yeq⟩
  rw [xeq, yeq]
  use a * c - b * d, a * d + b * c
  ring
-- QUOTE.

/- TEXT:
这个证明并未给出太多直觉洞见，现在我们展示证明思路。**高斯整数** 是形如 :math:`a + bi` 的数，其中 :math:`a` 和 :math:`b` 是整数，而 :math:`i = \sqrt{-1}` 。根据定义，高斯整数 :math:`a + bi` 的 *范数* 是 :math:`a^2 + b^2` 。所以高斯整数的范数是平方和，且任意平方和都可以这样表示。上述定理反映了一个事实，即高斯整数的乘积的范数等于范数的乘积：若 :math:`x` 是 :math:`a + bi` 的范数，且 :math:`y` 是 :math:`c + di` 的范数，则 :math:`xy` 是 :math:`(a + bi) (c + di)` 的范数。我们充满惊人注意力的证明说明了这样一个事实：最容易形式化的证明并不总是最透彻的。在 :numref:`section_building_the_gaussian_integers` 中，我们将为你介绍定义高斯整数的方法，并利用它们提供另一种证明。

在存在量词中解包等式，然后用它来重写目标中的表达式的模式经常出现，以至于 ``rcases`` 策略提供了一个缩写：如果使用关键字 ``rfl`` 代替新的标识符，``rcases`` 就会自动进行重写（这一技巧不适用于模式匹配的 lambda）。
TEXT. -/
-- QUOTE:
theorem sumOfSquares_mul' {x y : α} (sosx : SumOfSquares x) (sosy : SumOfSquares y) :
    SumOfSquares (x * y) := by
  rcases sosx with ⟨a, b, rfl⟩
  rcases sosy with ⟨c, d, rfl⟩
  use a * c - b * d, a * d + b * c
  ring
-- QUOTE.

end

/- TEXT:
与全称量词一样，存在量词也满地都是。例如，可除性隐含了一个“存在”语句。
TEXT. -/
-- BOTH:
section
variable {a b c : ℕ}

-- EXAMPLES:
-- QUOTE:
example (divab : a ∣ b) (divbc : b ∣ c) : a ∣ c := by
  rcases divab with ⟨d, beq⟩
  rcases divbc with ⟨e, ceq⟩
  rw [ceq, beq]
  use d * e; ring
-- QUOTE.

/- TEXT:
这再次为和 ``rfl`` 一起使用 ``rcases`` 提供了一个很好的配置。在上面的证明中试试看。感觉还不错！

接下来尝试证明下列定理：
TEXT. -/
-- QUOTE:
example (divab : a ∣ b) (divac : a ∣ c) : a ∣ b + c := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (divab : a ∣ b) (divbc : b ∣ c) : a ∣ c := by
  rcases divab with ⟨d, rfl⟩
  rcases divbc with ⟨e, rfl⟩
  use d * e; ring

example (divab : a ∣ b) (divac : a ∣ c) : a ∣ b + c := by
  rcases divab with ⟨d, rfl⟩
  rcases divac with ⟨e, rfl⟩
  use d + e; ring

-- BOTH:
end

/- TEXT:
.. index:: surjective function

另一个重要的例子是，若函数 :math:`f : \alpha \to \beta` 满足对值域 :math:`\beta` 中任意的 :math:`y`, 存在定义域 :math:`\alpha` 中的 :math:`x`, 使得 :math:`f(x) = y` ，那么我们称这个函数是 *满射* 。注意到这个语句既包含全称量词，也包含存在量词，这解释了为什么接下来的例子同时使用了 ``intro`` 和 ``use`` 。
TEXT. -/
-- BOTH:
section

open Function

-- EXAMPLES:
-- QUOTE:
example {c : ℝ} : Surjective fun x ↦ x + c := by
  intro x
  use x - c
  dsimp; ring
-- QUOTE.

/- TEXT:
试试这个，使用定理 ``mul_div_cancel₀`` ：
TEXT. -/
-- QUOTE:
example {c : ℝ} (h : c ≠ 0) : Surjective fun x ↦ c * x := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example {c : ℝ} (h : c ≠ 0) : Surjective fun x ↦ c * x := by
  intro x
  use x / c
  dsimp; rw [mul_div_cancel₀ _ h]

example {c : ℝ} (h : c ≠ 0) : Surjective fun x ↦ c * x := by
  intro x
  use x / c
  field_simp

/- TEXT:
.. index:: field_simp, tactics ; field_simp

技巧： ``field_simp`` 策略通常可以有效地去分母。它可以与 ``ring`` 策略结合使用。
TEXT. -/
-- QUOTE:
example (x y : ℝ) (h : x - y ≠ 0) : (x ^ 2 - y ^ 2) / (x - y) = x + y := by
  field_simp [h]
  ring
-- QUOTE.

/- TEXT:
下一个示例使用了满射性假设，将它应用于一个合适的值。你可以在任何表达式中使用 ``rcases`` ，而不仅仅是在假设中。
TEXT. -/
-- QUOTE:
example {f : ℝ → ℝ} (h : Surjective f) : ∃ x, f x ^ 2 = 4 := by
  rcases h 2 with ⟨x, hx⟩
  use x
  rw [hx]
  norm_num
-- QUOTE.

-- BOTH:
end

/- TEXT:
看看你能否用这些方法证明满射函数的复合是满射。
TEXT. -/
-- BOTH:
section
open Function
-- QUOTE:
variable {α : Type*} {β : Type*} {γ : Type*}
variable {g : β → γ} {f : α → β}

-- EXAMPLES:
example (surjg : Surjective g) (surjf : Surjective f) : Surjective fun x ↦ g (f x) := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (surjg : Surjective g) (surjf : Surjective f) : Surjective fun x ↦ g (f x) := by
  intro z
  rcases surjg z with ⟨y, rfl⟩
  rcases surjf y with ⟨x, rfl⟩
  use x

-- BOTH:
end
