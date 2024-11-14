-- BOTH:
import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S03

/- TEXT:
.. _negation:

否定
--------

符号 ``¬`` （ ``\n`` , ``\neg``）表示否定，所以 ``¬ x < y`` 是说 ``x`` 不小于 ``y`` ， ``¬ x = y`` （或者，等价地， ``x ≠ y``）是说 ``x`` 不等于 ``y`` ，而 ``¬ ∃ z, x < z ∧ z < y`` 是说不存在 ``z`` 使其严格位于 ``x`` 和 ``y`` 之间。在 Lean 中，符号 ``¬ A`` 是 ``A → False`` 的缩写，你可以认为它表示 ``A`` 导出矛盾。聪明的你会发现，你可以通过引入假设 ``h : A`` 并证明 ``False`` 来证明 ``¬ A`` ，如果你有 ``h : ¬ A`` 和 ``h' : A`` ，那么把 ``h`` 应用于 ``h'`` 就产生 ``False``.

为了演示，考虑严格序的反自反律 ``lt_irrefl`` ，它是说对每个 ``a`` 我们有 ``¬ a < a`` 。反对称律 ``lt_asymm`` 是说我们有 ``a < b → ¬ b < a`` 。我们证明， ``lt_asymm`` 可从 ``lt_irrefl`` 推出。
TEXT. -/
-- BOTH:
section
variable (a b : ℝ)

-- EXAMPLES:
-- QUOTE:
example (h : a < b) : ¬b < a := by
  intro h'
  have : a < a := lt_trans h h'
  apply lt_irrefl a this
-- QUOTE.

/- TEXT:
.. index:: this, have, tactics ; have, from, tactics ; from

这个例子引入了两个新技巧。第一，当我们使用 ``have`` 而不提供名字时，Lean 使用名字 ``this`` 。因为这个证明太短，我们提供了精确证明项。但你真正需要注意的是这个证明中 ``intro`` 策略的结果，它留下目标 ``False`` ，还有，我们最终对 ``a < a`` 使用 ``lt_irrefl`` 证明了 ``False`` 。

这里是另一个例子，它使用上一节定义的谓词 ``FnHasUb`` ，也就是说一个函数有上界。
TEXT. -/
-- BOTH:
def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a

variable (f : ℝ → ℝ)

-- EXAMPLES:
-- QUOTE:
example (h : ∀ a, ∃ x, f x > a) : ¬FnHasUb f := by
  intro fnub
  rcases fnub with ⟨a, fnuba⟩
  rcases h a with ⟨x, hx⟩
  have : f x ≤ a := fnuba x
  linarith
-- QUOTE.

/- TEXT:
当目标可由语境中的线性等式和不等式得出时，使用 ``linarith`` 通常很方便。

类似地证明下列定理：
TEXT. -/
-- QUOTE:
example (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f :=
  sorry

example : ¬FnHasUb fun x ↦ x :=
  sorry
-- QUOTE.

-- SOLUTIONS:
example (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f := by
  rintro ⟨a, ha⟩
  rcases h a with ⟨x, hx⟩
  have := ha x
  linarith

example : ¬FnHasUb fun x ↦ x := by
  rintro ⟨a, ha⟩
  have : a + 1 ≤ a := ha (a + 1)
  linarith

/- TEXT:
Mathlib 提供了一些关于序和否定的定理：
TEXT. -/
-- QUOTE:
#check (not_le_of_gt : a > b → ¬a ≤ b)
#check (not_lt_of_ge : a ≥ b → ¬a < b)
#check (lt_of_not_ge : ¬a ≥ b → a < b)
#check (le_of_not_gt : ¬a > b → a ≤ b)
-- QUOTE.

/- TEXT:
回顾谓词 ``Monotone f`` ，它表示 ``f`` 是非递减的。用刚才列举的一些定理证明下面的内容：
TEXT. -/
-- QUOTE:
example (h : Monotone f) (h' : f a < f b) : a < b := by
  sorry

example (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (h : Monotone f) (h' : f a < f b) : a < b := by
  apply lt_of_not_ge
  intro h''
  apply absurd h'
  apply not_lt_of_ge (h h'')

example (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
  intro h''
  apply absurd h'
  apply not_lt_of_ge
  apply h'' h

/- TEXT:
我们可以说明，如果我们把 ``<`` 换成 ``≤`` ，则上一段的第一个例子无法被证明。我们可以通过给出反例证明一个全称量词语句的否定。接下来完成证明：
TEXT. -/
-- QUOTE:
example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
  intro h
  let f := fun x : ℝ ↦ (0 : ℝ)
  have monof : Monotone f := by sorry
  have h' : f 1 ≤ f 0 := le_refl _
  sorry
-- QUOTE.

-- SOLUTIONS:
example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
  intro h
  let f := fun x : ℝ ↦ (0 : ℝ)
  have monof : Monotone f := by
    intro a b leab
    rfl
  have h' : f 1 ≤ f 0 := le_refl _
  have : (1 : ℝ) ≤ 0 := h monof h'
  linarith

/- TEXT:
.. index:: let, tactics ; let

这个例子引入了 ``let`` 策略，它向语境添加了一个 **局部定义**。如果你把光标移动到目标窗口的 ``let`` 命令后面的地方，你会看到 ``f : ℝ → ℝ := fun x ↦ 0`` 已经被添加到语境中。当必须展开定义时， Lean会展开。特别地，当我们使用 ``le_refl`` 证明 ``f 1 ≤ f 0`` 时，Lean 把 ``f 1`` 和 ``f 0`` 约化为 ``0``.

使用 ``le_of_not_gt`` 证明下列内容：
TEXT. -/
-- QUOTE:
example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  apply le_of_not_gt
  intro h'
  linarith [h _ h']

-- BOTH:
end

/- TEXT:
我们刚才所做的许多证明都隐含着这样一个事实：如果 ``P`` 是任何属性，说没有任何事物具有 ``P`` 属性就等于说一切事物都不具有 ``P`` 属性，而说并非所有东西都具有 ``P`` 属性等同于说某些东西不具备 ``P`` 属性。换句话说，以下四个推理都是有效的（但其中有一个无法使用我们目前已讲解的内容证明）：
TEXT. -/
-- BOTH:
section
-- QUOTE:
variable {α : Type*} (P : α → Prop) (Q : Prop)

-- EXAMPLES:
example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
  sorry

example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  sorry

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  sorry

example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
  intro x Px
  apply h
  use x

example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  rintro ⟨x, Px⟩
  exact h x Px

example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  intro h'
  rcases h with ⟨x, nPx⟩
  apply nPx
  apply h'

/- TEXT:
第一、二、四个可以使用你已经学到的方法直接证明。鼓励你尝试。然而，第三个更为困难，因为它是从一个对象的不存在可以得出矛盾的这一事实中得出结论，认为该对象是存在的。这是 **经典** 数学推理的一个实例。我们可以像下面这样使用反证法证明第三个结果。
TEXT. -/
-- QUOTE:
example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  apply h
  intro x
  show P x
  by_contra h''
  exact h' ⟨x, h''⟩
-- QUOTE.

/- TEXT:
.. index:: by_contra, tactics ; by_contra and by_contradiction,

确保你搞懂了示例。 ``by_contra`` 策略允许我们通过假定 ``¬ Q`` 推出矛盾来证明目标 ``Q`` 。事实上，它等价于使用等价关系 ``not_not : ¬ ¬ Q ↔ Q`` 。确认一下你可以使用 ``by_contra`` 证明这个等价的正方向，而反方向可从常规的否定法则得出。
TEXT. -/
-- QUOTE:
example (h : ¬¬Q) : Q := by
  sorry

example (h : Q) : ¬¬Q := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (h : ¬¬Q) : Q := by
  by_contra h'
  exact h h'

example (h : Q) : ¬¬Q := by
  intro h'
  exact h' h

-- BOTH:
end

/- TEXT:
用反证法证明下面的内容，它是我们在上面证明的一个蕴涵的相反方向。（提示：先使用 ``intro`` ）
TEXT. -/
-- BOTH:
section
variable (f : ℝ → ℝ)

-- EXAMPLES:
-- QUOTE:
example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  intro a
  by_contra h'
  apply h
  use a
  intro x
  apply le_of_not_gt
  intro h''
  apply h'
  use x

/- TEXT:
.. index:: push_neg, tactics ; push_neg

处理前面带有否定词的复合语句通常很无趣，通常我们希望会把否定词放进里面。好消息，Mathlib 提供了 ``push_neg`` 策略来找到否定词在里面的等价命题。命令 ``push_neg at h`` 重述假设 ``h`` 。
TEXT. -/
-- QUOTE:
example (h : ¬∀ a, ∃ x, f x > a) : FnHasUb f := by
  push_neg at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  dsimp only [FnHasUb, FnUb] at h
  push_neg at h
  exact h
-- QUOTE.

/- TEXT:
在第二个例子中，我们可以使用 ``dsimp`` 展开 ``FnHasUb`` 和 ``FnUb`` 的定义。（我们需要使用 ``dsimp`` 而不是 ``rw`` 来展开 ``FnUb``, 因为它出现在量词的辖域中。）在上面的例子中，你可以验证对于 ``¬∃ x, P x`` 和 ``¬∀ x, P x`` ， ``push_neg`` 策略做了我们期望的事情。即使不知道如何处理合取符号，你也应该能使用 ``push_neg`` 证明如下定理：
TEXT. -/
-- QUOTE:
example (h : ¬Monotone f) : ∃ x y, x ≤ y ∧ f y < f x := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (h : ¬Monotone f) : ∃ x y, x ≤ y ∧ f y < f x := by
  rw [Monotone] at h
  push_neg  at h
  exact h

/- TEXT:
.. index:: contrapose, tactics ; contrapose

Mathlib 还有一个策略 ``contrapose`` ，它把目标 ``A → B`` 转化为 ``¬B → ¬A`` 。类似地，给定从假设 ``h : A`` 证明 ``B`` 的目标，
``contrapose h`` 会给你留下从假设 ``¬B`` 证明 ``¬A`` 的目标。使用 ``contrapose!`` 将在 ``contrapose`` 之外对当前目标（事后假设）应用 ``push_neg`` 。
TEXT. -/
-- QUOTE:
example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  contrapose! h
  exact h

example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 := by
  contrapose! h
  use x / 2
  constructor <;> linarith
-- QUOTE.

-- BOTH:
end

/- TEXT:
下一节解释 ``constructor`` 命令及其后分号的使用。

我们以 *爆炸原理* （ex falso）结束本节，它是说从自相矛盾可以得出任何命题。在 Lean 中，它用 ``False.elim`` 表示，它对于任何命题 ``P`` 确认了 ``False → P`` 。这似乎是一个奇怪的原理，但它经常出现。我们经常通过分情况来证明定理，有时我们可以证明其中一种情况是矛盾的。在这种情况下，我们需要断言矛盾确证了目标，这样我们就可以继续下一个目标了。（在 :numref:`disjunction` 中，我们将看到分情况讨论的实例。）

.. index:: exfalso, contradiction, absurd, tactics ; exfalso, tactics ; contradiction

Lean 提供了多种在出现矛盾时关闭目标的方法。
TEXT. -/
section
variable (a : ℕ)

-- QUOTE:
example (h : 0 < 0) : a > 37 := by
  exfalso
  apply lt_irrefl 0 h

example (h : 0 < 0) : a > 37 :=
  absurd h (lt_irrefl 0)

example (h : 0 < 0) : a > 37 := by
  have h' : ¬0 < 0 := lt_irrefl 0
  contradiction
-- QUOTE.

end

/- TEXT:
``exfalso`` 策略把当前的目标替换为证明 ``False`` 的目标。给定 ``h : P`` 和 ``h' : ¬ P`` ，项 ``absurd h h'`` 可证明任何命题。最后， ``contradiction`` 策略尝试通过在假设中找到矛盾，例如一对形如 ``h : P`` 和 ``h' : ¬ P`` 的假设来关闭目标。另外本例也可以用 ``linarith`` 。
TEXT. -/
