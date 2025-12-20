-- BOTH:
import MIL.Common
import Mathlib.Topology.MetricSpace.Basic

/- TEXT:
.. _proving_facts_about_algebraic_structures:

证明关于代数结构的命题
----------------------------------------

.. index:: order relation, partial order

在 :numref:`proving_identities_in_algebraic_structures` 中，
我们看到许多关于实数的常见恒等式适用于更一般的代数结构类，比如交换环。
我们还有其他代数结构，例如，**偏序** 是一个具有二元关系的集合，该关系是自反的、传递的和反对称的，就像实数上的 ``≤`` 。
TEXT. -/
section
-- QUOTE:
variable {α : Type*} [PartialOrder α]
variable (x y z : α)

-- EXAMPLES:
#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)

-- QUOTE.

/- TEXT:
Mathlib 中习惯用希腊字母 ``α``、 ``β`` 和 ``γ`` （用 ``\a``、``\b`` 和 ``\g`` 输入）等等表示一般类型，使用 ``R`` 和 ``G`` 等来表示如环和群等特殊的代数结构。

对于任何偏序 ``≤``，还有一个 **严格偏序** ``<``，类似实数上的 ``<`` ，是去掉等于的小于等于。
TEXT. -/
-- QUOTE:
#check x < y
#check (lt_irrefl x : ¬ (x < x))
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
  lt_iff_le_and_ne
-- QUOTE.

end

/- TEXT:
在这个例子中，符号 ``∧`` 表示 “且”，符号 ``¬`` 表示 “非”，而 ``x ≠ y`` 是 ``¬ (x = y)`` 的缩写。
:numref:`第 %s 章 <logic>` 会讲到如何使用这些逻辑连接词来 **证明** ``<`` 具有所示的性质。

.. index:: lattice

一个 **格** 是给偏序添加运算符 ``⊓`` 和 ``⊔`` 的结构，
这些运算符类似于实数上的 ``min`` 和 ``max``，
称为 **最大下界** 和 **最小上界** （greatest lower bound, least upper bound） ，
用 ``\glb`` 和 ``\lub`` 输入：
TEXT. -/
-- BOTH:
section
-- QUOTE:
variable {α : Type*} [Lattice α]
variable (x y z : α)

-- EXAMPLES:
#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)
-- QUOTE.

/- TEXT:
这些符号通常也称为 **下确界** 和 **上确界** ，
在 Mathlib 的定理名称中被记为 ``inf`` 和 ``sup``。
与此同时它们也经常被称为 **meet** 和 **join** 。因此，如果你使用格，需要记住以下术语：

* ``⊓`` 是 **最大下界** 、 **下确界** 或 **meet** 。

* ``⊔`` 是 **最小上界** 、 **上确界** 或 **join** 。

一些格的实例包括：

* 任何全序上的 ``min`` 和 ``max``，例如带有 ``≤`` 的整数或实数

* 某个域的子集合的 ``∩`` ( ``\cap`` ) 和 ``∪`` ( ``\cup`` )，其中的序是 ``⊆`` ( ``\subseteq`` )

* 布尔真值的 ``∧`` 和 ``∨``，其中的序是如果 ``x`` 是假或 ``y`` 是真，则 ``x ≤ y``

* 自然数（或正自然数）上的 ``gcd`` 和 ``lcm``，其中的序是 ``∣``

* 向量空间的线性子空间的集合，其中最大下界由交集给出，最小上界由两个空间的和给出，序是包含关系

* 一个集合（或在 Lean 中，一个类型）上的拓扑的集合，其中两个拓扑的最大下界由它们的并集生成的拓扑给出，最小上界是它们的交集，并且排序是逆包含关系

你可以验证，与 ``min`` / ``max`` 和 ``gcd`` / ``lcm`` 一样，你可以仅使用刻画它们的公理以及 ``le_refl`` 和 ``le_trans`` 来证明下确界和上确界的交换律和结合律。
TEXT. -/

/- 这一段很突兀，先不放到正文里。
.. index:: trans, tactics ; trans

当看到目标 ``x ≤ z`` 时直接使用 ``apply le_trans`` 并不总是一个好主意，Lean 无法猜测我们想要使用哪个 ``y`` 作为中间元素。因此， ``apply le_trans`` 会产生三个看起来像 ``x ≤ ?a`` ， ``?a ≤ z`` 和 ``α`` 的目标，其中 ``?a`` （可能带有更复杂的自动生成名称）表示神秘未知的 ``y`` 。最后一个目标类型为 ``α`` ，是为了提供 ``y`` 的值。它在最后出现，因为 Lean 希望通过第一个目标 ``x ≤ ?a`` 的证明自动推断出它。为了避免这种不理想的情况，可以使用 ``calc`` 策略显式地提供 ``y`` 。或者，可以使用 ``trans`` 策略，该策略将 ``y`` 作为参数，并生成期望的目标 ``x ≤ y`` 和 ``y ≤ z`` 。最好的建议是通过直接提供完整的证明来避免此问题，例如 ``exact le_trans inf_le_left inf_le_right`` ，但这需要更多的规划。
-/
-- QUOTE:
example : x ⊓ y = y ⊓ x := by
  sorry

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  sorry

example : x ⊔ y = y ⊔ x := by
  sorry

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example : x ⊓ y = y ⊓ x := by
  apply le_antisymm
  repeat
    apply le_inf
    · apply inf_le_right
    apply inf_le_left

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  · apply le_inf
    · trans x ⊓ y
      apply inf_le_left
      apply inf_le_left
    apply le_inf
    · trans x ⊓ y
      apply inf_le_left
      apply inf_le_right
    apply inf_le_right
  apply le_inf
  · apply le_inf
    · apply inf_le_left
    trans y ⊓ z
    apply inf_le_right
    apply inf_le_left
  trans y ⊓ z
  apply inf_le_right
  apply inf_le_right

example : x ⊔ y = y ⊔ x := by
  apply le_antisymm
  repeat
    apply sup_le
    · apply le_sup_right
    apply le_sup_left

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  apply le_antisymm
  · apply sup_le
    · apply sup_le
      apply le_sup_left
      · trans y ⊔ z
        apply le_sup_left
        apply le_sup_right
    trans y ⊔ z
    apply le_sup_right
    apply le_sup_right
  apply sup_le
  · trans x ⊔ y
    apply le_sup_left
    apply le_sup_left
  apply sup_le
  · trans x ⊔ y
    apply le_sup_right
    apply le_sup_left
  apply le_sup_right

/- TEXT:
在 Mathlib 中它们分别叫 ``inf_comm`` 、 ``inf_assoc`` 、 ``sup_comm`` 和 ``sup_assoc`` 。

另一个很好的练习是仅使用这些公理证明 **吸收律** ：
TEXT. -/
-- QUOTE:
theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  sorry

theorem absorb2 : x ⊔ x ⊓ y = x := by
  sorry
-- QUOTE.

-- SOLUTIONS:
theorem absorb1αα : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  · apply inf_le_left
  apply le_inf
  · apply le_refl
  apply le_sup_left

theorem absorb2αα : x ⊔ x ⊓ y = x := by
  apply le_antisymm
  · apply sup_le
    · apply le_refl
    apply inf_le_left
  apply le_sup_left

-- BOTH:
end

/- TEXT:
在 Mathlib 中它们分别叫 ``inf_sup_self`` 和 ``sup_inf_self``.

格上附加条件 ``x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z)`` 和 ``x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z)`` 称为 **分配格（distributive lattice）** 。
TEXT. -/
-- BOTH:
section
-- QUOTE:
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left x y z : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right x y z : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left x y z : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right x y z : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
-- QUOTE.
end

/- TEXT:
使用 ``⊓`` 和 ``⊔`` 的交换律易证左右两个版本等价。有兴趣的话你可以构造一个不分配的格。现在的目标是尝试证明在任何格中，一个分配律可以推导出另一个分配律。
TEXT. -/
-- BOTH:
section
-- QUOTE:
variable {α : Type*} [Lattice α]
variable (a b c : α)

-- EXAMPLES:
example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  sorry

example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  rw [h, @inf_comm _ _ (a ⊔ b), absorb1, @inf_comm _ _ (a ⊔ b), h, ← sup_assoc, @inf_comm _ _ c a,
    absorb2, inf_comm]

example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  rw [h, @sup_comm _ _ (a ⊓ b), absorb2, @sup_comm _ _ (a ⊓ b), h, ← inf_assoc, @sup_comm _ _ c a,
    absorb1, sup_comm]

-- BOTH:
end

/- TEXT:
可以将结构公理组合成更大的结构。例如，**严格有序环** 是一个环上附加偏序，且满足环运算与序是兼容的：
TEXT. -/
-- BOTH:
section
-- QUOTE:
variable {R : Type*} [StrictOrderedRing R]
variable (a b c : R)

-- EXAMPLES:
#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)
-- QUOTE.

/- TEXT:
:numref:`第 %s 章 <logic>` 将从 ``mul_pos`` 和 ``<`` 的定义中得出以下定理：
TEXT. -/
-- QUOTE:
#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)
-- QUOTE.

/- TEXT:
下面是一个拓展练习，展示了任何有序环上的算术和序的常见引理。希望你仅使用环、偏序以及上面两个示例中列举的事实来证明它们（环可能并非交换，因此不能用 ``ring`` 策略）：
TEXT. -/
-- QUOTE:
example (h : a ≤ b) : 0 ≤ b - a := by
  sorry

example (h: 0 ≤ b - a) : a ≤ b := by
  sorry

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  sorry
-- QUOTE.

-- SOLUTIONS:
theorem aux1 (h : a ≤ b) : 0 ≤ b - a := by
  rw [← sub_self a, sub_eq_add_neg, sub_eq_add_neg, add_comm, add_comm b]
  apply add_le_add_left h

theorem aux2 (h : 0 ≤ b - a) : a ≤ b := by
  rw [← add_zero a, ← sub_add_cancel b a, add_comm (b - a)]
  apply add_le_add_left h

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  have h1 : 0 ≤ (b - a) * c := mul_nonneg (aux1 _ _ h) h'
  rw [sub_mul] at h1
  exact aux2 _ _ h1

-- BOTH:
end

/- TEXT:
.. index:: metric space

最后，**度量空间** 是配备了距离 ``dist x y`` 的集合，距离将任何一对元素映射到一个实数，满足以下公理：
TEXT. -/
-- BOTH:
section
-- QUOTE:
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

-- EXAMPLES:
#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)
-- QUOTE.

/- TEXT:
证明距离始终是非负的。你可能会用到 ``nonneg_of_mul_nonneg_left`` 。在 Mathlib 中这个定理被称为 ``dist_nonneg`` 。
TEXT. -/
-- QUOTE:
example (x y : X) : 0 ≤ dist x y := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (x y : X) : 0 ≤ dist x y :=by
  have : 0 ≤ dist x y + dist y x := by
    rw [← dist_self x]
    apply dist_triangle
  linarith [dist_comm x y]

-- BOTH:
end
