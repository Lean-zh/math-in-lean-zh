import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import MIL.Common

/- TEXT:
.. _section_building_the_gaussian_integers:

构建高斯整数
------------------------------

现在我们将通过构建一个重要的数学对象—— **高斯整数** ，来说明在 Lean 中代数层次结构的使用，并证明它是欧几里得域。换句话说，按照我们一直在使用的术语，我们将定义高斯整数，并证明它们是欧几里得域结构的一个实例。

在普通的数学术语中，高斯整数集 :math:`\Bbb{Z}[i]` 是复数集 :math:`\{ a + b i \mid a, b \in \Bbb{Z}\}`。但我们的目标不是将其定义为复数集的一个子集，而是将其定义为一种独立的数据类型。为此，我们将高斯整数表示为一对整数，分别视为其 **实部** 和 **虚部** 。
BOTH: -/
-- QUOTE:
@[ext]
structure GaussInt where
  re : ℤ
  im : ℤ
-- QUOTE.

/- TEXT:
我们首先证明高斯整数具有环的结构，其中 ``0`` 定义为 ``⟨0, 0⟩`` ， ``1`` 定义为 ``⟨1, 0⟩`` ，加法按点定义。为了确定乘法的定义，记住我们希望由 ``⟨0, 1⟩`` 表示的元素 :math:`i` 是 :math:`-1` 的平方根。因此，我们希望

.. math::

   (a + bi) (c + di) & = ac + bci + adi + bd i^2 \\
     & = (ac - bd) + (bc + ad)i.

这解释了下面对 ``Mul`` 的定义。
BOTH: -/
namespace GaussInt

-- QUOTE:
instance : Zero GaussInt :=
  ⟨⟨0, 0⟩⟩

instance : One GaussInt :=
  ⟨⟨1, 0⟩⟩

instance : Add GaussInt :=
  ⟨fun x y ↦ ⟨x.re + y.re, x.im + y.im⟩⟩

instance : Neg GaussInt :=
  ⟨fun x ↦ ⟨-x.re, -x.im⟩⟩

instance : Mul GaussInt :=
  ⟨fun x y ↦ ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re⟩⟩
-- QUOTE.

/- TEXT:
正如在 :numref:`section_structures` 中所提到的，将与某种数据类型相关的所有定义放在同名的命名空间中是个好主意。因此，在与本章相关的 Lean 文件中，这些定义是在 ``GaussInt`` 命名空间中进行的。
请注意，这里我们直接定义了符号 ``0`` 、 ``1`` 、 ``+`` 、 ``-`` 和 ``*`` 的解释，而不是将它们命名为 ``GaussInt.zero`` 之类的名称并将其分配给这些名称。通常，为定义提供一个明确的名称很有用，例如，用于与 ``simp`` 和 ``rewrite`` 一起使用。
BOTH: -/
-- QUOTE:
theorem zero_def : (0 : GaussInt) = ⟨0, 0⟩ :=
  rfl

theorem one_def : (1 : GaussInt) = ⟨1, 0⟩ :=
  rfl

theorem add_def (x y : GaussInt) : x + y = ⟨x.re + y.re, x.im + y.im⟩ :=
  rfl

theorem neg_def (x : GaussInt) : -x = ⟨-x.re, -x.im⟩ :=
  rfl

theorem mul_def (x y : GaussInt) :
    x * y = ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re⟩ :=
  rfl
-- QUOTE.

/- TEXT:
对计算实部和虚部的规则进行命名，并将其声明给简化器，这也是很有用的。
BOTH: -/
-- QUOTE:
@[simp]
theorem zero_re : (0 : GaussInt).re = 0 :=
  rfl

@[simp]
theorem zero_im : (0 : GaussInt).im = 0 :=
  rfl

@[simp]
theorem one_re : (1 : GaussInt).re = 1 :=
  rfl

@[simp]
theorem one_im : (1 : GaussInt).im = 0 :=
  rfl

@[simp]
theorem add_re (x y : GaussInt) : (x + y).re = x.re + y.re :=
  rfl

@[simp]
theorem add_im (x y : GaussInt) : (x + y).im = x.im + y.im :=
  rfl

@[simp]
theorem neg_re (x : GaussInt) : (-x).re = -x.re :=
  rfl

@[simp]
theorem neg_im (x : GaussInt) : (-x).im = -x.im :=
  rfl

@[simp]
theorem mul_re (x y : GaussInt) : (x * y).re = x.re * y.re - x.im * y.im :=
  rfl

@[simp]
theorem mul_im (x y : GaussInt) : (x * y).im = x.re * y.im + x.im * y.re :=
  rfl
-- QUOTE.

/- TEXT:
现在令人惊讶地容易证明高斯整数是交换环的一个实例。我们正在很好地利用结构概念。每个特定的高斯整数都是 ``GaussInt`` 结构的一个实例，而 ``GaussInt`` 类型本身，连同相关操作，则是 ``CommRing`` 结构的一个实例。 ``CommRing`` 结构反过来又扩展了符号结构 ``Zero`` 、 ``One`` 、 ``Add`` 、 ``Neg`` 和 ``Mul`` 。

如果您输入 ``instance : CommRing GaussInt := _`` ，点击 VS Code 中出现的灯泡图标，然后让 Lean 自动填充结构定义的框架，您会看到大量的条目。然而，跳转到结构的定义会发现，其中许多字段都有默认定义，Lean 会自动为您填充。下面的定义中列出了关键的几个。

如果您输入 ``instance : CommRing GaussInt := _`` ，点击 VS Code 中出现的灯泡图标，然后让 Lean 填充结构定义的骨架，您会看到令人望而生畏的条目数量。然而，跳转到该结构的定义后会发现，许多字段都有默认定义，Lean 会自动为您填充。以下定义中展示的是其中关键的部分。 ``nsmul`` 和 ``zsmul`` 是一个特殊情况，暂时可以忽略，它们将在下一章中解释。在每种情况下，相关的恒等式都是通过展开定义、使用 ``ext`` 策略将恒等式简化为其实部和虚部、进行简化，并在必要时在整数中执行相关的环计算来证明的。需要注意的是，我们本可以轻松避免重复所有这些代码，但这并不是当前讨论的主题。
BOTH: -/
-- QUOTE:
instance instCommRing : CommRing GaussInt where
  zero := 0
  one := 1
  add := (· + ·)
  neg x := -x
  mul := (· * ·)
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc := by
    intros
    ext <;> simp <;> ring
  zero_add := by
    intro
    ext <;> simp
  add_zero := by
    intro
    ext <;> simp
  neg_add_cancel := by
    intro
    ext <;> simp
  add_comm := by
    intros
    ext <;> simp <;> ring
  mul_assoc := by
    intros
    ext <;> simp <;> ring
  one_mul := by
    intro
    ext <;> simp
  mul_one := by
    intro
    ext <;> simp
  left_distrib := by
    intros
    ext <;> simp <;> ring
  right_distrib := by
    intros
    ext <;> simp <;> ring
  mul_comm := by
    intros
    ext <;> simp <;> ring
  zero_mul := by
    intros
    ext <;> simp
  mul_zero := by
    intros
    ext <;> simp
-- QUOTE.

@[simp]
theorem sub_re (x y : GaussInt) : (x - y).re = x.re - y.re :=
  rfl

@[simp]
theorem sub_im (x y : GaussInt) : (x - y).im = x.im - y.im :=
  rfl

/- TEXT:
Lean 的库将具有至少两个不同元素的类型定义为 **非平凡** 类型。在环的上下文中，这等同于说零不等于一。由于一些常见的定理依赖于这一事实，我们不妨现在就证明它。
BOTH: -/
-- QUOTE:
instance : Nontrivial GaussInt := by
  use 0, 1
  rw [Ne, GaussInt.ext_iff]
  simp
-- QUOTE.

end GaussInt

/- TEXT:
我们现在将证明高斯整数具有一个重要的额外性质。一个 **欧几里得整环（Euclidean domain）** 是一个环 :math:`R`，配备了一个 **范数** 函数 :math:`N : R \to \mathbb{N}`，满足以下两个性质：

-对于 :math:`R` 中的任意 :math:`a` 和非零 :math:`b`，存在 :math:`R` 中的 :math:`q` 和 :math:`r`，使得 :math:`a = bq + r`，并且要么 :math:`r = 0`，要么 :math:`N(r) < N(b)`。
-对于任意 :math:`a` 和非零 :math:`b`，:math:`N(a) \le N(ab)`。
整数环 :math:`\Bbb{Z}` 与范数 :math:`N(a) = |a|` 是欧几里得整环的一个典型例子。在这种情况下，我们可以将 :math:`q` 取为 :math:`a` 除以 :math:`b` 的整数除法结果，并将 :math:`r` 取为余数。这些函数在 Lean 中定义，并满足以下性质：
EXAMPLES: -/
-- QUOTE:
example (a b : ℤ) : a = b * (a / b) + a % b :=
  Eq.symm (Int.ediv_add_emod a b)

example (a b : ℤ) : b ≠ 0 → 0 ≤ a % b :=
  Int.emod_nonneg a

example (a b : ℤ) : b ≠ 0 → a % b < |b| :=
  Int.emod_lt a
-- QUOTE.

/- TEXT:
在任意环中，若一个元素 :math:`a` 能整除 1，则称其为 **单位元** 。若一个非零元素 :math:`a` 不能写成 :math:`a = bc` 的形式，其中 :math:`b` 和 :math:`c` 均不是单位元，则称其为 **不可约元** 。在整数环中，每个不可约元 :math:`a` 都是 **素元** ，也就是说，每当 :math:`a` 能整除乘积 :math:`bc` 时，它就能整除 :math:`b` 或 :math:`c` 。但是
在其他环中，这一性质可能会失效。在环 :math:`\Bbb{Z}[\sqrt{-5}]` 中，我们有

.. math::

  6 = 2 \cdot 3 = (1 + \sqrt{-5})(1 - \sqrt{-5}),

并且元素 :math:`2` 、 :math:`3` 、 :math:`1 + \sqrt{-5}` 以及 :math:`1 - \sqrt{-5}` 都是不可约的，但它们不是素元。例如， :math:`2` 能整除乘积 :math:`(1 + \sqrt{-5})(1 - \sqrt{-5})` ，但它不能整除这两个因数中的任何一个。特别地，我们不再具有唯一分解性：数字 :math:`6` 可以用不止一种方式分解为不可约元素。

相比之下，每个欧几里得域都是唯一分解域，这意味着每个不可约元素都是素元。
欧几里得域的公理意味着可以将任何非零元素表示为不可约元素的有限乘积。它们还意味着可以使用欧几里得算法找到任意两个非零元素 ``a`` 和 ``b`` 的最大公约数，即能被任何其他公因数整除的元素。这反过来又意味着，除了乘以单位元素外，分解为不可约元素是唯一的。

我们现在证明高斯整数是一个欧几里得域，其范数定义为 :math:`N(a + bi) = (a + bi)(a - bi) = a^2 + b^2` 。高斯整数 :math:`a - bi` 被称为 :math:`a + bi` 的 **共轭** 。不难验证，对于任何复数 :math:`x` 和 :math:`y` ，我们都有 :math:`N(xy) = N(x)N(y)` 。

要证明这个范数的定义能使高斯整数构成欧几里得域，只有第一个性质具有挑战性。假设我们想写成 :math:`a + bi = (c + di) q + r` 的形式，其中 :math:`q` 和 :math:`r` 是合适的数。将 :math:`a + bi` 和 :math:`c + di` 视为复数，进行除法运算。

.. math::

  \frac{a + bi}{c + di} = \frac{(a + bi)(c - di)}{(c + di)(c-di)} =
    \frac{ac + bd}{c^2 + d^2} + \frac{bc -ad}{c^2+d^2} i.

实部和虚部可能不是整数，但我们可将其四舍五入到最接近的整数 :math:`u` 和 :math:`v` 。然后我们可以将右边表示为 :math:`(u + vi) + (u' + v'i)` ，其中 :math:`u' + v'i` 是剩余的部分。请注意，我们有 :math:`|u'| \le 1/2` 和 :math:`|v'| \le 1/2` ，因此

.. math::

  N(u' + v' i) = (u')^2 + (v')^2 \le 1/4 + 1/4 \le 1/2.

乘以 :math:`c + di`，我们有

.. math::

  a + bi = (c + di) (u + vi) + (c + di) (u' + v'i).

设 :math:`q = u + vi` 以及 :math:`r = (c + di) (u' + v'i)` ，则有
:math:`a + bi = (c + di) q + r` ，我们只需对 :math:`N(r)` 进行限制：

.. math::

  N(r) = N(c + di)N(u' + v'i) \le N(c + di) \cdot 1/2 < N(c + di).

我们刚刚进行的论证需要将高斯整数视为复数的一个子集。因此，在 Lean 中对其进行形式化的一种选择是将高斯整数嵌入到复数中，将整数嵌入到高斯整数中，定义从实数到整数的舍入函数，并且要非常小心地在这些数系之间进行适当的转换。
实际上，这正是 Mathlib 中所采用的方法，其中高斯整数本身是作为 **二次整数** 环的一个特例来构造的。
请参阅文件 `GaussianInt.lean
<https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/NumberTheory/Zsqrtd/GaussianInt.lean>`_.

在这里，我们将进行一个完全在整数范围内进行的论证。
这说明了在将数学形式化时人们通常面临的一种选择。
当一个论证需要库中尚未包含的概念或工具时，人们有两个选择：要么形式化所需的这些概念或工具，要么调整论证以利用已有的概念和工具。
从长远来看，当结果可以在其他情境中使用时，第一个选择通常是对时间的良好投资。
然而，从实际角度来看，有时寻找一个更基础的证明会更有效。

整数的常规商余定理指出，对于任意整数 :math:`a` 和非零整数 :math:`b`，都存在整数 :math:`q` 和 :math:`r` 使得 :math:`a = b q + r` 且 :math:`0 \le r < b`。这里我们将使用以下变体，即存在整数 :math:`q'` 和 :math:`r'` 使得 :math:`a = b q' + r'` 且 :math:`|r'| \le b/2`。您可以验证，如果第一个陈述中的 :math:`r` 满足 :math:`r \le b/2`，则可以取 :math:`q' = q` 和 :math:`r' = r`，否则可以取 :math:`q' = q + 1` 和 :math:`r' = r - b`。我们感谢 Heather Macbeth 提出以下更优雅的方法，该方法避免了按情况定义。我们只需在除法前将 ``b / 2`` 加到 ``a`` 上，然后从余数中减去它。
BOTH: -/
namespace Int

-- QUOTE:
def div' (a b : ℤ) :=
  (a + b / 2) / b

def mod' (a b : ℤ) :=
  (a + b / 2) % b - b / 2

theorem div'_add_mod' (a b : ℤ) : b * div' a b + mod' a b = a := by
  rw [div', mod']
  linarith [Int.ediv_add_emod (a + b / 2) b]

theorem abs_mod'_le (a b : ℤ) (h : 0 < b) : |mod' a b| ≤ b / 2 := by
  rw [mod', abs_le]
  constructor
  · linarith [Int.emod_nonneg (a + b / 2) h.ne']
  have := Int.emod_lt_of_pos (a + b / 2) h
  have := Int.ediv_add_emod b 2
  have := Int.emod_lt_of_pos b zero_lt_two
  linarith
-- QUOTE.

/- TEXT:
请注意我们老朋友 ``linarith`` 的使用。我们还需要用 ``div'`` 来表示 ``mod'`` 。
BOTH: -/
-- QUOTE:
theorem mod'_eq (a b : ℤ) : mod' a b = a - b * div' a b := by linarith [div'_add_mod' a b]
-- QUOTE.

end Int

/- TEXT:
我们将使用这样一个事实，即 :math:`x^2 + y^2` 等于零当且仅当 :math:`x` 和 :math:`y` 都为零。作为练习，我们要求您证明在任何有序环中都成立。
SOLUTIONS: -/
private theorem aux {α : Type*} [LinearOrderedRing α] {x y : α} (h : x ^ 2 + y ^ 2 = 0) : x = 0 :=
  haveI h' : x ^ 2 = 0 := by
    apply le_antisymm _ (sq_nonneg x)
    rw [← h]
    apply le_add_of_nonneg_right (sq_nonneg y)
  pow_eq_zero h'

-- QUOTE:
-- BOTH:
theorem sq_add_sq_eq_zero {α : Type*} [LinearOrderedRing α] (x y : α) :
    x ^ 2 + y ^ 2 = 0 ↔ x = 0 ∧ y = 0 := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  constructor
  · intro h
    constructor
    · exact aux h
    rw [add_comm] at h
    exact aux h
  rintro ⟨rfl, rfl⟩
  norm_num
-- QUOTE.

-- BOTH:
/- TEXT:
我们将本节中剩余的所有定义和定理都放在 ``GaussInt`` 命名空间中。
首先，我们定义 ``norm`` 函数，并请您证明其部分性质。
这些证明都很简短。
BOTH: -/
namespace GaussInt

-- QUOTE:
def norm (x : GaussInt) :=
  x.re ^ 2 + x.im ^ 2

@[simp]
theorem norm_nonneg (x : GaussInt) : 0 ≤ norm x := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  apply add_nonneg <;>
  apply sq_nonneg

-- BOTH:
theorem norm_eq_zero (x : GaussInt) : norm x = 0 ↔ x = 0 := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  rw [norm, sq_add_sq_eq_zero, GaussInt.ext_iff]
  rfl

-- BOTH:
theorem norm_pos (x : GaussInt) : 0 < norm x ↔ x ≠ 0 := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  rw [lt_iff_le_and_ne, ne_comm, Ne, norm_eq_zero]
  simp [norm_nonneg]

-- BOTH:
theorem norm_mul (x y : GaussInt) : norm (x * y) = norm x * norm y := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  simp [norm]
  ring

-- BOTH:
-- QUOTE.
/- TEXT:
接下来我们定义共轭函数：
BOTH: -/
-- QUOTE:
def conj (x : GaussInt) : GaussInt :=
  ⟨x.re, -x.im⟩

@[simp]
theorem conj_re (x : GaussInt) : (conj x).re = x.re :=
  rfl

@[simp]
theorem conj_im (x : GaussInt) : (conj x).im = -x.im :=
  rfl

theorem norm_conj (x : GaussInt) : norm (conj x) = norm x := by simp [norm]
-- QUOTE.

/- TEXT:
最后，我们为高斯整数定义除法运算，记作 ``x / y`` ，将复数商四舍五入到最近的高斯整数。为此我们使用自定义的 ``Int.div'`` 。
正如我们上面计算的那样，如果 ``x`` 是 :math:`a + bi`，而 ``y`` 是 :math:`c + di`，那么 ``x / y`` 的实部和虚部分别是如下式子最近的整数

.. math::

  \frac{ac + bd}{c^2 + d^2} \quad \text{和} \quad \frac{bc -ad}{c^2+d^2},

这里分子是 :math:`(a + bi) (c - di)` 的实部和虚部，而分母都等于 :math:`c + di` 的范数。
BOTH: -/
-- QUOTE:
instance : Div GaussInt :=
  ⟨fun x y ↦ ⟨Int.div' (x * conj y).re (norm y), Int.div' (x * conj y).im (norm y)⟩⟩
-- QUOTE.

/- TEXT:
定义了 ``x / y`` 之后，我们定义 ``x % y`` 为余数，即 ``x - (x / y) * y`` 。同样地，我们将这些定义记录在定理 ``div_def`` 和 ``mod_def`` 中，以便使用 ``simp`` 和 ``rewrite`` 。
BOTH: -/
-- QUOTE:
instance : Mod GaussInt :=
  ⟨fun x y ↦ x - y * (x / y)⟩

theorem div_def (x y : GaussInt) :
    x / y = ⟨Int.div' (x * conj y).re (norm y), Int.div' (x * conj y).im (norm y)⟩ :=
  rfl

theorem mod_def (x y : GaussInt) : x % y = x - y * (x / y) :=
  rfl
-- QUOTE.

/- TEXT:
这些定义立即得出对于每个 ``x`` 和 ``y`` 都有 ``x = y * (x / y) + x % y`` ，所以我们需要做的就是证明当 ``y`` 不为零时， ``x % y`` 的范数小于 ``y`` 的范数。

我们刚刚将 ``x / y`` 的实部和虚部分别定义为 ``div' (x * conj y).re (norm y)`` and ``div' (x * conj y).im (norm y)`` 。
计算得出，我们有

 ``(x % y) * conj y = (x - x / y * y) * conj y = x * conj y - x / y * (y * conj y)``

右侧实部和虚部恰好为 ``mod' (x * conj y).re (norm y)`` 和 ``mod' (x * conj y).im (norm y)`` 。
根据 ``div'`` 和 ``mod'`` 的性质，可以保证它们都小于或等于 ``norm y / 2`` 。
因此我们有

 ``norm ((x % y) * conj y) ≤ (norm y / 2)^2 + (norm y / 2)^2 ≤ (norm y / 2) * norm y`` .

另一方面，我们有

 ``norm ((x % y) * conj y) = norm (x % y) * norm (conj y) = norm (x % y) * norm y`` .

两边同时除以 ``norm y`` ，我们得到 ``norm（x % y）≤（norm y）/ 2 < norm y`` ，如所要求的那样。

这个杂乱的计算将在接下来的证明中进行。我们鼓励您仔细查看细节，看看能否找到更简洁的论证方法。
BOTH: -/
-- QUOTE:
theorem norm_mod_lt (x : GaussInt) {y : GaussInt} (hy : y ≠ 0) :
    (x % y).norm < y.norm := by
  have norm_y_pos : 0 < norm y := by rwa [norm_pos]
  have H1 : x % y * conj y = ⟨Int.mod' (x * conj y).re (norm y), Int.mod' (x * conj y).im (norm y)⟩
  · ext <;> simp [Int.mod'_eq, mod_def, div_def, norm] <;> ring
  have H2 : norm (x % y) * norm y ≤ norm y / 2 * norm y
  · calc
      norm (x % y) * norm y = norm (x % y * conj y) := by simp only [norm_mul, norm_conj]
      _ = |Int.mod' (x.re * y.re + x.im * y.im) (norm y)| ^ 2
          + |Int.mod' (-(x.re * y.im) + x.im * y.re) (norm y)| ^ 2 := by simp [H1, norm, sq_abs]
      _ ≤ (y.norm / 2) ^ 2 + (y.norm / 2) ^ 2 := by gcongr <;> apply Int.abs_mod'_le _ _ norm_y_pos
      _ = norm y / 2 * (norm y / 2 * 2) := by ring
      _ ≤ norm y / 2 * norm y := by gcongr; apply Int.ediv_mul_le; norm_num
  calc norm (x % y) ≤ norm y / 2 := le_of_mul_le_mul_right H2 norm_y_pos
    _ < norm y := by
        apply Int.ediv_lt_of_lt_mul
        · norm_num
        · linarith
-- QUOTE.

/- TEXT:
我们即将完成。我们的 ``norm`` 函数将高斯整数映射到非负整数。我们需要一个将高斯整数映射到自然数的函数，我们通过将 ``norm`` 与将整数映射到自然数的函数 ``Int.natAbs`` 组合来获得它。
接下来的两个引理中的第一个确立了将范数映射到自然数然后再映射回整数不会改变其值。
第二个引理重新表述了范数递减这一事实。
BOTH: -/
-- QUOTE:
theorem coe_natAbs_norm (x : GaussInt) : (x.norm.natAbs : ℤ) = x.norm :=
  Int.natAbs_of_nonneg (norm_nonneg _)

theorem natAbs_norm_mod_lt (x y : GaussInt) (hy : y ≠ 0) :
    (x % y).norm.natAbs < y.norm.natAbs := by
  apply Int.ofNat_lt.1
  simp only [Int.natCast_natAbs, abs_of_nonneg, norm_nonneg]
  apply norm_mod_lt x hy
-- QUOTE.

/- TEXT:
我们还需要确立范数函数在欧几里得域上的第二个关键性质。
BOTH: -/
-- QUOTE:
theorem not_norm_mul_left_lt_norm (x : GaussInt) {y : GaussInt} (hy : y ≠ 0) :
    ¬(norm (x * y)).natAbs < (norm x).natAbs := by
  apply not_lt_of_ge
  rw [norm_mul, Int.natAbs_mul]
  apply le_mul_of_one_le_right (Nat.zero_le _)
  apply Int.ofNat_le.1
  rw [coe_natAbs_norm]
  exact Int.add_one_le_of_lt ((norm_pos _).mpr hy)
-- QUOTE.

/- TEXT:
现在我们可以将其整合起来，证明高斯整数是欧几里得域的一个实例。我们使用已定义的商和余数函数。
Mathlib 中欧几里得域的定义比上面的更通用，因为它允许我们证明余数相对于任何良基度量都是递减的。
比较返回自然数的范数函数的值是只需这样一个度量的一个实例，在这种情况下，所需的性质就是定理 ``natAbs_norm_mod_lt`` 和 ``not_norm_mul_left_lt_norm`` 。
BOTH: -/
-- QUOTE:
instance : EuclideanDomain GaussInt :=
  { GaussInt.instCommRing with
    quotient := (· / ·)
    remainder := (· % ·)
    quotient_mul_add_remainder_eq :=
      fun x y ↦ by simp only; rw [mod_def, add_comm] ; ring
    quotient_zero := fun x ↦ by
      simp [div_def, norm, Int.div']
      rfl
    r := (measure (Int.natAbs ∘ norm)).1
    r_wellFounded := (measure (Int.natAbs ∘ norm)).2
    remainder_lt := natAbs_norm_mod_lt
    mul_left_not_lt := not_norm_mul_left_lt_norm }
-- QUOTE.

/- TEXT:
一个直接的好处是，我们现在知道，在高斯整数中，素数和不可约数的概念是一致的。
BOTH: -/
-- QUOTE:
example (x : GaussInt) : Irreducible x ↔ Prime x :=
  irreducible_iff_prime
-- QUOTE.

end GaussInt
