import MIL.Common
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open Set Filter

noncomputable section

/- TEXT:
.. index:: measure theory

.. _measure_theory:

测度论
--------------
Mathlib 中积分的数学基础是测度论。甚至前一节的初等积分实际上也是 Bochner 积分。Bochner 积分是 Lebesgue 积分的推广，目标空间可以是任意的Banach空间，不一定是有限维的。

测度论的第一部分是集合的 :math:`\sigma` -代数的语言，被称作*可测集*。`MeasurableSpace` 类型族提供了带有这种结构的类型。空集 `empty` 和单元素集 `univ` 是可测的，可测集的补集是可测的，可数交和可数并是可测的。注意，这些公理是冗余的；如果你 `#print MeasurableSpace`，你会看到Mathlib用来构造可测集的公理。可数性条件可以使用 `Encodable` 类型族来表示。

BOTH: -/
-- QUOTE:
variable {α : Type*} [MeasurableSpace α]

-- EXAMPLES:
example : MeasurableSet (∅ : Set α) :=
  MeasurableSet.empty

example : MeasurableSet (univ : Set α) :=
  MeasurableSet.univ

example {s : Set α} (hs : MeasurableSet s) : MeasurableSet (sᶜ) :=
  hs.compl

example : Encodable ℕ := by infer_instance

example (n : ℕ) : Encodable (Fin n) := by infer_instance

-- BOTH:
variable {ι : Type*} [Encodable ι]

-- EXAMPLES:
example {f : ι → Set α} (h : ∀ b, MeasurableSet (f b)) : MeasurableSet (⋃ b, f b) :=
  MeasurableSet.iUnion h

example {f : ι → Set α} (h : ∀ b, MeasurableSet (f b)) : MeasurableSet (⋂ b, f b) :=
  MeasurableSet.iInter h
-- QUOTE.

/- TEXT:
如果一个类型是可测的，那么我们就可以测量它。字面上，对配备 :math:`\sigma` -代数的集合（或者类型）的测量是一个函数，它是从可测集到扩展（即允许无穷）非负实数的函数，并且满足可数无交并集合上可加性。在 Mathlib 中，我们不希望每次测量集合时都带着写一个集合可测。因此我们把这个测度推广到任何集合 `s` ，作为包含 `s` 的可测集合的测度的最小值。当然，许多引理仍然需要可测假设，但不是全部。
BOTH: -/
-- QUOTE:
open MeasureTheory
variable {μ : Measure α}

-- EXAMPLES:
example (s : Set α) : μ s = ⨅ (t : Set α) (_ : s ⊆ t) (_ : MeasurableSet t), μ t :=
  measure_eq_iInf s

example (s : ι → Set α) : μ (⋃ i, s i) ≤ ∑' i, μ (s i) :=
  measure_iUnion_le s

example {f : ℕ → Set α} (hmeas : ∀ i, MeasurableSet (f i)) (hdis : Pairwise (Disjoint on f)) :
    μ (⋃ i, f i) = ∑' i, μ (f i) :=
  μ.m_iUnion hmeas hdis
-- QUOTE.

/- TEXT:
一旦一个类型有了与它相关联的测度，我们就说，如果性质 `P` 只在一个测度为0的集合上失效，则 `P` “几乎处处”成立 (almost everywhere, ae)。几乎处处的性质集合形成了一个过滤器 (filter)，但是 Mathlib 引入了特殊的符号来表示一个性质几乎处处成立。

EXAMPLES: -/
-- QUOTE:
example {P : α → Prop} : (∀ᵐ x ∂μ, P x) ↔ ∀ᶠ x in ae μ, P x :=
  Iff.rfl
-- QUOTE.
