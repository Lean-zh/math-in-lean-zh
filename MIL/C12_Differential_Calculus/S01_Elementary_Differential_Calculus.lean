import MIL.Common
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue

open Set Filter
open Topology Filter Classical Real

noncomputable section

/- TEXT:
.. index:: elementary calculus

.. _elementary_differential_calculus:

初等微分学
-----------


设 ``f`` 为从实数到实数的函数。讨论 ``f`` 在单个点处的导数与讨论导数函数是有区别的。
在 Mathlib 中，第一个概念表示如下。
EXAMPLES: -/
-- QUOTE:
open Real

/-- 正弦函数在 0 处的导数为 1 。 -/
example : HasDerivAt sin 1 0 := by simpa using hasDerivAt_sin 0
-- QUOTE.

/- TEXT:
我们也可以在不指明某点处导数的情况下表达函数 ``f`` 在该点可微，方法是写成 ``DifferentiableAt ℝ`` 。我们明确写出 ``ℝ`` 是因为在稍更一般的语境中，当我们讨论从 ``ℂ`` 到 ``ℂ`` 的函数时，我们希望能够在实可微和复可微（即复导数的意义下可微）之间做出区分。
EXAMPLES: -/
-- QUOTE:
example (x : ℝ) : DifferentiableAt ℝ sin x :=
  (hasDerivAt_sin x).differentiableAt
-- QUOTE.

/- TEXT:
每次想要提及导数时都得提供可微性的证明，这会很不方便。
因此，Mathlib 提供了一个函数 ``deriv f ： ℝ → ℝ`` ，它适用于任何 ``f ： ℝ → ℝ`` 的函数，
但在 ``f`` 不可微的任何点上，该函数被定义为取值 ``0`` 。
EXAMPLES: -/
-- QUOTE:
example {f : ℝ → ℝ} {x a : ℝ} (h : HasDerivAt f a x) : deriv f x = a :=
  h.deriv

example {f : ℝ → ℝ} {x : ℝ} (h : ¬DifferentiableAt ℝ f x) : deriv f x = 0 :=
  deriv_zero_of_not_differentiableAt h
-- QUOTE.

/- TEXT:
当然，关于 ``deriv`` 的许多引理确实需要可微性假设。例如，您应该思考一下在没有可微性假设的情况下，下一个引理的反例。
EXAMPLES: -/
-- QUOTE:
example {f g : ℝ → ℝ} {x : ℝ} (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    deriv (f + g) x = deriv f x + deriv g x :=
  deriv_add hf hg
-- QUOTE.

/- TEXT:
有趣的是，然而，存在一些语句能够通过利用函数不可微时 ``deriv`` 的值默认为零这一事实来避免可微性假设。
因此，理解下面的语句需要确切了解 ``deriv`` 的定义。
EXAMPLES: -/
-- QUOTE:
example {f : ℝ → ℝ} {a : ℝ} (h : IsLocalMin f a) : deriv f a = 0 :=
  h.deriv_eq_zero
-- QUOTE.

/- TEXT:
我们甚至可以在没有任何可微性假设的情况下陈述罗尔定理（Rolle's theorem），这似乎更奇怪。
EXAMPLES: -/
-- QUOTE:
open Set

example {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hfc : ContinuousOn f (Icc a b)) (hfI : f a = f b) :
    ∃ c ∈ Ioo a b, deriv f c = 0 :=
  exists_deriv_eq_zero hab hfc hfI
-- QUOTE.

/- TEXT:
当然，这个技巧对一般的中值定理并不适用。
EXAMPLES: -/
-- QUOTE:
example (f : ℝ → ℝ) {a b : ℝ} (hab : a < b) (hf : ContinuousOn f (Icc a b))
    (hf' : DifferentiableOn ℝ f (Ioo a b)) : ∃ c ∈ Ioo a b, deriv f c = (f b - f a) / (b - a) :=
  exists_deriv_eq_slope f hab hf hf'
-- QUOTE.

/- TEXT:
Lean 可以使用 ``simp`` 策略自动计算一些简单的导数。
EXAMPLES: -/
-- QUOTE:
example : deriv (fun x : ℝ ↦ x ^ 5) 6 = 5 * 6 ^ 4 := by simp

example : deriv sin π = -1 := by simp
-- QUOTE.
