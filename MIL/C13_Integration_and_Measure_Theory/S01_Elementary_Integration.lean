import MIL.Common
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.Convolution

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

open Set Filter

open Topology Filter

noncomputable section

/- TEXT:
.. index:: integration

.. _elementary_integration:

初等积分
----------------------

我们首先关注函数在 `ℝ` 上有限区间的积分。我们可以积分初等函数。

EXAMPLES: -/
-- QUOTE:
open MeasureTheory intervalIntegral

open Interval
-- 这里引入了记号`[[a, b]]` 来表示区间`min a b`到`max a b`。

example (a b : ℝ) : (∫ x in a..b, x) = (b ^ 2 - a ^ 2) / 2 :=
  integral_id

example {a b : ℝ} (h : (0 : ℝ) ∉ [[a, b]]) : (∫ x in a..b, 1 / x) = Real.log (b / a) :=
  integral_one_div h
-- QUOTE.

/- TEXT:
微积分基本定理联系了微分和积分。下面我们给出这个定理的两个部分的一种简单情形。
第一部分说明积分是微分的逆运算，第二部分说明了如何计算微元的累积。（这两个部分非常密切相关，但它们的最好版本(没有写在这里)并不等价。）

EXAMPLES: -/
-- QUOTE:
example (f : ℝ → ℝ) (hf : Continuous f) (a b : ℝ) : deriv (fun u ↦ ∫ x : ℝ in a..u, f x) b = f b :=
  (integral_hasStrictDerivAt_right (hf.intervalIntegrable _ _) (hf.stronglyMeasurableAtFilter _ _)
        hf.continuousAt).hasDerivAt.deriv

example {f : ℝ → ℝ} {a b : ℝ} {f' : ℝ → ℝ} (h : ∀ x ∈ [[a, b]], HasDerivAt f (f' x) x)
    (h' : IntervalIntegrable f' volume a b) : (∫ y in a..b, f' y) = f b - f a :=
  integral_eq_sub_of_hasDerivAt h h'
-- QUOTE.

/- TEXT:
在Mathlib中也定义了卷积，并证明了卷积的基本性质。
EXAMPLES: -/
-- QUOTE:
open Convolution

example (f : ℝ → ℝ) (g : ℝ → ℝ) : f ⋆ g = fun x ↦ ∫ t, f t * g (x - t) :=
  rfl
-- QUOTE.
