import MIL.Common
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open Set Filter

open Topology Filter ENNReal

open MeasureTheory

noncomputable section
variable {α : Type*} [MeasurableSpace α]
variable {μ : Measure α}

/- TEXT:
.. _integration:

积分
-----------

现在我们有了测度和可测空间，我们就可以考虑积分了。正如前文所讲，Mathlib 使用非常一般的积分记号，支持任意的 Banach 空间。像往常一样，我们不希望我们的记号带有假设，所以我们这样约定：如果函数不可积，那么积分等于零。大多数与积分有关的引理都有可积性假设。
EXAMPLES: -/
-- QUOTE:
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {f : α → E}

example {f g : α → E} (hf : Integrable f μ) (hg : Integrable g μ) :
    ∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ :=
  integral_add hf hg
-- QUOTE.

/- TEXT:
作为我们做出的各种约定之间复杂交互的一个例子，让我们看看如何积分常值函数。回顾一下测度 `μ` 是在扩展的非负实数 `ℝ≥0∞` 上取值的，存在一个函数 `ENNReal.toReal : ℝ≥0∞ → ℝ` 把无穷点 `⊤` 映到0。对任意 `s : Set α`，如果 `μ s = ⊤` ，则非零的常值函数在 `s` 上不可积，因此根据约定积分值为0，刚好是 `(μ s).toReal` 的结果。所以我们有下面的引理。
EXAMPLES: -/
-- QUOTE:
example {s : Set α} (c : E) : ∫ x in s, c ∂μ = (μ s).toReal • c :=
  setIntegral_const c
-- QUOTE.

/- TEXT:
现在我们快速地解释如何获得积分理论中最重要的定理，从控制收敛定理开始 （dominated convergence theorem）。Mathlib 中有几个版本，这里我们只展示最基本的一个。
EXAMPLES: -/
-- QUOTE:
open Filter

example {F : ℕ → α → E} {f : α → E} (bound : α → ℝ) (hmeas : ∀ n, AEStronglyMeasurable (F n) μ)
    (hint : Integrable bound μ) (hbound : ∀ n, ∀ᵐ a ∂μ, ‖F n a‖ ≤ bound a)
    (hlim : ∀ᵐ a ∂μ, Tendsto (fun n : ℕ ↦ F n a) atTop (𝓝 (f a))) :
    Tendsto (fun n ↦ ∫ a, F n a ∂μ) atTop (𝓝 (∫ a, f a ∂μ)) :=
  tendsto_integral_of_dominated_convergence bound hmeas hint hbound hlim
-- QUOTE.

/- TEXT:
还有一个积类型上的积分的 Fubini 定理：
EXAMPLES: -/
-- QUOTE:
example {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ] {β : Type*}
    [MeasurableSpace β] {ν : Measure β} [SigmaFinite ν] (f : α × β → E)
    (hf : Integrable f (μ.prod ν)) : ∫ z, f z ∂ μ.prod ν = ∫ x, ∫ y, f (x, y) ∂ν ∂μ :=
  integral_prod f hf
-- QUOTE.

end

/- TEXT:
有一个非常一般的版本的卷积适用于任何连续双线性形式。
EXAMPLES: -/
section

-- QUOTE:
open Convolution

-- EXAMPLES:
variable {𝕜 : Type*} {G : Type*} {E : Type*} {E' : Type*} {F : Type*} [NormedAddCommGroup E]
  [NormedAddCommGroup E'] [NormedAddCommGroup F] [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]
  [NormedSpace 𝕜 E'] [NormedSpace 𝕜 F] [MeasurableSpace G] [NormedSpace ℝ F] [CompleteSpace F]
  [Sub G]

example (f : G → E) (g : G → E') (L : E →L[𝕜] E' →L[𝕜] F) (μ : Measure G) :
    f ⋆[L, μ] g = fun x ↦ ∫ t, L (f t) (g (x - t)) ∂μ :=
  rfl
-- QUOTE.

end

/- TEXT:
最后，Mathlib 有一个非常一般的换元公式。下面的命题中，`BorelSpace E` 意为由开集 `E` 生成的 `E` 上的 :math:`\sigma`-代数，`IsAddHaarMeasure μ` 意为测度 `μ` 是左不变的(left-invariant)，在紧集上有限，在开集上为正数。
EXAMPLES: -/
-- QUOTE:
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {s : Set E} {f : E → E}
    {f' : E → E →L[ℝ] E} (hs : MeasurableSet s)
    (hf : ∀ x : E, x ∈ s → HasFDerivWithinAt f (f' x) s x) (h_inj : InjOn f s) (g : E → F) :
    ∫ x in f '' s, g x ∂μ = ∫ x in s, |(f' x).det| • g (f x) ∂μ :=
  integral_image_eq_integral_abs_det_fderiv_smul μ hs hf h_inj g
-- QUOTE.
