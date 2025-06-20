import MIL.Common
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Prod


open Set Filter

open Topology Filter

noncomputable section

/- TEXT:
.. index:: normed space

.. _normed_spaces:

赋范空间中的微分学
------------------

赋范空间
^^^^^^^^

利用 **赋范向量空间** 的概念，可以将微分推广到 ``ℝ`` 之外，该概念同时涵盖了方向和距离。我们从 **赋范群** 的概念开始，它是一个加法交换群，配备了一个实值范数函数，满足以下条件。
EXAMPLES: -/
section

-- QUOTE:
variable {E : Type*} [NormedAddCommGroup E]

example (x : E) : 0 ≤ ‖x‖ :=
  norm_nonneg x

example {x : E} : ‖x‖ = 0 ↔ x = 0 :=
  norm_eq_zero

example (x y : E) : ‖x + y‖ ≤ ‖x‖ + ‖y‖ :=
  norm_add_le x y
-- QUOTE.

/- TEXT:
每个赋范空间都是一个度量空间，其距离函数为 :math:`d(x, y) = \| x - y \|`，因此它也是一个拓扑空间。Lean 和 Mathlib 都知道这一点。
EXAMPLES: -/
-- QUOTE:
example : MetricSpace E := by infer_instance

example {X : Type*} [TopologicalSpace X] {f : X → E} (hf : Continuous f) :
    Continuous fun x ↦ ‖f x‖ :=
  hf.norm
-- QUOTE.

/- TEXT:
为了在范数的概念中引入线性代数中的概念，我们在 ``NormedAddGroup E`` 的基础上添加了 ``NormedSpace ℝ E`` 这一假设。这表明 ``E`` 是 ``ℝ`` 上的向量空间，并且标量乘法满足以下条件。
EXAMPLES: -/
-- QUOTE:
variable [NormedSpace ℝ E]

example (a : ℝ) (x : E) : ‖a • x‖ = |a| * ‖x‖ :=
  norm_smul a x
-- QUOTE.

/- TEXT:
完备的赋范空间被称为 **巴拿赫空间** 。
每个有限维向量空间都是完备的。
EXAMPLES: -/
-- QUOTE:
example [FiniteDimensional ℝ E] : CompleteSpace E := by infer_instance
-- QUOTE.

/- TEXT:
在前面的所有示例中，我们都使用实数作为基域。
更一般地说，我们可以在任何 **非平凡赋范域** 上的向量空间中理解微积分。这些域配备了实值范数，该范数具有乘法性质，并且不是每个元素的范数都为零或一（等价地说，存在范数大于一的元素）。
EXAMPLES: -/
-- QUOTE:
example (𝕜 : Type*) [NontriviallyNormedField 𝕜] (x y : 𝕜) : ‖x * y‖ = ‖x‖ * ‖y‖ :=
  norm_mul x y

example (𝕜 : Type*) [NontriviallyNormedField 𝕜] : ∃ x : 𝕜, 1 < ‖x‖ :=
  NormedField.exists_one_lt_norm 𝕜
-- QUOTE.

/- TEXT:
在一个非平凡赋范域上的有限维向量空间，只要域本身是完备的，那么该向量空间就是完备的。
EXAMPLES: -/
-- QUOTE:
example (𝕜 : Type*) [NontriviallyNormedField 𝕜] (E : Type*) [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] : CompleteSpace E :=
  FiniteDimensional.complete 𝕜 E
-- QUOTE.

end

/- TEXT:
连续线性映射
^^^^^^^^^^^^


现在我们来讨论赋范空间范畴中的态射，即连续线性映射。
在 Mathlib 中，赋范空间 ``E`` 和 ``F`` 之间的 ``𝕜`` 线性连续映射的类型写作  ``E →L[𝕜] F`` 。
它们被实现为 **捆绑映射** ，这意味着该类型的元素包含映射本身以及线性和连续的性质。
Lean 会插入一个强制转换，使得连续线性映射可以当作函数来处理。
EXAMPLES: -/
section

-- QUOTE:
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

example : E →L[𝕜] E :=
  ContinuousLinearMap.id 𝕜 E

example (f : E →L[𝕜] F) : E → F :=
  f

example (f : E →L[𝕜] F) : Continuous f :=
  f.cont

example (f : E →L[𝕜] F) (x y : E) : f (x + y) = f x + f y :=
  f.map_add x y

example (f : E →L[𝕜] F) (a : 𝕜) (x : E) : f (a • x) = a • f x :=
  f.map_smul a x
-- QUOTE.

/- TEXT:
连续线性映射具有算子范数，其特征在于以下性质。
EXAMPLES: -/
-- QUOTE:
variable (f : E →L[𝕜] F)

example (x : E) : ‖f x‖ ≤ ‖f‖ * ‖x‖ :=
  f.le_opNorm x

example {M : ℝ} (hMp : 0 ≤ M) (hM : ∀ x, ‖f x‖ ≤ M * ‖x‖) : ‖f‖ ≤ M :=
  f.opNorm_le_bound hMp hM
-- QUOTE.

end

/- TEXT:
还有一种连续线性同构的 **成束** 概念。
这种同构的类型表示为 ``E ≃L[𝕜] F`` 。

作为一项具有挑战性的练习，您可以证明巴拿赫-斯坦因豪斯定理，也称为一致有界性原理。
该原理指出，从巴拿赫空间到赋范空间的一族连续线性映射在逐点有界的情况下，这些线性映射的范数是一致有界的。
主要依据是贝尔纲定理 ``nonempty_interior_of_iUnion_of_closed`` （您在拓扑学章节中证明过其一个版本）。
次要依据包括 ``continuous_linear_map.opNorm_le_of_shell`` 、 ``interior_subset`` 、 ``interior_iInter_subset``  和  ``isClosed_le`` 。
BOTH: -/
section

-- QUOTE:
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

open Metric

-- EXAMPLES:
example {ι : Type*} [CompleteSpace E] {g : ι → E →L[𝕜] F} (h : ∀ x, ∃ C, ∀ i, ‖g i x‖ ≤ C) :
    ∃ C', ∀ i, ‖g i‖ ≤ C' := by
  -- 由范数 `‖g i x‖` 被 `n` 所限制那些的 `x : E` 组成的子集序列
  let e : ℕ → Set E := fun n ↦ ⋂ i : ι, { x : E | ‖g i x‖ ≤ n }
  -- 这些集合每个都是闭集
  have hc : ∀ n : ℕ, IsClosed (e n)
  sorry
  -- 并集是整个空间；这就是我们使用 `h` 的地方
  have hU : (⋃ n : ℕ, e n) = univ
  sorry
  /- 应用贝尔纲定理得出结论：存在某个 `m ： ℕ` ，使得 `e m` 包含某个 `x`  -/
  obtain ⟨m, x, hx⟩ : ∃ m, ∃ x, x ∈ interior (e m) := sorry
  obtain ⟨ε, ε_pos, hε⟩ : ∃ ε > 0, ball x ε ⊆ interior (e m) := sorry
  obtain ⟨k, hk⟩ : ∃ k : 𝕜, 1 < ‖k‖ := sorry
  -- 证明球内所有元素在应用任何 `g i` 后范数均不超过 `m`
  have real_norm_le : ∀ z ∈ ball x ε, ∀ (i : ι), ‖g i z‖ ≤ m
  sorry
  have εk_pos : 0 < ε / ‖k‖ := sorry
  refine ⟨(m + m : ℕ) / (ε / ‖k‖), fun i ↦ ContinuousLinearMap.opNorm_le_of_shell ε_pos ?_ hk ?_⟩
  sorry
  sorry
-- QUOTE.

-- SOLUTIONS:
example {ι : Type*} [CompleteSpace E] {g : ι → E →L[𝕜] F} (h : ∀ x, ∃ C, ∀ i, ‖g i x‖ ≤ C) :
    ∃ C', ∀ i, ‖g i‖ ≤ C' := by
  -- 由范数 `‖g i x‖` 被 `n` 所限制那些的 `x : E` 组成的子集序列
  let e : ℕ → Set E := fun n ↦ ⋂ i : ι, { x : E | ‖g i x‖ ≤ n }
  -- 这些集合每个都是闭集
  have hc : ∀ n : ℕ, IsClosed (e n) := fun i ↦
    isClosed_iInter fun i ↦ isClosed_le (g i).cont.norm continuous_const
  -- 并集是整个空间；这就是我们使用 `h` 的地方
  have hU : (⋃ n : ℕ, e n) = univ := by
    refine eq_univ_of_forall fun x ↦ ?_
    rcases h x with ⟨C, hC⟩
    obtain ⟨m, hm⟩ := exists_nat_ge C
    exact ⟨e m, mem_range_self m, mem_iInter.mpr fun i ↦ le_trans (hC i) hm⟩
  /- 应用贝尔纲定理得出结论：存在某个 `m ： ℕ` ，使得 `e m` 包含某个 `x` -/
  obtain ⟨m : ℕ, x : E, hx : x ∈ interior (e m)⟩ := nonempty_interior_of_iUnion_of_closed hc hU
  obtain ⟨ε, ε_pos, hε : ball x ε ⊆ interior (e m)⟩ := isOpen_iff.mp isOpen_interior x hx
  obtain ⟨k : 𝕜, hk : 1 < ‖k‖⟩ := NormedField.exists_one_lt_norm 𝕜
  -- 证明球内所有元素在应用任何 `g i` 后范数均不超过 `m`
  have real_norm_le : ∀ z ∈ ball x ε, ∀ (i : ι), ‖g i z‖ ≤ m := by
    intro z hz i
    replace hz := mem_iInter.mp (interior_iInter_subset _ (hε hz)) i
    apply interior_subset hz
  have εk_pos : 0 < ε / ‖k‖ := div_pos ε_pos (zero_lt_one.trans hk)
  refine ⟨(m + m : ℕ) / (ε / ‖k‖), fun i ↦ ContinuousLinearMap.opNorm_le_of_shell ε_pos ?_ hk ?_⟩
  · exact div_nonneg (Nat.cast_nonneg _) εk_pos.le
  intro y le_y y_lt
  calc
    ‖g i y‖ = ‖g i (y + x) - g i x‖ := by rw [(g i).map_add, add_sub_cancel_right]
    _ ≤ ‖g i (y + x)‖ + ‖g i x‖ := (norm_sub_le _ _)
    _ ≤ m + m :=
      (add_le_add (real_norm_le (y + x) (by rwa [add_comm, add_mem_ball_iff_norm]) i)
        (real_norm_le x (mem_ball_self ε_pos) i))
    _ = (m + m : ℕ) := by norm_cast
    _ ≤ (m + m : ℕ) * (‖y‖ / (ε / ‖k‖)) :=
      (le_mul_of_one_le_right (Nat.cast_nonneg _)
        ((one_le_div <| div_pos ε_pos (zero_lt_one.trans hk)).2 le_y))
    _ = (m + m : ℕ) / (ε / ‖k‖) * ‖y‖ := (mul_comm_div _ _ _).symm


-- BOTH:
end

/- TEXT:
渐近比较
^^^^^^^^

定义可微性也需要渐近比较。
Mathlib 拥有一个涵盖大 O 和小 o 关系的广泛库，其定义如下。
打开 ``asymptotics`` 域允许我们使用相应的符号。
在这里，我们将仅使用小 o 来定义可微性。
EXAMPLES: -/
-- QUOTE:
open Asymptotics

example {α : Type*} {E : Type*} [NormedGroup E] {F : Type*} [NormedGroup F] (c : ℝ)
    (l : Filter α) (f : α → E) (g : α → F) : IsBigOWith c l f g ↔ ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖ :=
  isBigOWith_iff

example {α : Type*} {E : Type*} [NormedGroup E] {F : Type*} [NormedGroup F]
    (l : Filter α) (f : α → E) (g : α → F) : f =O[l] g ↔ ∃ C, IsBigOWith C l f g :=
  isBigO_iff_isBigOWith

example {α : Type*} {E : Type*} [NormedGroup E] {F : Type*} [NormedGroup F]
    (l : Filter α) (f : α → E) (g : α → F) : f =o[l] g ↔ ∀ C > 0, IsBigOWith C l f g :=
  isLittleO_iff_forall_isBigOWith

example {α : Type*} {E : Type*} [NormedAddCommGroup E] (l : Filter α) (f g : α → E) :
    f ~[l] g ↔ (f - g) =o[l] g :=
  Iff.rfl
-- QUOTE.

/- TEXT:
可微性
^^^^^^

我们现在准备讨论赋范空间之间的可微函数。
与基本的一维情况类似，Mathlib 定义了一个谓词 ``HasFDerivAt`` 和一个函数  ``fderiv`` 。
这里的字母“f”代表 **弗雷歇（Fréchet）** 。
EXAMPLES: -/
section

-- QUOTE:
open Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

example (f : E → F) (f' : E →L[𝕜] F) (x₀ : E) :
    HasFDerivAt f f' x₀ ↔ (fun x ↦ f x - f x₀ - f' (x - x₀)) =o[𝓝 x₀] fun x ↦ x - x₀ :=
  hasFDerivAtFilter_iff_isLittleO ..

example (f : E → F) (f' : E →L[𝕜] F) (x₀ : E) (hff' : HasFDerivAt f f' x₀) : fderiv 𝕜 f x₀ = f' :=
  hff'.fderiv
-- QUOTE.

/- TEXT:
我们还有取值于多重线性映射类型 ``E [×n]→L[𝕜] F`` 的迭代导数，并且我们有连续可微函数。类型 ``WithTop ℕ`` 是在自然数 ``ℕ`` 的基础上添加了一个比任何自然数都大的元素 ``⊤`` 。因此，:math:`\mathcal{C}^\infty` 函数是满足 ``ContDiff 𝕜 ⊤ f`` 的函数 ``f`` 。
EXAMPLES: -/
-- QUOTE:
example (n : ℕ) (f : E → F) : E → E[×n]→L[𝕜] F :=
  iteratedFDeriv 𝕜 n f

example (n : WithTop ℕ) {f : E → F} :
    ContDiff 𝕜 n f ↔
      (∀ m : ℕ, (m : WithTop ℕ) ≤ n → Continuous fun x ↦ iteratedFDeriv 𝕜 m f x) ∧
        ∀ m : ℕ, (m : WithTop ℕ) < n → Differentiable 𝕜 fun x ↦ iteratedFDeriv 𝕜 m f x :=
  contDiff_iff_continuous_differentiable
-- QUOTE.

/- TEXT:
存在一种更严格的可微性概念，称为 ``HasStrictFDerivAt`` ，它用于逆函数定理和隐函数定理的表述，这两个定理都在 Mathlib 中。在 ``ℝ`` 或 ``ℂ`` 上，连续可微函数都是严格可微的。
EXAMPLES: -/
-- QUOTE:
example {𝕂 : Type*} [RCLike 𝕂] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕂 E] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕂 F] {f : E → F} {x : E} {n : WithTop ℕ}
    (hf : ContDiffAt 𝕂 n f x) (hn : 1 ≤ n) : HasStrictFDerivAt f (fderiv 𝕂 f x) x :=
  hf.hasStrictFDerivAt hn
-- QUOTE.

/- TEXT:
局部逆定理是通过一种运算来表述的，该运算从一个函数生成其反函数，并且假定该函数在点 ``a`` 处严格可微，且其导数为同构映射。

下面的第一个例子得到了这个局部逆。
接下来的一个例子表明，它确实是从左和从右的局部逆，并且它是严格可微的。
EXAMPLES: -/
-- QUOTE:
section LocalInverse
variable [CompleteSpace E] {f : E → F} {f' : E ≃L[𝕜] F} {a : E}

example (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) : F → E :=
  HasStrictFDerivAt.localInverse f f' a hf

example (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) :
    ∀ᶠ x in 𝓝 a, hf.localInverse f f' a (f x) = x :=
  hf.eventually_left_inverse

example (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) :
    ∀ᶠ x in 𝓝 (f a), f (hf.localInverse f f' a x) = x :=
  hf.eventually_right_inverse

example {f : E → F} {f' : E ≃L[𝕜] F} {a : E}
  (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) :
    HasStrictFDerivAt (HasStrictFDerivAt.localInverse f f' a hf) (f'.symm : F →L[𝕜] E) (f a) :=
  HasStrictFDerivAt.to_localInverse hf

end LocalInverse
-- QUOTE.

/- TEXT:
这只是对 Mathlib 中微分学的一个快速浏览。该库包含许多我们未讨论过的变体。例如，在一维情况下，您可能希望使用单侧导数。在 Mathlib 中，您可以在更一般的上下文中找到实现此目的的方法；请参阅 ``HasFDerivWithinAt`` 或更通用的 ``HasFDerivAtFilter`` 。
EXAMPLES: -/
#check HasFDerivWithinAt

#check HasFDerivAtFilter

end
