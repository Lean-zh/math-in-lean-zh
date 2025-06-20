import MIL.Common
import Mathlib.Topology.Instances.Real
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

open Set Filter
open Topology Filter

/- TEXT:
.. index:: metric space

.. _metric_spaces:

度量空间
--------------


在上一节中的示例主要关注实数序列。在本节中，我们将提高一点一般性，关注度量空间。
度量空间是一种类型 ``X`` ，它配备了一个距离函数 ``dist : X → X → ℝ`` ，这是在 ``X = ℝ`` 情形下函数 ``fun x y ↦ |x - y|`` 的一种推广。

引入这样一个空间很简单，我们将检验距离函数所需的所有性质。
BOTH: -/
-- QUOTE:
variable {X : Type*} [MetricSpace X] (a b c : X)

#check (dist a b : ℝ)
#check (dist_nonneg : 0 ≤ dist a b)
#check (dist_eq_zero : dist a b = 0 ↔ a = b)
#check (dist_comm a b : dist a b = dist b a)
#check (dist_triangle a b c : dist a c ≤ dist a b + dist b c)
-- QUOTE.

/- TEXT:

请注意，我们还有其他变体，其中距离可以是无穷大，或者 ``dist a b`` 可以为零而不需要 ``a = b`` 或者两者皆是。
它们分别被称为 ``EMetricSpace`` 、 ``PseudoMetricSpace`` 和 ``PseudoEMetricSpace`` （这里“e”代表“扩展”）。

BOTH: -/
-- -- Note the next three lines are not quoted, their purpose is to make sure those things don't get renamed while we're looking elsewhere.

-- 请注意接下来的三行未加引号，其目的是在我们查看其他内容时确保这些内容不会被重命名。
#check EMetricSpace
#check PseudoMetricSpace
#check PseudoEMetricSpace

/- TEXT:

请注意，我们从实数集 ``ℝ`` 到度量空间的旅程跳过了需要线性代数知识的赋范空间这一特殊情况，这部分内容将在微积分章节中进行解释。

收敛与连续性
^^^^^^^^^^^

利用距离函数，我们已经能够在度量空间之间定义收敛序列和连续函数。
实际上，它们是在下一节所涵盖的更一般的情形中定义的，
但我们有一些引理将定义重新表述为距离的形式。
BOTH: -/
-- QUOTE:
example {u : ℕ → X} {a : X} :
    Tendsto u atTop (𝓝 a) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (u n) a < ε :=
  Metric.tendsto_atTop

example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} :
    Continuous f ↔
      ∀ x : X, ∀ ε > 0, ∃ δ > 0, ∀ x', dist x' x < δ → dist (f x') (f x) < ε :=
  Metric.continuous_iff
-- QUOTE.

/- TEXT:
.. index:: continuity, tactics ; continuity

**很多** 引理都有一些连续性假设，所以我们最终要证明很多连续性结果，并且有一个专门用于此任务的 ``连续性`` 策略。让我们证明一个连续性陈述，它将在下面的一个练习中用到。请注意，Lean 知道如何将两个度量空间的乘积视为一个度量空间，因此考虑从 ``X × X`` 到 ``ℝ`` 的连续函数是有意义的。
特别是距离函数（未卷曲的版本）就是这样一种函数。
BOTH: -/
-- QUOTE:
example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) := by continuity
-- QUOTE.

/- TEXT:

这种策略有点慢，所以了解如何手动操作也是有用的。我们首先需要利用 ``fun p : X × X ↦ f p.1`` 是连续的这一事实，因为它是连续函数  ``f`` （由假设 ``hf`` 给出）与投影 ``prod.fst`` 的复合，而 ``prod.fst`` 的连续性正是引理 ``continuous_fst`` 的内容。复合性质是  ``Continuous.comp`` ，它在 ``Continuous`` 命名空间中，所以我们可以用点表示法将 ``Continuous.comp hf continuous_fst`` 压缩为 ``hf.comp continuous_fst`` ，这实际上更易读，因为它确实读作将我们的假设和引理进行复合。我们对第二个分量做同样的操作，以获得 ``fun p ： X × X ↦ f p.2`` 的连续性。然后，我们使用 ``Continuous.prod_mk`` 将这两个连续性组合起来，得到 ``(hf.comp continuous_fst).prod_mk (hf.comp continuous_snd) : Continuous (fun p : X × X ↦ (f p.1， f p.2))`` ，并再次复合以完成我们的完整证明。
BOTH: -/
-- QUOTE:
example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) :=
  continuous_dist.comp ((hf.comp continuous_fst).prod_mk (hf.comp continuous_snd))
-- QUOTE.

/- TEXT:

通过 ``Continuous.comp`` 将 ``Continuous.prod_mk`` 和 ``continuous_dist`` 结合起来的方式感觉很笨拙，即便像上面那样大量使用点标记也是如此。更严重的问题在于，这个漂亮的证明需要大量的规划。Lean 接受上述证明项是因为它是一个完整的项，证明了一个与我们的目标定义上等价的陈述，关键在于要展开的定义是函数的复合。实际上，我们的目标函数 ``fun p ： X × X ↦ dist (f p.1) (f p.2)`` 并未以复合的形式给出。我们提供的证明项证明了 ``dist ∘ (fun p ： X × X ↦ (f p.1， f p.2))`` 的连续性，而这恰好与我们的目标函数定义上相等。但如果尝试从 ``apply continuous_dist.comp`` 开始逐步使用战术构建这个证明，Lean 的繁饰器将无法识别复合函数并拒绝应用此引理。当涉及类型乘积时，这种情况尤其糟糕。

这里更适用的引理是
 ``Continuous.dist {f g : X → Y} : Continuous f → Continuous g → Continuous (fun x ↦ dist (f x) (g x))``
它对 Lean 的繁饰器更友好，并且在直接提供完整证明项时也能提供更简短的证明，这一点从以下两个对上述陈述的新证明中可以看出：
BOTH: -/
-- QUOTE:
example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) := by
  apply Continuous.dist
  exact hf.comp continuous_fst
  exact hf.comp continuous_snd

example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) :=
  (hf.comp continuous_fst).dist (hf.comp continuous_snd)
-- QUOTE.

/- TEXT:
请注意，如果不考虑来自组合的详细说明问题，压缩我们证明的另一种方法是使用 ``Continuous.prod_map`` ，它有时很有用，并给出一个替代的证明项 ``continuous_dist.comp (hf.prod_map hf)`` ，这个证明项甚至更短，输入起来也更方便。

由于在便于详细阐述的版本和便于输入的较短版本之间做出选择令人感到遗憾，让我们以 ``Continuous.fst'`` 提供的最后一点压缩来结束这个讨论，它允许将 ``hf.comp continuous_fst`` 压缩为  ``hf.fst'`` （ ``snd``  也是如此），从而得到我们的最终证明，现在已接近晦涩难懂的程度。
BOTH: -/
-- QUOTE:
example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) :=
  hf.fst'.dist hf.snd'
-- QUOTE.

/- TEXT:

现在轮到你来证明一些连续性引理了。在尝试了连续性策略之后，你将需要使用  ``Continuous.add`` 、 ``continuous_pow``  和 ``continuous_id`` 手动完成证明。
BOTH: -/
-- QUOTE:
example {f : ℝ → X} (hf : Continuous f) : Continuous fun x : ℝ ↦ f (x ^ 2 + x) :=
  sorry
-- QUOTE.

-- SOLUTIONS:
example {f : ℝ → X} (hf : Continuous f) : Continuous fun x : ℝ ↦ f (x ^ 2 + x) :=
  hf.comp <| (continuous_pow 2).add continuous_id

/- TEXT:

到目前为止，我们把连续性视为一个整体概念，但也可以定义某一点处的连续性。
BOTH: -/
-- QUOTE:
example {X Y : Type*} [MetricSpace X] [MetricSpace Y] (f : X → Y) (a : X) :
    ContinuousAt f a ↔ ∀ ε > 0, ∃ δ > 0, ∀ {x}, dist x a < δ → dist (f x) (f a) < ε :=
  Metric.continuousAt_iff
-- QUOTE.

/- TEXT:

球、开集与闭集
^^^^^^^^^^^^^

一旦我们有了距离函数，最重要的几何定义就是（开）球和闭球。

BOTH: -/
-- QUOTE:
variable (r : ℝ)

example : Metric.ball a r = { b | dist b a < r } :=
  rfl

example : Metric.closedBall a r = { b | dist b a ≤ r } :=
  rfl
-- QUOTE.

/- TEXT:

请注意，这里的 `r` 是任意实数，没有符号限制。当然，有些陈述确实需要半径条件。
BOTH: -/
-- QUOTE:
example (hr : 0 < r) : a ∈ Metric.ball a r :=
  Metric.mem_ball_self hr

example (hr : 0 ≤ r) : a ∈ Metric.closedBall a r :=
  Metric.mem_closedBall_self hr
-- QUOTE.

/- TEXT:

一旦我们有了球，就可以定义开集。实际上，它们是在下一节所涵盖的更一般的情形中定义的，但我们有一些引理将定义重新表述为用球来表示。

BOTH: -/
-- QUOTE:
example (s : Set X) : IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, Metric.ball x ε ⊆ s :=
  Metric.isOpen_iff
-- QUOTE.

/- TEXT:

那么闭集就是其补集为开集的集合。它们的重要性质是它们在极限运算下是封闭的。一个集合的闭包是包含它的最小闭集。
BOTH: -/
-- QUOTE:
example {s : Set X} : IsClosed s ↔ IsOpen (sᶜ) :=
  isOpen_compl_iff.symm

example {s : Set X} (hs : IsClosed s) {u : ℕ → X} (hu : Tendsto u atTop (𝓝 a))
    (hus : ∀ n, u n ∈ s) : a ∈ s :=
  hs.mem_of_tendsto hu (Eventually.of_forall hus)

example {s : Set X} : a ∈ closure s ↔ ∀ ε > 0, ∃ b ∈ s, a ∈ Metric.ball b ε :=
  Metric.mem_closure_iff
-- QUOTE.

/- TEXT:
请在不使用 `mem_closure_iff_seq_limit` 的情况下完成下一个练习。
BOTH: -/
-- QUOTE:
example {u : ℕ → X} (hu : Tendsto u atTop (𝓝 a)) {s : Set X} (hs : ∀ n, u n ∈ s) :
    a ∈ closure s :=
  sorry
-- QUOTE.

-- SOLUTIONS:
example {u : ℕ → X} (hu : Tendsto u atTop (𝓝 a)) {s : Set X} (hs : ∀ n, u n ∈ s) : a ∈ closure s := by
  rw [Metric.tendsto_atTop] at hu
  rw [Metric.mem_closure_iff]
  intro ε ε_pos
  rcases hu ε ε_pos with ⟨N, hN⟩
  refine ⟨u N, hs _, ?_⟩
  rw [dist_comm]
  exact hN N le_rfl

/- TEXT:

请记住，在滤子部分中提到，邻域滤子在 Mathlib 中起着重要作用。在度量空间的背景下，关键在于球体为这些滤子提供了基。这里的主要引理是 ``Metric.nhds_basis_ball`` 和  ``Metric.nhds_basis_closedBall`` ，它们分别表明具有正半径的开球和闭球具有这一性质。中心点是一个隐式参数，因此我们可以像下面的例子那样调用  ``Filter.HasBasis.mem_iff`` 。
BOTH: -/
-- QUOTE:
example {x : X} {s : Set X} : s ∈ 𝓝 x ↔ ∃ ε > 0, Metric.ball x ε ⊆ s :=
  Metric.nhds_basis_ball.mem_iff

example {x : X} {s : Set X} : s ∈ 𝓝 x ↔ ∃ ε > 0, Metric.closedBall x ε ⊆ s :=
  Metric.nhds_basis_closedBall.mem_iff
-- QUOTE.

/- TEXT:

紧致性
^^^^^

紧性是一个重要的拓扑概念。它区分了度量空间中的子集，这些子集具有与实数中的线段相同的性质，而与其他区间不同：

* 任何取值于紧集中的序列都有一个子序列在该紧集中收敛。
* 在非空紧集上取实数值的任何连续函数都是有界的，并且在某个地方达到其界值（这被称为极值定理）。
* 紧集是闭集。

首先让我们验证实数中的单位区间确实是一个紧集，然后验证一般度量空间中紧集的上述断言。在第二个陈述中，我们只需要在给定的集合上连续，因此我们将使用 ``ContinuousOn`` 而不是 ``Continuous`` ，并且我们将分别给出最小值和最大值的陈述。当然，所有这些结果都是从更一般的形式推导出来的，其中一些将在后面的章节中讨论。
BOTH: -/
-- QUOTE:
example : IsCompact (Set.Icc 0 1 : Set ℝ) :=
  isCompact_Icc

example {s : Set X} (hs : IsCompact s) {u : ℕ → X} (hu : ∀ n, u n ∈ s) :
    ∃ a ∈ s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 a) :=
  hs.tendsto_subseq hu

example {s : Set X} (hs : IsCompact s) (hs' : s.Nonempty) {f : X → ℝ}
      (hfs : ContinuousOn f s) :
    ∃ x ∈ s, ∀ y ∈ s, f x ≤ f y :=
  hs.exists_isMinOn hs' hfs

example {s : Set X} (hs : IsCompact s) (hs' : s.Nonempty) {f : X → ℝ}
      (hfs : ContinuousOn f s) :
    ∃ x ∈ s, ∀ y ∈ s, f y ≤ f x :=
  hs.exists_isMaxOn hs' hfs

example {s : Set X} (hs : IsCompact s) : IsClosed s :=
  hs.isClosed
-- QUOTE.

/- TEXT:

我们还可以通过添加一个额外的 ``Prop`` 值类型类来指定度量空间是全局紧致的：

BOTH: -/
-- QUOTE:
example {X : Type*} [MetricSpace X] [CompactSpace X] : IsCompact (univ : Set X) :=
  isCompact_univ
-- QUOTE.

/- TEXT:

在紧致度量空间中，任何闭集都是紧致的，这就是 ``IsClosed.isCompact`` 。
BOTH: -/
#check IsCompact.isClosed

/- TEXT:
一致连续函数
^^^^^^^^^^^

现在我们来探讨度量空间上的均匀性概念：一致连续函数、柯西序列和完备性。
同样，这些概念是在更一般的背景下定义的，但在度量空间中我们有引理来获取它们的基本定义。
我们先从一致连续性讲起。

BOTH: -/
-- QUOTE:
example {X : Type*} [MetricSpace X] {Y : Type*} [MetricSpace Y] {f : X → Y} :
    UniformContinuous f ↔
      ∀ ε > 0, ∃ δ > 0, ∀ {a b : X}, dist a b < δ → dist (f a) (f b) < ε :=
  Metric.uniformContinuous_iff
-- QUOTE.

/- TEXT:

为了练习运用所有这些定义，我们将证明从紧致度量空间到度量空间的连续函数是一致连续的（在后面的章节中我们将看到更一般的形式）。

我们首先给出一个非正式的概述。设 ``f : X → Y`` 是从一个紧致度量空间到一个度量空间的连续函数。
我们固定 ``ε > 0`` ，然后开始寻找某个 ``δ`` 。

令 ``φ : X × X → ℝ ：= fun p ↦ dist (f p.1) (f p.2)`` 以及  ``K := { p ： X × X | ε ≤ φ p }`` 。
注意到由于 ``f`` 和距离函数都是连续的，所以 ``φ`` 也是连续的。
并且 ``K`` 显然是闭集（使用  ``isClosed_le`` ），因此由于 ``X`` 是紧致的，所以 ``K`` 也是紧致的。

然后我们使用 ``eq_empty_or_nonempty`` 来讨论两种可能性。如果集合 ``K`` 为空，那么显然我们已经完成了（例如，我们可以设  ``δ = 1`` ）。所以假设 ``K`` 不为空，利用极值定理选择 ``(x₀, x₁)`` 使得距离函数在 ``K`` 上达到最小值。然后我们可以设 ``δ = dist x₀ x₁`` 并检查一切是否都正常。

BOTH: -/
-- QUOTE:
example {X : Type*} [MetricSpace X] [CompactSpace X]
      {Y : Type*} [MetricSpace Y] {f : X → Y}
    (hf : Continuous f) : UniformContinuous f :=
  sorry
-- QUOTE.

-- SOLUTIONS:
example {X : Type*} [MetricSpace X] [CompactSpace X] {Y : Type*} [MetricSpace Y] {f : X → Y}
    (hf : Continuous f) : UniformContinuous f := by
  rw [Metric.uniformContinuous_iff]
  intro ε ε_pos
  let φ : X × X → ℝ := fun p ↦ dist (f p.1) (f p.2)
  have φ_cont : Continuous φ := hf.fst'.dist hf.snd'
  let K := { p : X × X | ε ≤ φ p }
  have K_closed : IsClosed K := isClosed_le continuous_const φ_cont
  have K_cpct : IsCompact K := K_closed.isCompact
  rcases eq_empty_or_nonempty K with hK | hK
  · use 1, by norm_num
    intro x y _
    have : (x, y) ∉ K := by simp [hK]
    simpa [K] using this
  · rcases K_cpct.exists_isMinOn hK continuous_dist.continuousOn with ⟨⟨x₀, x₁⟩, xx_in, H⟩
    use dist x₀ x₁
    constructor
    · change _ < _
      rw [dist_pos]
      intro h
      have : ε ≤ 0 := by simpa [K, φ, *] using xx_in
      linarith
    · intro x x'
      contrapose!
      intro (hxx' : (x, x') ∈ K)
      exact H hxx'

/- TEXT:

完备性
^^^^^^


度量空间中的柯西序列是指其各项越来越接近的序列。
表述这一概念有几种等价的方式。
特别是收敛序列是柯西序列。但反过来只有在所谓的 **完备** 空间中才成立。


BOTH: -/
-- QUOTE:
example (u : ℕ → X) :
    CauchySeq u ↔ ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, dist (u m) (u n) < ε :=
  Metric.cauchySeq_iff

example (u : ℕ → X) :
    CauchySeq u ↔ ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, dist (u n) (u N) < ε :=
  Metric.cauchySeq_iff'

example [CompleteSpace X] (u : ℕ → X) (hu : CauchySeq u) :
    ∃ x, Tendsto u atTop (𝓝 x) :=
  cauchySeq_tendsto_of_complete hu
-- QUOTE.

/- TEXT:

我们将通过证明一个方便的判别式来练习使用这个定义，该判别式是 Mathlib 中出现的一个判别式的特殊情况。这也是一个在几何背景下练习使用大求和符号的好机会。除了滤子部分的解释外，您可能还需要使用  ``tendsto_pow_atTop_nhds_zero_of_lt_one`` 、 ``Tendsto.mul``  和  ``dist_le_range_sum_dist`` 。
BOTH: -/
open BigOperators

open Finset

-- QUOTE:
theorem cauchySeq_of_le_geometric_two' {u : ℕ → X}
    (hu : ∀ n : ℕ, dist (u n) (u (n + 1)) ≤ (1 / 2) ^ n) : CauchySeq u := by
  rw [Metric.cauchySeq_iff']
  intro ε ε_pos
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 1 / 2 ^ N * 2 < ε := by sorry
  use N
  intro n hn
  obtain ⟨k, rfl : n = N + k⟩ := le_iff_exists_add.mp hn
  calc
    dist (u (N + k)) (u N) = dist (u (N + 0)) (u (N + k)) := sorry
    _ ≤ ∑ i in range k, dist (u (N + i)) (u (N + (i + 1))) := sorry
    _ ≤ ∑ i in range k, (1 / 2 : ℝ) ^ (N + i) := sorry
    _ = 1 / 2 ^ N * ∑ i in range k, (1 / 2 : ℝ) ^ i := sorry
    _ ≤ 1 / 2 ^ N * 2 := sorry
    _ < ε := sorry

-- QUOTE.

-- SOLUTIONS:
example {u : ℕ → X} (hu : ∀ n : ℕ, dist (u n) (u (n + 1)) ≤ (1 / 2) ^ n) : CauchySeq u := by
  rw [Metric.cauchySeq_iff']
  intro ε ε_pos
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 1 / 2 ^ N * 2 < ε := by
    have : Tendsto (fun N : ℕ ↦ (1 / 2 ^ N * 2 : ℝ)) atTop (𝓝 0) := by
      rw [← zero_mul (2 : ℝ)]
      apply Tendsto.mul
      simp_rw [← one_div_pow (2 : ℝ)]
      apply tendsto_pow_atTop_nhds_zero_of_lt_one <;> linarith
      exact tendsto_const_nhds
    rcases(atTop_basis.tendsto_iff (nhds_basis_Ioo_pos (0 : ℝ))).mp this ε ε_pos with ⟨N, _, hN⟩
    exact ⟨N, by simpa using (hN N left_mem_Ici).2⟩
  use N
  intro n hn
  obtain ⟨k, rfl : n = N + k⟩ := le_iff_exists_add.mp hn
  calc
    dist (u (N + k)) (u N) = dist (u (N + 0)) (u (N + k)) := by rw [dist_comm, add_zero]
    _ ≤ ∑ i in range k, dist (u (N + i)) (u (N + (i + 1))) :=
      (dist_le_range_sum_dist (fun i ↦ u (N + i)) k)
    _ ≤ ∑ i in range k, (1 / 2 : ℝ) ^ (N + i) := (sum_le_sum fun i _ ↦ hu <| N + i)
    _ = 1 / 2 ^ N * ∑ i in range k, (1 / 2 : ℝ) ^ i := by simp_rw [← one_div_pow, pow_add, ← mul_sum]
    _ ≤ 1 / 2 ^ N * 2 :=
      (mul_le_mul_of_nonneg_left (sum_geometric_two_le _)
        (one_div_nonneg.mpr (pow_nonneg (zero_le_two : (0 : ℝ) ≤ 2) _)))
    _ < ε := hN


/- TEXT:

我们已准备好迎接本节的最终大 Boss：完备度量空间上的贝尔纲定理（Baire's theorem）！
下面的证明框架展示了有趣的技术。它使用了感叹号形式的 ``choose`` 策略（您应该尝试去掉这个感叹号），并且展示了如何在证明过程中使用 ``Nat.rec_on`` 来递归定义某些内容。

BOTH: -/
-- QUOTE:
open Metric

example [CompleteSpace X] (f : ℕ → Set X) (ho : ∀ n, IsOpen (f n)) (hd : ∀ n, Dense (f n)) :
    Dense (⋂ n, f n) := by
  let B : ℕ → ℝ := fun n ↦ (1 / 2) ^ n
  have Bpos : ∀ n, 0 < B n
  sorry
  /- 将密度假设转化为两个函数 `center` 和 `radius`，对于任意的 n、x、δ、δpos，这两个函数分别关联一个中心和一个正半径，使得 `closedBall center radius` 同时包含在 `f n` 和 `closedBall x δ` 中。我们还可以要求 `radius ≤ (1/2)^(n+1)`，以确保之后能得到一个柯西序列。-/
  have :
    ∀ (n : ℕ) (x : X),
      ∀ δ > 0, ∃ y : X, ∃ r > 0, r ≤ B (n + 1) ∧ closedBall y r ⊆ closedBall x δ ∩ f n :=
    by sorry
  choose! center radius Hpos HB Hball using this
  intro x
  rw [mem_closure_iff_nhds_basis nhds_basis_closedBall]
  intro ε εpos
  /-  设 `ε` 为正数。我们需要在以 `x` 为圆心、半径为 `ε` 的球内找到一个点，该点属于所有的 `f n`。为此，我们递归地构造一个序列 `F n = (c n, r n)`，使得闭球 `closedBall (c n) (r n)` 包含在前一个球内且属于 `f n`，并且 `r n` 足够小以确保 `c n` 是一个柯西序列。那么 `c n` 收敛到一个极限，该极限属于所有的 `f n`。-/
  let F : ℕ → X × ℝ := fun n ↦
    Nat.recOn n (Prod.mk x (min ε (B 0)))
      fun n p ↦ Prod.mk (center n p.1 p.2) (radius n p.1 p.2)
  let c : ℕ → X := fun n ↦ (F n).1
  let r : ℕ → ℝ := fun n ↦ (F n).2
  have rpos : ∀ n, 0 < r n := by sorry
  have rB : ∀ n, r n ≤ B n := by sorry
  have incl : ∀ n, closedBall (c (n + 1)) (r (n + 1)) ⊆ closedBall (c n) (r n) ∩ f n := by
    sorry
  have cdist : ∀ n, dist (c n) (c (n + 1)) ≤ B n := by sorry
  have : CauchySeq c := cauchySeq_of_le_geometric_two' cdist
  -- 由于序列 `c n` 在完备空间中是柯西序列，所以它收敛于极限 `y`。
  -- 根据完备空间中柯西序列收敛的定理，存在 `y` 使得 `c n` 收敛于 `y`，记为 `ylim`。
  -- 这个点 `y` 就是我们想要的点。接下来我们要验证它属于所有的 `f n` 以及 `ball x ε`。
  use y
  have I : ∀ n, ∀ m ≥ n, closedBall (c m) (r m) ⊆ closedBall (c n) (r n) := by sorry
  have yball : ∀ n, y ∈ closedBall (c n) (r n) := by sorry
  sorry
-- QUOTE.

-- SOLUTIONS:
example [CompleteSpace X] (f : ℕ → Set X) (ho : ∀ n, IsOpen (f n)) (hd : ∀ n, Dense (f n)) :
    Dense (⋂ n, f n) := by
  let B : ℕ → ℝ := fun n ↦ (1 / 2) ^ n
  have Bpos : ∀ n, 0 < B n := fun n ↦ pow_pos sorry n
  /- 将密度假设转化为两个函数 `center` 和 `radius`，对于任意的 n、x、δ、δpos，这两个函数分别关联一个中心和一个正半径，使得 `closedBall center radius` 同时包含在 `f n` 和 `closedBall x δ` 中。我们还可以要求 `radius ≤ (1/2)^(n+1)`，以确保之后能得到一个柯西序列。 -/
  have :
    ∀ (n : ℕ) (x : X),
      ∀ δ > 0, ∃ y : X, ∃ r > 0, r ≤ B (n + 1) ∧ closedBall y r ⊆ closedBall x δ ∩ f n := by
    intro n x δ δpos
    have : x ∈ closure (f n) := hd n x
    rcases Metric.mem_closure_iff.1 this (δ / 2) (half_pos δpos) with ⟨y, ys, xy⟩
    rw [dist_comm] at xy
    obtain ⟨r, rpos, hr⟩ : ∃ r > 0, closedBall y r ⊆ f n :=
      nhds_basis_closedBall.mem_iff.1 (isOpen_iff_mem_nhds.1 (ho n) y ys)
    refine ⟨y, min (min (δ / 2) r) (B (n + 1)), ?_, ?_, fun z hz ↦ ⟨?_, ?_⟩⟩
    show 0 < min (min (δ / 2) r) (B (n + 1))
    exact lt_min (lt_min (half_pos δpos) rpos) (Bpos (n + 1))
    show min (min (δ / 2) r) (B (n + 1)) ≤ B (n + 1)
    exact min_le_right _ _
    show z ∈ closedBall x δ
    exact
      calc
        dist z x ≤ dist z y + dist y x := dist_triangle _ _ _
        _ ≤ min (min (δ / 2) r) (B (n + 1)) + δ / 2 := (add_le_add hz xy.le)
        _ ≤ δ / 2 + δ / 2 := (add_le_add_right ((min_le_left _ _).trans (min_le_left _ _)) _)
        _ = δ := add_halves δ

    show z ∈ f n
    exact
      hr
        (calc
          dist z y ≤ min (min (δ / 2) r) (B (n + 1)) := hz
          _ ≤ r := (min_le_left _ _).trans (min_le_right _ _)
          )
  choose! center radius Hpos HB Hball using this
  refine fun x ↦ (mem_closure_iff_nhds_basis nhds_basis_closedBall).2 fun ε εpos ↦ ?_
  /- `ε` 是正数。我们必须找到一个位于以 `x` 为中心、半径为 `ε` 的球内且属于所有 `f n` 的点。为此，我们递归地构造一个序列 `F n = (c n, r n)`，使得闭球 `closedBall (c n) (r n)` 包含在前一个球内且属于 `f n`，并且 `r n` 足够小以确保 `c n` 是一个柯西序列。然后 `c n` 收敛到一个属于所有 `f n` 的极限。 -/
  let F : ℕ → X × ℝ := fun n ↦
    Nat.recOn n (Prod.mk x (min ε (B 0))) fun n p ↦ Prod.mk (center n p.1 p.2) (radius n p.1 p.2)
  let c : ℕ → X := fun n ↦ (F n).1
  let r : ℕ → ℝ := fun n ↦ (F n).2
  have rpos : ∀ n, 0 < r n := by
    intro n
    induction' n with n hn
    exact lt_min εpos (Bpos 0)
    exact Hpos n (c n) (r n) hn
  have rB : ∀ n, r n ≤ B n := by
    intro n
    induction' n with n hn
    exact min_le_right _ _
    exact HB n (c n) (r n) (rpos n)
  have incl : ∀ n, closedBall (c (n + 1)) (r (n + 1)) ⊆ closedBall (c n) (r n) ∩ f n := fun n ↦
    Hball n (c n) (r n) (rpos n)
  have cdist : ∀ n, dist (c n) (c (n + 1)) ≤ B n := by
    intro n
    rw [dist_comm]
    have A : c (n + 1) ∈ closedBall (c (n + 1)) (r (n + 1)) :=
      mem_closedBall_self (rpos <| n + 1).le
    have I :=
      calc
        closedBall (c (n + 1)) (r (n + 1)) ⊆ closedBall (c n) (r n) :=
          (incl n).trans Set.inter_subset_left
        _ ⊆ closedBall (c n) (B n) := closedBall_subset_closedBall (rB n)

    exact I A
  have : CauchySeq c := cauchySeq_of_le_geometric_two' cdist
  -- 由于序列 `c n` 在完备空间中是柯西序列，所以它收敛于某个极限 `y`。
  -- 根据完备空间中柯西序列收敛的定理，存在 `y` 使得 `c n` 收敛于 `y`，记为 `ylim`。
  -- 这个点 `y` 就是我们想要的点。接下来我们要验证它属于所有的 `f n` 以及 `ball x ε`。
  use y
  have I : ∀ n, ∀ m ≥ n, closedBall (c m) (r m) ⊆ closedBall (c n) (r n) := by
    intro n
    refine Nat.le_induction ?_ fun m hnm h ↦ ?_
    · exact Subset.rfl
    · exact (incl m).trans (Set.inter_subset_left.trans h)
  have yball : ∀ n, y ∈ closedBall (c n) (r n) := by
    intro n
    refine isClosed_ball.mem_of_tendsto ylim ?_
    refine (Filter.eventually_ge_atTop n).mono fun m hm ↦ ?_
    exact I n m hm (mem_closedBall_self (rpos _).le)
  constructor
  · suffices ∀ n, y ∈ f n by rwa [Set.mem_iInter]
    intro n
    have : closedBall (c (n + 1)) (r (n + 1)) ⊆ f n :=
      Subset.trans (incl n) Set.inter_subset_right
    exact this (yball (n + 1))
  calc
    dist y x ≤ r 0 := yball 0
    _ ≤ ε := min_le_left _ _
