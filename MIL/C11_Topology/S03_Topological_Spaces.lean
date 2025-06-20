import MIL.Common
import Mathlib.Topology.Instances.Real
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

open Set Filter Topology

/- TEXT:
.. index:: topological space

.. _topological_spaces:

拓扑空间
--------


基础
^^^^^^^^^^^^


我们现在提高一般性，引入拓扑空间。我们将回顾定义拓扑空间的两种主要方式，然后解释拓扑空间范畴比度量空间范畴表现得要好得多。请注意，这里我们不会使用 Mathlib 的范畴论，只是采用一种稍微范畴化一点的观点。

从度量空间到拓扑空间转变的第一种思考方式是，我们只记住开集（或等价地，闭集）的概念。从这个角度来看，拓扑空间是一种配备了被称为开集的集合族的类型。这个集合族必须满足下面给出的若干公理（这个集合族稍有冗余，但我们忽略这一点）。
BOTH: -/
-- QUOTE:
section
variable {X : Type*} [TopologicalSpace X]

example : IsOpen (univ : Set X) :=
  isOpen_univ

example : IsOpen (∅ : Set X) :=
  isOpen_empty

example {ι : Type*} {s : ι → Set X} (hs : ∀ i, IsOpen (s i)) : IsOpen (⋃ i, s i) :=
  isOpen_iUnion hs

example {ι : Type*} [Fintype ι] {s : ι → Set X} (hs : ∀ i, IsOpen (s i)) :
    IsOpen (⋂ i, s i) :=
  isOpen_iInter_of_finite hs
-- QUOTE.

/- TEXT:

闭集被定义为补集是开集的集合。拓扑空间之间的函数是（全局）连续的，当且仅当所有开集的原像都是开集。
BOTH: -/
-- QUOTE:
variable {Y : Type*} [TopologicalSpace Y]

example {f : X → Y} : Continuous f ↔ ∀ s, IsOpen s → IsOpen (f ⁻¹' s) :=
  continuous_def
-- QUOTE.

/- TEXT:
根据这个定义，我们已经可以看出，与度量空间相比，拓扑空间仅保留了足够的信息来讨论连续函数：如果且仅如果两种拓扑结构具有相同的连续函数，则类型上的两种拓扑结构相同（实际上，当且仅当两种结构具有相同的开集时，恒等函数在两个方向上都是连续的）。

然而，一旦我们转向某一点的连续性，就会看到基于开集的方法的局限性。在 Mathlib 中，我们经常将拓扑空间视为每个点 x 都附带一个邻域滤子 ``𝓝 x`` 的类型（相应的函数 ``X → Filter X`` 满足进一步说明的某些条件）。回想一下滤子部分的内容，这些工具发挥着两个相关的作用。首先， ``𝓝 x`` 被视为 X 中接近 ``x`` 的点的广义集合。其次，它被视为一种方式，用于说明对于任何谓词 ``P : X → Prop`` ，该谓词对于足够接近 x 的点成立。让我们来陈述 ``f ： X → Y`` 在 ``x`` 处连续。纯粹基于滤子的说法是， ``f``  下 ``x`` 附近点的广义集合的直接像包含在 ``f x`` 附近点的广义集合中。回想一下，这可以写成 ``map f (𝓝 x) ≤ 𝓝 (f x)`` 或者 ``Tendsto f (𝓝 x) (𝓝 (f x))`` 。
BOTH: -/
-- QUOTE:
example {f : X → Y} {x : X} : ContinuousAt f x ↔ map f (𝓝 x) ≤ 𝓝 (f x) :=
  Iff.rfl
-- QUOTE.

/- TEXT:
还可以使用被视为普通集合的邻域和被视为广义集合的邻域滤子来拼写它：“对于 ``f x`` 的任何邻域 ``U`` ，所有靠近 ``x`` 的点都被发送到 ``U`` ”。请注意，证明又是 ``iff.rfl`` ，这种观点在定义上与前一种观点等价。
BOTH: -/
-- QUOTE:
example {f : X → Y} {x : X} : ContinuousAt f x ↔ ∀ U ∈ 𝓝 (f x), ∀ᶠ x in 𝓝 x, f x ∈ U :=
  Iff.rfl
-- QUOTE.

/- TEXT:
现在我们来解释如何从一种观点转换到另一种观点。就开集而言，我们可以简单地将 ``𝓝 x`` 的成员定义为包含一个包含 ``x`` 的开集的集合。
BOTH: -/
-- QUOTE:
example {x : X} {s : Set X} : s ∈ 𝓝 x ↔ ∃ t, t ⊆ s ∧ IsOpen t ∧ x ∈ t :=
  mem_nhds_iff
-- QUOTE.

/- TEXT:
要朝另一方向进行，我们需要讨论 ``𝓝 ： X → Filter X`` 成为拓扑的邻域函数必须满足的条件。

第一个约束条件是，将 ``𝓝 x`` 视为广义集合时，它将包含被视为广义集合 ``pure x`` 的集合 ``{x}`` （解释这个奇怪的名字会离题太远，所以我们暂时接受它）。另一种说法是，如果一个谓词对靠近 ``x`` 的点成立，那么它在 ``x`` 处也成立。
BOTH: -/
-- QUOTE:
example (x : X) : pure x ≤ 𝓝 x :=
  pure_le_nhds x

example (x : X) (P : X → Prop) (h : ∀ᶠ y in 𝓝 x, P y) : P x :=
  h.self_of_nhds
-- QUOTE.

/- TEXT:
然后一个更微妙的要求是，对于任何谓词 ``P : X → Prop`` 以及任何 ``x`` ，如果 ``P y`` 对于接近 ``x`` 的 ``y`` 成立，那么对于接近 ``x`` 的 ``y`` 以及接近 ``y`` 的 ``z`` ， ``P z`` 也成立。更确切地说，我们有：
BOTH: -/
-- QUOTE:
example {P : X → Prop} {x : X} (h : ∀ᶠ y in 𝓝 x, P y) : ∀ᶠ y in 𝓝 x, ∀ᶠ z in 𝓝 y, P z :=
  eventually_eventually_nhds.mpr h
-- QUOTE.

/- TEXT:
这两个结果描述了对于集合 X 上的拓扑空间结构而言，函数 ``X → Filter X`` 成为邻域函数的特征。仍然存在一个函数 ``TopologicalSpace.mkOfNhds : (X → Filter X) → TopologicalSpace X`` ，但只有当输入满足上述两个约束条件时，它才会将其作为邻域函数返回。更确切地说，我们有一个引理 ``TopologicalSpace.nhds_mkOfNhds`` ，以另一种方式说明了这一点，而我们的下一个练习将从上述表述方式推导出这种不同的表述方式。
BOTH: -/
#check TopologicalSpace.mkOfNhds

#check TopologicalSpace.nhds_mkOfNhds

-- QUOTE:
example {α : Type*} (n : α → Filter α) (H₀ : ∀ a, pure a ≤ n a)
    (H : ∀ a : α, ∀ p : α → Prop, (∀ᶠ x in n a, p x) → ∀ᶠ y in n a, ∀ᶠ x in n y, p x) :
    ∀ a, ∀ s ∈ n a, ∃ t ∈ n a, t ⊆ s ∧ ∀ a' ∈ t, s ∈ n a' :=
  sorry
-- QUOTE.

-- SOLUTIONS:
example {α : Type*} (n : α → Filter α) (H₀ : ∀ a, pure a ≤ n a)
    (H : ∀ a : α, ∀ p : α → Prop, (∀ᶠ x in n a, p x) → ∀ᶠ y in n a, ∀ᶠ x in n y, p x) :
    ∀ a, ∀ s ∈ n a, ∃ t ∈ n a, t ⊆ s ∧ ∀ a' ∈ t, s ∈ n a' := by
  intro a s s_in
  refine ⟨{ y | s ∈ n y }, H a (fun x ↦ x ∈ s) s_in, ?_, by tauto⟩
  rintro y (hy : s ∈ n y)
  exact H₀ y hy

-- BOTH:
end

-- BOTH.
/- TEXT:
请注意， ``TopologicalSpace.mkOfNhds``  并不经常使用，但了解拓扑空间结构中邻域滤子的精确含义仍然是很有好处的。

要在 Mathlib 中高效地使用拓扑空间，接下来需要了解的是，我们大量使用了 ``TopologicalSpace : Type u → Type u`` 的形式属性。从纯粹的数学角度来看，这些形式属性是解释拓扑空间如何解决度量空间存在的问题的一种非常清晰的方式。从这个角度来看，拓扑空间解决的问题在于度量空间的函子性非常差，而且总体上具有非常糟糕的范畴性质。这还不包括前面已经讨论过的度量空间包含大量拓扑上无关的几何信息这一事实。

我们先关注函子性。度量空间结构可以诱导到子集上，或者等价地说，可以通过单射映射拉回。但也就仅此而已。它们不能通过一般的映射拉回，甚至不能通过满射映射推前。

特别是对于度量空间的商空间或不可数个度量空间的乘积，不存在合理的距离。例如，考虑类型 ``ℝ → ℝ`` ，将其视为由 ``ℝ`` 索引的 ``ℝ`` 的副本的乘积。我们希望说函数序列的逐点收敛是一种值得考虑的收敛概念。但在 ``ℝ → ℝ`` 上不存在能给出这种收敛概念距离。与此相关的是，不存在这样的距离，使得映射 ``f : X → (ℝ → ℝ)`` 是连续的当且仅当对于每个 ``t ： ℝ`` ， ``fun x ↦ f x t`` 是连续的。

现在我们来回顾一下用于解决所有这些问题的数据。首先，我们可以使用任何映射 ``f : X → Y`` 将拓扑从一侧推到另一侧或从另一侧拉到这一侧。这两个操作形成了一个伽罗瓦连接。
BOTH: -/
-- QUOTE:
variable {X Y : Type*}

example (f : X → Y) : TopologicalSpace X → TopologicalSpace Y :=
  TopologicalSpace.coinduced f

example (f : X → Y) : TopologicalSpace Y → TopologicalSpace X :=
  TopologicalSpace.induced f

example (f : X → Y) (T_X : TopologicalSpace X) (T_Y : TopologicalSpace Y) :
    TopologicalSpace.coinduced f T_X ≤ T_Y ↔ T_X ≤ TopologicalSpace.induced f T_Y :=
  coinduced_le_iff_le_induced
-- QUOTE.

/- TEXT:
这些操作与函数的复合兼容。
通常，前推是协变的，后拉是逆变的，参见 ``coinduced_compose`` 和 ``induced_compose`` 。
在纸上，我们将使用记号 :math:`f_*T` 表示 ``TopologicalSpace.coinduced f T`` ，使用记号 :math:`f^*T` 表示 ``TopologicalSpace.induced f T`` 。
BOTH: -/
#check coinduced_compose

#check induced_compose

/- TEXT:
接下来的一个重要部分是在给定结构下对 ``拓扑空间 X`` 建立一个完整的格结构。如果您认为拓扑主要是开集的数据，那么您会期望 ``拓扑空间 X`` 上的序关系来自 ``Set (Set X)`` ，即您期望 ``t ≤ t'`` 当且仅当对于 ``t'`` 中的开集  ``u`` ，它在 ``t`` 中也是开集。然而，我们已经知道 Mathlib 更侧重于邻域而非开集，因此对于任何 ``x ： X`` ，我们希望从拓扑空间到邻域的映射 ``fun T ： TopologicalSpace X ↦ @nhds X T x`` 是保序的。而且我们知道 ``Filter X`` 上的序关系是为确保 ``principal : Set X → Filter X`` 保序而设计的，从而可以将滤子视为广义集合。所以我们在 ``TopologicalSpace X`` 上使用的序关系与来自 ``Set (Set X)`` 的序关系是相反的。
BOTH: -/
-- QUOTE:
example {T T' : TopologicalSpace X} : T ≤ T' ↔ ∀ s, T'.IsOpen s → T.IsOpen s :=
  Iff.rfl
-- QUOTE.

/- TEXT:

现在，我们可以通过将推进（或拉回）操作与序关系相结合来恢复连续性。

BOTH: -/
-- QUOTE:
example (T_X : TopologicalSpace X) (T_Y : TopologicalSpace Y) (f : X → Y) :
    Continuous f ↔ TopologicalSpace.coinduced f T_X ≤ T_Y :=
  continuous_iff_coinduced_le
-- QUOTE.

/- TEXT:
有了这个定义以及前推和复合的兼容性，我们自然地得到了这样一个通用性质：对于任何拓扑空间 :math:`Z` ，函数 :math:`g : Y → Z` 对于拓扑 :math:`f_*T_X` 是连续的，当且仅当 :math:`g ∘ f` 是连续的。

.. math::
  g \text{ continuous } &⇔ g_*(f_*T_X) ≤ T_Z \\
  &⇔ (g ∘ f)_* T_X ≤ T_Z \\
  &⇔ g ∘ f \text{ continuous}


BOTH: -/
-- QUOTE:
example {Z : Type*} (f : X → Y) (T_X : TopologicalSpace X) (T_Z : TopologicalSpace Z)
      (g : Y → Z) :
    @Continuous Y Z (TopologicalSpace.coinduced f T_X) T_Z g ↔
      @Continuous X Z T_X T_Z (g ∘ f) := by
  rw [continuous_iff_coinduced_le, coinduced_compose, continuous_iff_coinduced_le]
-- QUOTE.

/- TEXT:
因此，我们已经得到了商拓扑（使用投影映射作为 ``f`` ）。这并没有用到对于所有 ``X`` ， ``TopologicalSpace X`` 都是一个完备格这一事实。现在让我们看看所有这些结构如何通过抽象的废话证明积拓扑的存在性。
我们上面考虑了 ``ℝ → ℝ`` 的情况，但现在让我们考虑一般情况 ``Π i, X i`` ，其中 ``ι : Type*`` 且 ``X ： ι → Type*`` 。我们希望对于任何拓扑空间 ``Z`` 以及任何函数 ``f ： Z → Π i， X i`` ， ``f`` 是连续的当且仅当 ``(fun x ↦ x i) ∘ f`` 对于所有 ``i`` 都是连续的。
让我们在纸上用符号 ``p_i`` 表示投影 ``(fun (x ： Π i， X i) ↦ x i)`` 来探究这个约束条件：

.. math::
  (∀ i, p_i ∘ f \text{ continuous}) &⇔ ∀ i, (p_i ∘ f)_* T_Z ≤ T_{X_i} \\
  &⇔ ∀ i, (p_i)_* f_* T_Z ≤ T_{X_i}\\
  &⇔ ∀ i, f_* T_Z ≤ (p_i)^*T_{X_i}\\
  &⇔  f_* T_Z ≤ \inf \left[(p_i)^*T_{X_i}\right]

因此我们看到，对于 ``Π i, X i`` ，我们想要的拓扑结构是什么：
BOTH: -/
-- QUOTE:
example (ι : Type*) (X : ι → Type*) (T_X : ∀ i, TopologicalSpace (X i)) :
    (Pi.topologicalSpace : TopologicalSpace (∀ i, X i)) =
      ⨅ i, TopologicalSpace.induced (fun x ↦ x i) (T_X i) :=
  rfl
-- QUOTE.

/- TEXT:
这就结束了我们关于 Mathlib 的探讨，其如何认为拓扑空间通过成为更具函子性的理论与对于任何固定类型都具有完备格结构的特性，从而弥补度量空间理论的缺陷。

分离性与可数性
^^^^^^^^^^^^^


我们看到拓扑空间范畴具有非常良好的性质。为此付出的代价是存在一些相当病态的拓扑空间。
你可以对拓扑空间做出一些假设，以确保其行为更接近度量空间。其中最重要的是 ``T2 空间`` ，也称为“豪斯多夫空间”，它能确保极限是唯一的。
更强的分离性质是 ``T3 空间`` ，它还确保了 ``正则空间`` 性质：每个点都有一个闭邻域基。

BOTH: -/
-- QUOTE:
example [TopologicalSpace X] [T2Space X] {u : ℕ → X} {a b : X} (ha : Tendsto u atTop (𝓝 a))
    (hb : Tendsto u atTop (𝓝 b)) : a = b :=
  tendsto_nhds_unique ha hb

example [TopologicalSpace X] [RegularSpace X] (a : X) :
    (𝓝 a).HasBasis (fun s : Set X ↦ s ∈ 𝓝 a ∧ IsClosed s) id :=
  closed_nhds_basis a
-- QUOTE.

/- TEXT:
请注意，根据定义，在每个拓扑空间中，每个点都有一个开邻域基。
BOTH: -/
-- QUOTE:
example [TopologicalSpace X] {x : X} :
    (𝓝 x).HasBasis (fun t : Set X ↦ t ∈ 𝓝 x ∧ IsOpen t) id :=
  nhds_basis_opens' x
-- QUOTE.

/- TEXT:
我们现在的主要目标是证明基本定理，该定理允许通过连续性进行延拓。从布尔巴基学派的《一般拓扑学》一书，第 I 卷第 8.5 节，定理 1（仅取非平凡的蕴含部分）：

设 :math:`X` 为拓扑空间，:math:`A` 是 :math:`X` 的一个稠密子集，:math:`f : A → Y` 是将 :math:`A` 映射到 :math:`T_3` 空间 :math:`Y` 的连续映射。若对于 :math:`X` 中的每个点 :math:`x` ，当 :math:`y` 趋近于 :math:`x` 且始终处于 :math:`A` 内时，:math:`f(y)` 在 :math:`Y` 中趋于一个极限，则存在 :math:`f` 在 :math:`X` 上的连续延拓 :math:`φ` 。

实际上，Mathlib 包含了上述引理的一个更通用的版本 ``DenseInducing.continuousAt_extend`` ，但在这里我们将遵循布尔巴基的版本。

请记住，对于 ``A : Set X`` ， ``↥A``  是与 ``A`` 相关联的子类型，并且在需要时，Lean 会自动插入那个有趣的上箭头。而（包含）强制转换映射为 ``(↑) : A → X`` 。假设“趋向于 :math:`x` 且始终处于 :math:`A` 中”对应于拉回滤子 ``comap (↑) (𝓝 x)`` 。

我们首先证明一个辅助引理，将其提取出来以简化上下文（特别是这里我们不需要 Y 是拓扑空间）。
BOTH: -/
-- QUOTE:
theorem aux {X Y A : Type*} [TopologicalSpace X] {c : A → X}
      {f : A → Y} {x : X} {F : Filter Y}
      (h : Tendsto f (comap c (𝓝 x)) F) {V' : Set Y} (V'_in : V' ∈ F) :
    ∃ V ∈ 𝓝 x, IsOpen V ∧ c ⁻¹' V ⊆ f ⁻¹' V' := by
/- EXAMPLES:
  sorry

SOLUTIONS: -/
  simpa [and_assoc] using ((nhds_basis_opens' x).comap c).tendsto_left_iff.mp h V' V'_in
-- QUOTE.

/- TEXT:
现在让我们来证明连续性延拓定理的主要内容。

当需要在 ``↥A`` 上定义拓扑时，Lean 会自动使用诱导拓扑。
唯一相关的引理是
  ``nhds_induced (↑) : ∀ a ： ↥A， 𝓝 a = comap (↑) (𝓝 ↑a)``
（这实际上是一个关于诱导拓扑的一般引理）。

证明的大致思路是：

主要假设和选择公理给出一个函数 ``φ`` ，使得
  ``∀ x, Tendsto f (comap (↑) (𝓝 x)) (𝓝 (φ x))``
（因为 ``Y`` 是豪斯多夫空间， ``φ`` 是完全确定的，但在我们试图证明 ``φ`` 确实扩展了 ``f`` 之前，我们不需要这一点）。

首先证明 ``φ`` 是连续的。固定任意的 ``x : X`` 。
由于 ``Y`` 是正则的，只需检查对于 ``φ x`` 的每个 **闭** 邻域 ``V'`` ， ``φ⁻¹' V' ∈ 𝓝 x`` 。
极限假设（通过上面的辅助引理）给出了某个 ``V ∈ 𝓝 x`` ，使得 ``IsOpen V ∧ (↑)⁻¹' V ⊆ f⁻¹' V'`` 。
由于 ``V ∈ 𝓝 x`` ，只需证明 ``V ⊆ φ⁻¹' V'`` ，即 ``∀ y ∈ V， φ y ∈ V'`` 。
固定 ``V`` 中的 ``y`` 。因为 ``V`` 是 **开** 的，所以它是 ``y`` 的邻域。
特别是 ``(↑)⁻¹' V ∈ comap (↑) (𝓝 y)`` 且更进一步 ``f⁻¹' V' ∈ comap (↑) (𝓝 y)`` 。
此外， ``comap (↑) (𝓝 y) ≠ ⊥`` 因为 ``A`` 是稠密的。
因为我们知道 ``Tendsto f (comap (↑) (𝓝 y)) (𝓝 (φ y))`` ，这表明 ``φ y ∈ closure V'`` ，并且由于 ``V'`` 是闭的，我们已经证明了 ``φ y ∈ V'`` 。

接下来要证明的是 ``φ`` 延拓了 ``f`` 。这里就要用到 ``f`` 的连续性以及 ``Y`` 是豪斯多夫空间这一事实。
BOTH: -/
-- QUOTE:
example [TopologicalSpace X] [TopologicalSpace Y] [T3Space Y] {A : Set X}
    (hA : ∀ x, x ∈ closure A) {f : A → Y} (f_cont : Continuous f)
    (hf : ∀ x : X, ∃ c : Y, Tendsto f (comap (↑) (𝓝 x)) (𝓝 c)) :
    ∃ φ : X → Y, Continuous φ ∧ ∀ a : A, φ a = f a := by
/- EXAMPLES:
  sorry

#check HasBasis.tendsto_right_iff

SOLUTIONS: -/
  choose φ hφ using hf
  use φ
  constructor
  · rw [continuous_iff_continuousAt]
    intro x
    suffices ∀ V' ∈ 𝓝 (φ x), IsClosed V' → φ ⁻¹' V' ∈ 𝓝 x by
      simpa [ContinuousAt, (closed_nhds_basis (φ x)).tendsto_right_iff]
    intro V' V'_in V'_closed
    obtain ⟨V, V_in, V_op, hV⟩ : ∃ V ∈ 𝓝 x, IsOpen V ∧ (↑) ⁻¹' V ⊆ f ⁻¹' V' := aux (hφ x) V'_in
    suffices : ∀ y ∈ V, φ y ∈ V'
    exact mem_of_superset V_in this
    intro y y_in
    have hVx : V ∈ 𝓝 y := V_op.mem_nhds y_in
    haveI : (comap ((↑) : A → X) (𝓝 y)).NeBot := by simpa [mem_closure_iff_comap_neBot] using hA y
    apply V'_closed.mem_of_tendsto (hφ y)
    exact mem_of_superset (preimage_mem_comap hVx) hV
  · intro a
    have lim : Tendsto f (𝓝 a) (𝓝 (φ a)) := by simpa [nhds_induced] using hφ a
    exact tendsto_nhds_unique lim f_cont.continuousAt
-- QUOTE.

/- TEXT:
除了分离性之外，您还可以对拓扑空间做出的主要假设是可数性假设，以使其更接近度量空间。其中最主要的是第一可数性，即要求每个点都有一个可数的邻域基。特别是，这确保了集合的闭包可以通过序列来理解。

BOTH: -/
-- QUOTE:
example [TopologicalSpace X] [FirstCountableTopology X]
      {s : Set X} {a : X} :
    a ∈ closure s ↔ ∃ u : ℕ → X, (∀ n, u n ∈ s) ∧ Tendsto u atTop (𝓝 a) :=
  mem_closure_iff_seq_limit
-- QUOTE.

/- TEXT:
紧致性
^^^^^


现在让我们来讨论一下拓扑空间的紧致性是如何定义的。和往常一样，对此有多种思考方式，而 Mathlib 采用的是滤子版本。

我们首先需要定义滤子的聚点。给定拓扑空间 ``X`` 上的一个滤子 ``F`` ，若将 ``F`` 视为广义集合，则点 ``x : X`` 是 ``F`` 的聚点，当且仅当 ``F`` 与广义集合中所有接近 ``x`` 的点的集合有非空交集。

那么我们就可以说，集合 ``s`` 是紧致的，当且仅当包含于 ``s`` 中的每一个非空广义集合 ``F`` ，即满足 ``F ≤ 𝓟 s`` 的集合，都在 ``s`` 中有一个聚点。

BOTH: -/
-- QUOTE:
variable [TopologicalSpace X]

example {F : Filter X} {x : X} : ClusterPt x F ↔ NeBot (𝓝 x ⊓ F) :=
  Iff.rfl

example {s : Set X} :
    IsCompact s ↔ ∀ (F : Filter X) [NeBot F], F ≤ 𝓟 s → ∃ a ∈ s, ClusterPt a F :=
  Iff.rfl
-- QUOTE.

/- TEXT:
例如，如果 ``F`` 是  ``map u atTop`` ，即 ``u ： ℕ → X`` 在 ``atTop`` 下的像，其中 ``atTop`` 是非常大的自然数的广义集合，那么假设 ``F ≤ 𝓟 s`` 意味着对于足够大的  ``n`` ， ``u n``  属于  ``s`` 。说 ``x`` 是 ``map u atTop`` 的聚点意味着非常大的数的像与接近 ``x`` 的点的集合相交。如果 ``𝓝 x`` 有一个可数基，我们可以将其解释为说 ``u`` 有一个子序列收敛于  ``x`` ，这样我们就得到了度量空间中紧致性的样子。
BOTH: -/
-- QUOTE:
example [FirstCountableTopology X] {s : Set X} {u : ℕ → X} (hs : IsCompact s)
    (hu : ∀ n, u n ∈ s) : ∃ a ∈ s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 a) :=
  hs.tendsto_subseq hu
-- QUOTE.

/- TEXT:
聚点与连续函数的性质相容。
BOTH: -/
-- QUOTE:
variable [TopologicalSpace Y]

example {x : X} {F : Filter X} {G : Filter Y} (H : ClusterPt x F) {f : X → Y}
    (hfx : ContinuousAt f x) (hf : Tendsto f F G) : ClusterPt (f x) G :=
  ClusterPt.map H hfx hf
-- QUOTE.

/- TEXT:
作为练习，我们将证明连续映射下的紧集的像是紧集。除了我们已经看到的内容外，您还应该使用 ``Filter.push_pull`` 和 ``NeBot.of_map`` 。
BOTH: -/
-- QUOTE:
-- EXAMPLES:
example [TopologicalSpace Y] {f : X → Y} (hf : Continuous f) {s : Set X} (hs : IsCompact s) :
    IsCompact (f '' s) := by
  intro F F_ne F_le
  have map_eq : map f (𝓟 s ⊓ comap f F) = 𝓟 (f '' s) ⊓ F := by sorry
  have Hne : (𝓟 s ⊓ comap f F).NeBot := by sorry
  have Hle : 𝓟 s ⊓ comap f F ≤ 𝓟 s := inf_le_left
  sorry
-- QUOTE.

-- SOLUTIONS:
example [TopologicalSpace Y] {f : X → Y} (hf : Continuous f) {s : Set X} (hs : IsCompact s) :
    IsCompact (f '' s) := by
  intro F F_ne F_le
  have map_eq : map f (𝓟 s ⊓ comap f F) = 𝓟 (f '' s) ⊓ F := by rw [Filter.push_pull, map_principal]
  have Hne : (𝓟 s ⊓ comap f F).NeBot := by
    apply NeBot.of_map
    rwa [map_eq, inf_of_le_right F_le]
  have Hle : 𝓟 s ⊓ comap f F ≤ 𝓟 s := inf_le_left
  rcases hs Hle with ⟨x, x_in, hx⟩
  refine ⟨f x, mem_image_of_mem f x_in, ?_⟩
  apply hx.map hf.continuousAt
  rw [Tendsto, map_eq]
  exact inf_le_right

/- TEXT:
也可以用开覆盖来表述紧性： ``s`` 是紧的，当且仅当覆盖 ``s`` 的每一个开集族都有一个有限的覆盖子族。
BOTH: -/
-- QUOTE:
example {ι : Type*} {s : Set X} (hs : IsCompact s) (U : ι → Set X) (hUo : ∀ i, IsOpen (U i))
    (hsU : s ⊆ ⋃ i, U i) : ∃ t : Finset ι, s ⊆ ⋃ i ∈ t, U i :=
  hs.elim_finite_subcover U hUo hsU
-- QUOTE.
