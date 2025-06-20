import MIL.Common
import Mathlib.Topology.Instances.Real

open Set Filter Topology

/- TEXT:
.. index:: Filter

.. _filters:

滤子
-------


类型 ``X`` 上的 **滤子** 是 ``X`` 的集合的集合，满足以下三个条件（我们将在下面详细说明）。该概念支持两个相关的想法：

* **极限** ，包括上述讨论过的各种极限：数列的有限极限和无穷极限、函数在某点或无穷远处的有限极限和无穷极限等等。

* **最终发生的事情** ，包括对于足够大的自然数 ``n : ℕ`` 发生的事情，或者在某一点 ``x`` 足够近的地方发生的事情，或者对于足够接近的点对发生的事情，或者在测度论意义上几乎处处发生的事情。对偶地，滤子也可以表达 **经常发生的事情** 的概念：对于任意大的 ``n`` ，在给定点的任意邻域内存在某点发生，等等。

与这些描述相对应的滤子将在本节稍后定义，但我们现在就可以给它们命名：

*  ``(atTop : Filter ℕ)`` ，由包含 ``{n | n ≥ N}`` 的 ``ℕ`` 的集合构成，其中 ``N`` 为某个自然数
*  ``𝓝 x`` ，由拓扑空间中 ``x`` 的邻域构成
*  ``𝓤 X`` ，由一致空间的邻域基构成（一致空间推广了度量空间和拓扑群）
*  ``μ.ae`` ，由相对于测度 ``μ`` 其补集测度为零的集合构成

一般的定义如下：一个滤子 ``F : Filter X`` 是集合 ``F.sets : Set (Set X)`` 的一个集合，满足以下条件：

*  ``F.univ_sets : univ ∈ F.sets``
*  ``F.sets_of_superset : ∀ {U V}, U ∈ F.sets → U ⊆ V → V ∈ F.sets``
*  ``F.inter_sets : ∀ {U V}, U ∈ F.sets → V ∈ F.sets → U ∩ V ∈ F.sets``

第一个条件表明，集合 ``X`` 的所有元素都属于  ``F.sets`` 。
第二个条件表明，如果 ``U`` 属于  ``F.sets`` ，那么包含 ``U`` 的任何集合也属于  ``F.sets`` 。
第三个条件表明， ``F.sets``  对有限交集是封闭的。
在 Mathlib 中，滤子 ``F`` 被定义为捆绑 ``F.sets`` 及其三个属性的结构，但这些属性不携带额外的数据，并且将 ``F`` 和 ``F.sets`` 之间的区别模糊化是方便的。我们
因此，将 ``U ∈ F`` 定义为 ``U ∈ F.sets`` 。
这就解释了为什么在一些提及 ``U ∈ F`` 的引理名称中会出现 ``sets`` 这个词。

可以将滤子视为定义“足够大”集合的概念。第一个条件表明 ``univ`` 是足够大的集合，第二个条件表明包含足够大集合的集合也是足够大的集合，第三个条件表明两个足够大集合的交集也是足够大的集合。

将类型 ``X`` 上的一个滤子视为 ``Set X`` 的广义元素，可能更有用。例如， ``atTop``  是“极大数的集合”，而 ``𝓝 x₀`` 是“非常接近 ``x₀`` 的点的集合”。这种观点的一种体现是，我们可以将任何 ``s : Set X`` 与所谓的“主滤子”相关联，该主滤子由包含 ``s`` 的所有集合组成。
此定义已在 Mathlib 中，并有一个记号 ``𝓟`` （在 ``Filter`` 命名空间中本地化）。为了演示的目的，我们请您借此机会在此处推导出该定义。
EXAMPLES: -/
-- QUOTE:
def principal {α : Type*} (s : Set α) : Filter α
    where
  sets := { t | s ⊆ t }
  univ_sets := sorry
  sets_of_superset := sorry
  inter_sets := sorry
-- QUOTE.

-- SOLUTIONS:
-- 在下一个示例中，我们可以在每个证明中使用 `tauto` 而不是记住这些引理
example {α : Type*} (s : Set α) : Filter α :=
  { sets := { t | s ⊆ t }
    univ_sets := subset_univ s
    sets_of_superset := fun hU hUV ↦ Subset.trans hU hUV
    inter_sets := fun hU hV ↦ subset_inter hU hV }

/- TEXT:
对于我们的第二个示例，我们请您定义滤子 ``atTop : Filter ℕ`` （我们也可以使用任何具有预序关系的类型来代替  ``ℕ`` ）
EXAMPLES: -/
-- QUOTE:
example : Filter ℕ :=
  { sets := { s | ∃ a, ∀ b, a ≤ b → b ∈ s }
    univ_sets := sorry
    sets_of_superset := sorry
    inter_sets := sorry }
-- QUOTE.

-- SOLUTIONS:
example : Filter ℕ :=
  { sets := { s | ∃ a, ∀ b, a ≤ b → b ∈ s }
    univ_sets := by
      use 42
      simp
    sets_of_superset := by
      rintro U V ⟨N, hN⟩ hUV
      use N
      tauto
    inter_sets := by
      rintro U V ⟨N, hN⟩ ⟨N', hN'⟩
      use max N N'
      intro b hb
      rw [max_le_iff] at hb
      constructor <;> tauto }

/- TEXT:
我们还可以直接定义任意实数 ``x : ℝ`` 的邻域滤子 ``𝓝 x`` 。在实数中， ``x``  的邻域是一个包含开区间 :math:`(x_0 - \varepsilon, x_0 + \varepsilon)` 的集合，在 Mathlib 中定义为 ``Ioo (x₀ - ε) (x₀ + ε)`` 。（Mathlib 中的这种邻域概念只是更一般构造的一个特例。）

有了这些例子，我们就可以定义函数 ``f : X → Y`` 沿着某个 ``F : Filter X`` 收敛到某个 ``G : Filter Y`` 的含义，如下所述：
BOTH: -/
-- QUOTE:
def Tendsto₁ {X Y : Type*} (f : X → Y) (F : Filter X) (G : Filter Y) :=
  ∀ V ∈ G, f ⁻¹' V ∈ F
-- QUOTE.

/- TEXT:
当 ``X`` 为 ``ℕ`` 且 ``Y`` 为 ``ℝ`` 时， ``Tendsto₁ u atTop (𝓝 x)``  等价于说序列 ``u : ℕ → ℝ`` 收敛于实数 ``x`` 。当 ``X`` 和 ``Y`` 均为 ``ℝ`` 时， ``Tendsto f (𝓝 x₀) (𝓝 y₀)`` 等价于熟悉的概念 :math:`\lim_{x \to x₀} f(x) = y₀` 。介绍中提到的所有其他类型的极限也等价于对源和目标上适当选择的滤子的 ``Tendsto₁`` 的实例。

上述的 ``Tendsto₁`` 概念在定义上等同于在 Mathlib 中定义的 ``Tendsto`` 概念，但后者定义得更为抽象。 ``Tendsto₁`` 的定义存在的问题是它暴露了量词和 ``G`` 的元素，并且掩盖了通过将滤子视为广义集合所获得的直观理解。我们可以通过使用更多的代数和集合论工具来隐藏量词 ``∀ V`` ，并使这种直观理解更加突出。第一个要素是与任何映射 ``f : X → Y`` 相关的 **前推** 操作 :math:`f_*`，在 Mathlib 中记为 ``Filter.map f`` 。给定 ``X`` 上的滤子 ``F`` ， ``Filter.map f F : Filter Y`` 被定义为使得 ``V ∈ Filter.map f F ↔ f ⁻¹' V ∈ F`` 成立。在这个示例文件中，我们已经打开了 ``Filter`` 命名空间，因此 ``Filter.map`` 可以写成 ``map`` 。这意味着我们可以使用 ``Filter Y`` 上的序关系来重写 ``Tendsto`` 的定义，该序关系是成员集合的反向包含关系。换句话说，给定 ``G H : Filter Y`` ，我们有 ``G ≤ H ↔ ∀ V : Set Y， V ∈ H → V ∈ G`` 。
EXAMPLES: -/
-- QUOTE:
def Tendsto₂ {X Y : Type*} (f : X → Y) (F : Filter X) (G : Filter Y) :=
  map f F ≤ G

example {X Y : Type*} (f : X → Y) (F : Filter X) (G : Filter Y) :
    Tendsto₂ f F G ↔ Tendsto₁ f F G :=
  Iff.rfl
-- QUOTE.

/- TEXT:
可能看起来滤子上的序关系是反向的。但请回想一下，我们可以通过将任何集合 ``s`` 映射到相应的主滤子的 ``𝓟 : Set X → Filter X`` 的包含关系，将 ``X`` 上的滤子视为 ``Set X`` 的广义元素。这种包含关系是保序的，因此 ``Filter`` 上的序关系确实可以被视为广义集合之间的自然包含关系。在这个类比中，前推类似于直接像（direct image）。而且，确实有  ``map f (𝓟 s) = 𝓟 (f '' s)`` 。

现在我们可以直观地理解为什么一个序列 ``u : ℕ → ℝ`` 收敛于点 ``x₀`` 当且仅当 ``map u atTop ≤ 𝓝 x₀`` 成立。这个不等式意味着在 “ ``u``  作用下”的“非常大的自然数集合”的“直接像”包含在“非常接近 ``x₀`` 的点的集合”中。

正如所承诺的那样， ``Tendsto₂``  的定义中没有任何量词或集合。
它还利用了前推操作的代数性质。
首先，每个 ``Filter.map f`` 都是单调的。其次， ``Filter.map``  与复合运算兼容。
EXAMPLES: -/
-- QUOTE:
#check (@Filter.map_mono : ∀ {α β} {m : α → β}, Monotone (map m))

#check
  (@Filter.map_map :
    ∀ {α β γ} {f : Filter α} {m : α → β} {m' : β → γ}, map m' (map m f) = map (m' ∘ m) f)
-- QUOTE.

/- TEXT:
这两个性质结合起来使我们能够证明极限的复合性，从而一次性得出引言中描述的 256 种组合引理变体，以及更多。
您可以使用 ``Tendsto₁`` 的全称量词定义或代数定义，连同上述两个引理，来练习证明以下陈述。
EXAMPLES: -/
-- QUOTE:
example {X Y Z : Type*} {F : Filter X} {G : Filter Y} {H : Filter Z} {f : X → Y} {g : Y → Z}
    (hf : Tendsto₁ f F G) (hg : Tendsto₁ g G H) : Tendsto₁ (g ∘ f) F H :=
  sorry
-- QUOTE.

-- SOLUTIONS:
example {X Y Z : Type*} {F : Filter X} {G : Filter Y} {H : Filter Z} {f : X → Y} {g : Y → Z}
    (hf : Tendsto₁ f F G) (hg : Tendsto₁ g G H) : Tendsto₁ (g ∘ f) F H :=
  calc
    map (g ∘ f) F = map g (map f F) := by rw [map_map]
    _ ≤ map g G := (map_mono hf)
    _ ≤ H := hg


example {X Y Z : Type*} {F : Filter X} {G : Filter Y} {H : Filter Z} {f : X → Y} {g : Y → Z}
    (hf : Tendsto₁ f F G) (hg : Tendsto₁ g G H) : Tendsto₁ (g ∘ f) F H := by
  intro V hV
  rw [preimage_comp]
  apply hf
  apply hg
  exact hV

/- TEXT:
前推构造使用一个映射将滤子从映射源推送到映射目标。
还有一个“拉回”操作，即 ``Filter.comap`` ，其方向相反。
这推广了集合上的原像操作。对于任何映射 ``f`` ，
 ``Filter.map f``  和 ``Filter.comap f`` 构成了所谓的 **伽罗瓦连接** ，也就是说，它们满足

 ``filter.map_le_iff_le_comap`` : ``f``  映射下的 ``F`` 小于等于 ``G`` 当且仅当 ``F`` 小于等于 ``G`` 在 ``f`` 下的逆像。

对于每一个 ``F`` 和 ``G`` 。
此操作可用于提供“Tendsto”的另一种表述形式，该形式可证明（但不是定义上）等同于 Mathlib 中的那个。

 ``comap``  操作可用于将滤子限制在子类型上。例如，假设我们有  ``f : ℝ → ℝ`` 、 ``x₀ : ℝ``  和  ``y₀ : ℝ`` ，并且假设我们想要说明当 ``x`` 在有理数范围内趋近于 ``x₀`` 时， ``f x``  趋近于  ``y₀`` 。我们可以使用强制转换映射 ``(↑) : ℚ → ℝ`` 将滤子 ``𝓝 x₀`` 拉回到  ``ℚ`` ，并声明  ``Tendsto (f ∘ (↑) : ℚ → ℝ) (comap (↑) (𝓝 x₀)) (𝓝 y₀)`` 。
EXAMPLES: -/
-- QUOTE:
variable (f : ℝ → ℝ) (x₀ y₀ : ℝ)

#check comap ((↑) : ℚ → ℝ) (𝓝 x₀)

#check Tendsto (f ∘ (↑)) (comap ((↑) : ℚ → ℝ) (𝓝 x₀)) (𝓝 y₀)
-- QUOTE.

/- TEXT:
拉回操作也与复合运算兼容，但它具有 **逆变性** ，也就是说，它会颠倒参数的顺序。
EXAMPLES: -/
-- QUOTE:
section
variable {α β γ : Type*} (F : Filter α) {m : γ → β} {n : β → α}

#check (comap_comap : comap m (comap n F) = comap (n ∘ m) F)

end
-- QUOTE.

/- TEXT:
现在让我们将注意力转向平面 ``ℝ × ℝ`` ，并尝试理解点 ``(x₀， y₀)`` 的邻域与 ``𝓝 x₀`` 和 ``𝓝 y₀`` 之间的关系。
存在一个乘积运算 ``Filter.prod : Filter X → Filter Y → Filter (X × Y)`` ，记作 ``×ˢ`` ，它回答了这个问题：
EXAMPLES: -/
-- QUOTE:
example : 𝓝 (x₀, y₀) = 𝓝 x₀ ×ˢ 𝓝 y₀ :=
  nhds_prod_eq
-- QUOTE.

/- TEXT:
该乘积运算通过拉回运算和 ``inf`` 运算来定义：

 ``F ×ˢ G = (comap Prod.fst F) ⊓ (comap Prod.snd G)``

这里的 ``inf`` 操作指的是对于任何类型 X 的 ``Filter X`` 上的格结构，其中 ``F ⊓ G`` 是小于 ``F`` 和 ``G`` 的最大滤子。
因此， ``inf`` 操作推广了集合交集的概念。

在 Mathlib 中的许多证明都使用了上述所有结构（ ``map`` 、 ``comap`` 、 ``inf`` 、 ``sup``  和  ``prod`` ），从而给出关于收敛性的代数证明，而无需提及滤子的成员。您可以在以下引理的证明中练习这样做，如果需要，可以展开 ``Tendsto`` 和 ``Filter.prod`` 的定义。
EXAMPLES: -/
-- QUOTE:
#check le_inf_iff

example (f : ℕ → ℝ × ℝ) (x₀ y₀ : ℝ) :
    Tendsto f atTop (𝓝 (x₀, y₀)) ↔
      Tendsto (Prod.fst ∘ f) atTop (𝓝 x₀) ∧ Tendsto (Prod.snd ∘ f) atTop (𝓝 y₀) :=
  sorry
-- QUOTE.

-- SOLUTIONS:
example (f : ℕ → ℝ × ℝ) (x₀ y₀ : ℝ) :
    Tendsto f atTop (𝓝 (x₀, y₀)) ↔
      Tendsto (Prod.fst ∘ f) atTop (𝓝 x₀) ∧ Tendsto (Prod.snd ∘ f) atTop (𝓝 y₀) :=
  calc
    Tendsto f atTop (𝓝 (x₀, y₀)) ↔ map f atTop ≤ 𝓝 (x₀, y₀) := Iff.rfl
    _ ↔ map f atTop ≤ 𝓝 x₀ ×ˢ 𝓝 y₀ := by rw [nhds_prod_eq]
    _ ↔ map f atTop ≤ comap Prod.fst (𝓝 x₀) ⊓ comap Prod.snd (𝓝 y₀) := Iff.rfl
    _ ↔ map f atTop ≤ comap Prod.fst (𝓝 x₀) ∧ map f atTop ≤ comap Prod.snd (𝓝 y₀) := le_inf_iff
    _ ↔ map Prod.fst (map f atTop) ≤ 𝓝 x₀ ∧ map Prod.snd (map f atTop) ≤ 𝓝 y₀ := by
      rw [← map_le_iff_le_comap, ← map_le_iff_le_comap]
    _ ↔ map (Prod.fst ∘ f) atTop ≤ 𝓝 x₀ ∧ map (Prod.snd ∘ f) atTop ≤ 𝓝 y₀ := by
      rw [map_map, map_map]


-- -- an alternative solution

-- 一种备选方案
example (f : ℕ → ℝ × ℝ) (x₀ y₀ : ℝ) :
    Tendsto f atTop (𝓝 (x₀, y₀)) ↔
      Tendsto (Prod.fst ∘ f) atTop (𝓝 x₀) ∧ Tendsto (Prod.snd ∘ f) atTop (𝓝 y₀) := by
  rw [nhds_prod_eq]
  unfold Tendsto SProd.sprod Filter.instSProd Filter.prod
  rw [le_inf_iff, ← map_le_iff_le_comap, map_map, ← map_le_iff_le_comap, map_map]

/- TEXT:
有序类型 ``Filter X`` 实际上是一个 **完备** 格，也就是说，存在一个最小元素，存在一个最大元素，并且 X 上的每个滤子集都有一个 ``Inf`` 和一个 ``Sup`` 。

请注意，根据滤子定义中的第二个性质（如果 ``U`` 属于 ``F`` ，那么任何包含 ``U`` 的集合也属于 ``F`` ），第一个性质（ ``X`` 的所有元素组成的集合属于 ``F`` ）等价于 ``F`` 不是空集合这一性质。这不应与更微妙的问题相混淆，即空集是否为 ``F`` 的一个 **元素** 。滤子的定义并不禁止 ``∅ ∈ F`` ，但如果空集在 ``F`` 中，那么每个集合都在 ``F`` 中，也就是说， ``∀ U : Set X, U ∈ F`` 。在这种情况下， ``F`` 是一个相当平凡的滤子，恰好是完备格 ``Filter X`` 的最小元素。这与布尔巴基对滤子的定义形成对比，布尔巴基的定义不允许滤子包含空集。

由于我们在定义中包含了平凡滤子，所以在某些引理中有时需要明确假设非平凡性。不过作为回报，该理论具有更优的整体性质。我们已经看到，包含平凡滤子为我们提供了一个最小元素。它还允许我们定义 ``principal : Set X → Filter X`` ，将 ``∅`` 映射到 ``⊥`` ，而无需添加预条件来排除空集。而且它还允许我们定义拉回操作时无需预条件。实际上，有可能 ``comap f F = ⊥`` 尽管 ``F ≠ ⊥`` 。例如，给定 ``x₀ : ℝ`` 和 ``s : Set ℝ`` ， ``𝓝 x₀`` 在从与 ``s`` 对应的子类型强制转换下的拉回非平凡当且仅当 ``x₀`` 属于 ``s`` 的闭包。

为了管理确实需要假设某些滤子非平凡的引理，Mathlib 设有类型类 ``Filter.NeBot`` ，并且库中存在假设 ``（F : Filter X）[F.NeBot]`` 的引理。实例数据库知道，例如， ``(atTop : Filter ℕ).NeBot`` ，并且知道将非平凡滤子向前推进会得到一个非平凡滤子。因此，假设 ``[F.NeBot]`` 的引理将自动应用于任何序列 ``u`` 的 ``map u atTop`` 。

我们对滤子的代数性质及其与极限的关系的探讨基本上已经完成，但我们尚未证明我们所提出的重新捕捉通常极限概念的主张是合理的。
表面上看， ``Tendsto u atTop (𝓝 x₀)`` 似乎比在 :numref: ``sequences_and_convergence``  中定义的收敛概念更强，因为我们要求 ``x₀`` 的 **每个** 邻域都有一个属于 ``atTop`` 的原像，而通常的定义仅要求对于标准邻域 ``Ioo (x₀ - ε) (x₀ + ε)`` 满足这一条件。关键在于，根据定义，每个邻域都包含这样的标准邻域。这一观察引出了 **滤子基（filter basis）** 的概念。

给定 ``F : Filter X`` ，如果对于每个集合 ``U`` ，我们有 ``U ∈ F`` 当且仅当它包含某个 ``s i`` ，那么集合族 ``s : ι → Set X`` 就是 ``F`` 的基。
换句话说，严格说来， ``s`` 是基当且仅当它满足 ``∀ U : Set X, U ∈ F ↔ ∃ i, s i ⊆ U`` 。考虑在索引类型中仅选择某些值 ``i`` 的 ``ι`` 上的谓词会更加灵活。
对于 ``𝓝 x₀`` ，我们希望 ``ι`` 为 ``ℝ`` ，用 ``ε`` 表示 ``i`` ，并且谓词应选择 ``ε`` 的正值。因此，集合 ``Ioo (x₀ - ε) (x₀ + ε)`` 构成 ``ℝ`` 上邻域拓扑的基这一事实可表述如下：
EXAMPLES: -/
-- QUOTE:
example (x₀ : ℝ) : HasBasis (𝓝 x₀) (fun ε : ℝ ↦ 0 < ε) fun ε ↦ Ioo (x₀ - ε) (x₀ + ε) :=
  nhds_basis_Ioo_pos x₀
-- QUOTE.

/- TEXT:
还有一个很好的 ``atTop`` 滤子的基础。引理 ``Filter.HasBasis.tendsto_iff`` 允许我们在给定 ``F`` 和 ``G`` 的基础的情况下，重新表述形式为 ``Tendsto f F G`` 的陈述。将这些部分组合在一起，就基本上得到了我们在 :numref: ``sequences_and_convergence``  中使用的收敛概念。
EXAMPLES: -/
-- QUOTE:
example (u : ℕ → ℝ) (x₀ : ℝ) :
    Tendsto u atTop (𝓝 x₀) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, u n ∈ Ioo (x₀ - ε) (x₀ + ε) := by
  have : atTop.HasBasis (fun _ : ℕ ↦ True) Ici := atTop_basis
  rw [this.tendsto_iff (nhds_basis_Ioo_pos x₀)]
  simp
-- QUOTE.

/- TEXT:

现在我们展示一下滤子如何有助于处理对于足够大的数字或对于给定点足够近的点成立的性质。在 :numref:`sequences_and_convergence` 中，我们经常遇到这样的情况：我们知道某个性质 ``P n`` 对于足够大的 ``n`` 成立，而另一个性质 ``Q n`` 对于足够大的 ``n`` 也成立。使用两次 ``cases`` 得到了满足 ``∀ n ≥ N_P， P n`` 和 ``∀ n ≥ N_Q， Q n`` 的 ``N_P`` 和  ``N_Q`` 。通过  ``set N := max N_P N_Q`` ，我们最终能够证明  ``∀ n ≥ N， P n ∧ Q n`` 。反复这样做会让人感到厌烦。

我们可以通过注意到“对于足够大的 n， ``P n``  和 ``Q n`` 成立”这一表述意味着我们有 ``{n | P n} ∈ atTop`` 和 ``{n | Q n} ∈ atTop`` 来做得更好。由于 ``atTop`` 是一个滤子，所以 ``atTop`` 中两个元素的交集仍在 ``atTop`` 中，因此我们有  ``{n | P n ∧ Q n} ∈ atTop`` 。书写 ``{n | P n} ∈ atTop`` 不太美观，但我们可以用更具提示性的记号  ``∀ᶠ n in atTop， P n`` 。这里的上标 ``f`` 表示“滤子”。你可以将这个记号理解为对于“非常大的数集”中的所有  ``n`` ， ``P n``  成立。 ``∀ᶠ``  记号代表  ``Filter.Eventually`` ，而引理 ``Filter.Eventually.and`` 利用滤子的交集性质来实现我们刚才所描述的操作：
EXAMPLES: -/
-- QUOTE:
example (P Q : ℕ → Prop) (hP : ∀ᶠ n in atTop, P n) (hQ : ∀ᶠ n in atTop, Q n) :
    ∀ᶠ n in atTop, P n ∧ Q n :=
  hP.and hQ
-- QUOTE.

/- TEXT:

这种表示法如此方便且直观，以至于当 ``P`` 是一个等式或不等式陈述时，我们也有专门的表示形式。例如，设 ``u`` 和 ``v`` 是两个实数序列，让我们证明如果对于足够大的 ``n`` ， ``u n`` 和 ``v n`` 相等，那么 ``u`` 趋向于 ``x₀`` 当且仅当 ``v`` 趋向于 ``x₀`` 。首先我们将使用通用的 ``Eventually`` ，然后使用专门针对等式谓词的 ``EventuallyEq`` 。这两个陈述在定义上是等价的，因此在两种情况下相同的证明都适用。
EXAMPLES: -/
-- QUOTE:
example (u v : ℕ → ℝ) (h : ∀ᶠ n in atTop, u n = v n) (x₀ : ℝ) :
    Tendsto u atTop (𝓝 x₀) ↔ Tendsto v atTop (𝓝 x₀) :=
  tendsto_congr' h

example (u v : ℕ → ℝ) (h : u =ᶠ[atTop] v) (x₀ : ℝ) :
    Tendsto u atTop (𝓝 x₀) ↔ Tendsto v atTop (𝓝 x₀) :=
  tendsto_congr' h
-- QUOTE.

/- TEXT:

从 ``Eventually`` 这一概念的角度来审视滤子的定义是很有启发性的。
给定滤子 ``F : Filter X`` ，对于 ``X`` 上的任意谓词 ``P`` 和 ``Q`` ，

条件 ``univ ∈ F`` 确保了 ``(∀ x, P x) → ∀ᶠ x in F, P x`` ，
条件 ``U ∈ F → U ⊆ V → V ∈ F`` 确保了 ``(∀ᶠ x in F, P x) → (∀ x, P x → Q x) → ∀ᶠ x in F, Q x`` ，并且
条件 ``U ∈ F → V ∈ F → U ∩ V ∈ F`` 确保了 ``(∀ᶠ x in F, P x) → (∀ᶠ x in F, Q x) → ∀ᶠ x in F, P x ∧ Q x`` 。
EXAMPLES: -/
-- QUOTE:
#check Eventually.of_forall
#check Eventually.mono
#check Eventually.and
-- QUOTE.

/- TEXT:

第二个项目，对应于 ``Eventually.mono`` ，支持使用滤子的优雅方式，尤其是与 ``Eventually.and`` 结合使用时。 ``filter_upwards``  策略使我们能够将它们组合起来。比较：
EXAMPLES: -/
-- QUOTE:
example (P Q R : ℕ → Prop) (hP : ∀ᶠ n in atTop, P n) (hQ : ∀ᶠ n in atTop, Q n)
    (hR : ∀ᶠ n in atTop, P n ∧ Q n → R n) : ∀ᶠ n in atTop, R n := by
  apply (hP.and (hQ.and hR)).mono
  rintro n ⟨h, h', h''⟩
  exact h'' ⟨h, h'⟩

example (P Q R : ℕ → Prop) (hP : ∀ᶠ n in atTop, P n) (hQ : ∀ᶠ n in atTop, Q n)
    (hR : ∀ᶠ n in atTop, P n ∧ Q n → R n) : ∀ᶠ n in atTop, R n := by
  filter_upwards [hP, hQ, hR] with n h h' h''
  exact h'' ⟨h, h'⟩
-- QUOTE.

/- TEXT:

熟悉测度论的读者会注意到，补集测度为零的集合构成的滤子 ``μ.ae`` （即“几乎每个点构成的集合”）作为 ``Tendsto`` 的源或目标并不是很有用，但它可以方便地与 ``Eventually`` 一起使用，以表明某个性质对几乎每个点都成立。

存在 ``∀ᶠ x in F, P x`` 的对偶版本，有时会很有用：
用 ``∃ᶠ x in F, P x`` 表示
 ``{x | ¬P x} ∉ F`` 。例如， ``∃ᶠ n in atTop, P n`` 意味着存在任意大的 ``n`` 使得 ``P n`` 成立。
 ``∃ᶠ`` 符号代表 ``Filter.Frequently`` 。

对于一个更复杂的示例，请考虑以下关于序列  ``u`` 、集合 ``M`` 和值 ``x`` 的陈述：

如果序列 ``u`` 收敛于 ``x`` ，且对于足够大的 ``n`` ， ``u n``  属于集合 ``M`` ，那么 ``x`` 就在集合 ``M`` 的闭包内。

这可以形式化表述如下：

   ``Tendsto u atTop (𝓝 x) → (∀ᶠ n in atTop, u n ∈ M) → x ∈ closure M`` .

这是拓扑库中定理 ``mem_closure_of_tendsto`` 的一个特殊情况。
试着利用所引用的引理来证明它，利用 ``ClusterPt x F`` 意味着 ``(𝓝 x ⊓ F).NeBot`` 这一事实，以及根据定义， ``∀ᶠ n in atTop， u n ∈ M`` 这一假设意味着 ``M ∈ map u atTop`` 。
EXAMPLES: -/
-- QUOTE:
#check mem_closure_iff_clusterPt
#check le_principal_iff
#check neBot_of_le

example (u : ℕ → ℝ) (M : Set ℝ) (x : ℝ) (hux : Tendsto u atTop (𝓝 x))
    (huM : ∀ᶠ n in atTop, u n ∈ M) : x ∈ closure M :=
  sorry
-- QUOTE.

-- SOLUTIONS:
example (u : ℕ → ℝ) (M : Set ℝ) (x : ℝ) (hux : Tendsto u atTop (𝓝 x))
    (huM : ∀ᶠ n in atTop, u n ∈ M) : x ∈ closure M :=
  mem_closure_iff_clusterPt.mpr (neBot_of_le <| le_inf hux <| le_principal_iff.mpr huM)
