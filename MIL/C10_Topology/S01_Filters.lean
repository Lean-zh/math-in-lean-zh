import MIL.Common
import Mathlib.Topology.Instances.Real

open Set Filter Topology

/- TEXT:
.. index:: Filter

.. _filters:

-- Filters

滤子
-------

-- A *filter* on a type ``X`` is a collection of sets of ``X`` that satisfies three
-- conditions that we will spell out below. The notion
-- supports two related ideas:

类型 ``X`` 上的 **滤子** 是 ``X`` 的集合的集合，满足以下三个条件（我们将在下面详细说明）。该概念支持两个相关的想法：

-- * *limits*, including all the kinds of limits discussed above: finite and infinite limits of sequences, finite and infinite limits of functions at a point or at infinity, and so on.

* **极限**，包括上述讨论过的各种极限：数列的有限极限和无穷极限、函数在某点或无穷远处的有限极限和无穷极限等等。

-- * *things happening eventually*, including things happening for large enough ``n : ℕ``, or sufficiently near a point ``x``, or for sufficiently close pairs of points, or almost everywhere in the sense of measure theory. Dually, filters can also express the idea of *things happening often*: for arbitrarily large ``n``, at a point in any neighborhood of a given point, etc.

* **最终发生的事情**，包括对于足够大的自然数 ``n ： ℕ`` 发生的事情，或者在某一点 ``x`` 足够近的地方发生的事情，或者对于足够接近的点对发生的事情，或者在测度论意义上几乎处处发生的事情。对偶地，滤子也可以表达**经常发生的事情**的概念：对于任意大的 ``n`` ，在给定点的任意邻域内存在某点发生，等等。

-- The filters that correspond to these descriptions will be defined later in this section, but we can already name them:

与这些描述相对应的滤子将在本节稍后定义，但我们现在就可以给它们命名：

-- * ``(atTop : Filter ℕ)``, made of sets of ``ℕ`` containing ``{n | n ≥ N}`` for some ``N``
-- * ``𝓝 x``, made of neighborhoods of ``x`` in a topological space
-- * ``𝓤 X``, made of entourages of a uniform space (uniform spaces generalize metric spaces and topological groups)
-- * ``μ.ae`` , made of sets whose complement has zero measure with respect to a measure ``μ``.

* ``(atTop : Filter ℕ)``，由包含 ``{n | n ≥ N}`` 的 ``ℕ`` 的集合构成，其中 ``N`` 为某个自然数
* ``𝓝 x``，由拓扑空间中 ``x`` 的邻域构成
* ``𝓤 X``，由一致空间的邻域基构成（一致空间推广了度量空间和拓扑群）
* ``μ.ae``，由相对于测度 ``μ`` 其补集测度为零的集合构成

-- The general definition is as follows: a filter ``F : Filter X`` is a
-- collection of sets ``F.sets : Set (Set X)`` satisfying the following:

一般的定义如下：一个滤子 ``F : Filter X`` 是集合 ``F.sets : Set (Set X)`` 的一个集合，满足以下条件：

-- * ``F.univ_sets : univ ∈ F.sets``
-- * ``F.sets_of_superset : ∀ {U V}, U ∈ F.sets → U ⊆ V → V ∈ F.sets``
-- * ``F.inter_sets : ∀ {U V}, U ∈ F.sets → V ∈ F.sets → U ∩ V ∈ F.sets``.

* ``F.univ_sets : univ ∈ F.sets``
* ``F.sets_of_superset : ∀ {U V}, U ∈ F.sets → U ⊆ V → V ∈ F.sets``
* ``F.inter_sets : ∀ {U V}, U ∈ F.sets → V ∈ F.sets → U ∩ V ∈ F.sets``.

-- The first condition says that the set of all elements of ``X`` belongs to ``F.sets``.
-- The second condition says that if ``U`` belongs to ``F.sets`` then anything
-- containing ``U`` also belongs to ``F.sets``.
-- The third condition says that ``F.sets`` is closed under finite intersections.
-- In Mathlib, a filter ``F`` is defined to be a structure bundling ``F.sets`` and its
-- three properties, but the properties carry no additional data,
-- and it is convenient to blur the distinction between ``F`` and ``F.sets``. We
-- therefore define ``U ∈ F`` to mean ``U ∈ F.sets``.
-- This explains why the word ``sets`` appears in the names of some lemmas that
-- that mention ``U ∈ F``.

第一个条件表明，集合 ``X`` 的所有元素都属于 ``F.sets``。
第二个条件表明，如果 ``U`` 属于 ``F.sets``，那么包含 ``U`` 的任何集合也属于 ``F.sets``。
第三个条件表明，``F.sets`` 对有限交集是封闭的。
在 Mathlib 中，滤子 ``F`` 被定义为捆绑 ``F.sets`` 及其三个属性的结构，但这些属性不携带额外的数据，并且将 ``F`` 和 ``F.sets`` 之间的区别模糊化是方便的。我们
因此，将``U ∈ F``定义为``U ∈ F.sets``。
这就解释了为什么在一些提及``U ∈ F``的引理名称中会出现``sets``这个词。

-- It may help to think of a filter as defining a notion of a "sufficiently large" set. The first
-- condition then says that ``univ`` is sufficiently large, the second one says that a set containing a sufficiently
-- large set is sufficiently large and the third one says that the intersection of two sufficiently large sets
-- is sufficiently large.

可以将滤子视为定义“足够大”集合的概念。第一个条件表明``univ``是足够大的集合，第二个条件表明包含足够大集合的集合也是足够大的集合，第三个条件表明两个足够大集合的交集也是足够大的集合。

-- It may be even  more useful to think of a filter on a type ``X``
-- as a generalized element of ``Set X``. For instance, ``atTop`` is the
-- "set of very large numbers" and ``𝓝 x₀`` is the "set of points very close to ``x₀``."
-- One manifestation of this view is that we can associate to any ``s : Set X`` the so-called *principal filter*
-- consisting of all sets that contain ``s``.
-- This definition is already in Mathlib and has a notation ``𝓟`` (localized in the ``Filter`` namespace).
-- For the purpose of demonstration, we ask you to take this opportunity to work out the definition here.

将类型``X``上的一个滤子视为``Set X``的广义元素，可能更有用。例如，``atTop`` 是“极大数的集合”，而 ``𝓝 x₀`` 是“非常接近 ``x₀`` 的点的集合”。这种观点的一种体现是，我们可以将任何 ``s ： Set X`` 与所谓的“主滤子”相关联，该主滤子由包含 ``s`` 的所有集合组成。
此定义已在 Mathlib 中，并有一个记号 ``𝓟``（在 ``Filter`` 命名空间中本地化）。为了演示的目的，我们请您借此机会在此处推导出该定义。
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
-- In the next example we could use `tauto` in each proof instead of knowing the lemmas
-- 在下一个示例中，我们可以在每个证明中使用 `tauto` 而不是记住这些引理
example {α : Type*} (s : Set α) : Filter α :=
  { sets := { t | s ⊆ t }
    univ_sets := subset_univ s
    sets_of_superset := fun hU hUV ↦ Subset.trans hU hUV
    inter_sets := fun hU hV ↦ subset_inter hU hV }

/- TEXT:
-- For our second example, we ask you to define the filter ``atTop : Filter ℕ``.
-- (We could use any type with a preorder instead of ``ℕ``.)

对于我们的第二个示例，我们请您定义滤子 ``atTop : Filter ℕ`` 。（我们也可以使用任何具有预序关系的类型来代替 ``ℕ``。）
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
-- We can also directly define the filter ``𝓝 x`` of neighborhoods of any ``x : ℝ``.
-- In the real numbers, a neighborhood of ``x`` is a set containing an open interval
-- :math:`(x_0 - \varepsilon, x_0 + \varepsilon)`,
-- defined in Mathlib as ``Ioo (x₀ - ε) (x₀ + ε)``.
-- (This is notion of a neighborhood is only a special case of a more general construction in Mathlib.)

我们还可以直接定义任意实数 ``x ： ℝ`` 的邻域滤子 ``𝓝 x`` 。在实数中，``x`` 的邻域是一个包含开区间 :math:`(x_0 - \varepsilon, x_0 + \varepsilon)` 的集合，在 Mathlib 中定义为 ``Ioo (x₀ - ε) (x₀ + ε)`` 。（Mathlib 中的这种邻域概念只是更一般构造的一个特例。）

-- With these examples, we can already define what is means for a function ``f : X → Y``
-- to converge to some ``G : Filter Y`` along some ``F : Filter X``,
-- as follows:

有了这些例子，我们就可以定义函数 ``f : X → Y`` 沿着某个 ``F : Filter X`` 收敛到某个 ``G : Filter Y`` 的含义，如下所述：
BOTH: -/
-- QUOTE:
def Tendsto₁ {X Y : Type*} (f : X → Y) (F : Filter X) (G : Filter Y) :=
  ∀ V ∈ G, f ⁻¹' V ∈ F
-- QUOTE.

/- TEXT:
-- When ``X`` is ``ℕ`` and ``Y`` is ``ℝ``, ``Tendsto₁ u atTop (𝓝 x)`` is equivalent to saying that the sequence ``u : ℕ → ℝ``
-- converges to the real number ``x``. When both ``X`` and ``Y`` are ``ℝ``, ``Tendsto f (𝓝 x₀) (𝓝 y₀)``
-- is equivalent to the familiar notion :math:`\lim_{x \to x₀} f(x) = y₀`.
-- All of the other kinds of limits mentioned in the introduction are
-- also equivalent to instances of ``Tendsto₁`` for suitable choices of filters on the source and target.

当 ``X`` 为 ``ℕ`` 且 ``Y`` 为 ``ℝ`` 时，``Tendsto₁ u atTop (𝓝 x)`` 等价于说序列 ``u ： ℕ → ℝ`` 收敛于实数 ``x`` 。当 ``X`` 和 ``Y`` 均为 ``ℝ`` 时，``Tendsto f (𝓝 x₀) (𝓝 y₀)`` 等价于熟悉的概念 :math:`\lim_{x \to x₀} f(x) = y₀` 。介绍中提到的所有其他类型的极限也等价于对源和目标上适当选择的滤子的 ``Tendsto₁`` 的实例。

-- The notion ``Tendsto₁`` above is definitionally equivalent to the notion ``Tendsto`` that is defined in Mathlib,
-- but the latter is defined more abstractly.
-- The problem with the definition of ``Tendsto₁`` is that it exposes a quantifier and elements of ``G``,
-- and it hides the intuition that we get by viewing filters as generalized sets. We can
-- hide the quantifier ``∀ V`` and make the intuition more salient by using more algebraic and set-theoretic machinery.
-- The first ingredient is the *pushforward* operation :math:`f_*` associated to any map ``f : X → Y``,
-- denoted ``Filter.map f`` in Mathlib. Given a filter ``F`` on ``X``, ``Filter.map f F : Filter Y`` is defined so that
-- ``V ∈ Filter.map f F ↔ f ⁻¹' V ∈ F`` holds definitionally.
-- In this examples file we've opened the ``Filter`` namespace so that
-- ``Filter.map`` can be written as ``map``. This means that we can rewrite the definition of ``Tendsto`` using
-- the order relation on ``Filter Y``, which is reversed inclusion of the set of members.
-- In other words, given ``G H : Filter Y``, we have ``G ≤ H ↔ ∀ V : Set Y, V ∈ H → V ∈ G``.

上述的``Tendsto₁``概念在定义上等同于在 Mathlib 中定义的``Tendsto``概念，但后者定义得更为抽象。``Tendsto₁``的定义存在的问题是它暴露了量词和``G``的元素，并且掩盖了通过将滤子视为广义集合所获得的直观理解。我们可以通过使用更多的代数和集合论工具来隐藏量词``∀ V``，并使这种直观理解更加突出。第一个要素是与任何映射``f : X → Y``相关的**前推**操作 ：math:`f_*`，在 Mathlib 中记为``Filter.map f``。给定``X``上的滤子``F``，``Filter.map f F ： Filter Y``被定义为使得``V ∈ Filter.map f F ↔ f ⁻¹' V ∈ F``成立。在这个示例文件中，我们已经打开了``Filter``命名空间，因此``Filter.map``可以写成``map``。这意味着我们可以使用``Filter Y``上的序关系来重写``Tendsto``的定义，该序关系是成员集合的反向包含关系。换句话说，给定``G H ： Filter Y``，我们有``G ≤ H ↔ ∀ V ： Set Y， V ∈ H → V ∈ G``。
EXAMPLES: -/
-- QUOTE:
def Tendsto₂ {X Y : Type*} (f : X → Y) (F : Filter X) (G : Filter Y) :=
  map f F ≤ G

example {X Y : Type*} (f : X → Y) (F : Filter X) (G : Filter Y) :
    Tendsto₂ f F G ↔ Tendsto₁ f F G :=
  Iff.rfl
-- QUOTE.

/- TEXT:
-- It may seem that the order relation on filters is backward. But recall that we can view filters on ``X`` as
-- generalized elements of ``Set X``, via the inclusion of ``𝓟 : Set X → Filter X`` which maps any set ``s`` to the corresponding principal filter.
-- This inclusion is order preserving, so the order relation on ``Filter`` can indeed be seen as the natural inclusion relation
-- between generalized sets. In this analogy, pushforward is analogous to the direct image.
-- And, indeed, ``map f (𝓟 s) = 𝓟 (f '' s)``.

可能看起来滤子上的序关系是反向的。但请回想一下，我们可以通过将任何集合 ``s`` 映射到相应的主滤子的 ``𝓟 ： Set X → Filter X`` 的包含关系，将 ``X`` 上的滤子视为 ``Set X`` 的广义元素。这种包含关系是保序的，因此 ``Filter`` 上的序关系确实可以被视为广义集合之间的自然包含关系。在这个类比中，前推类似于直接像（direct image）。而且，确实有 ``map f (𝓟 s) = 𝓟 (f '' s)``。

-- We can now understand intuitively why a sequence ``u : ℕ → ℝ`` converges to
-- a point ``x₀`` if and only if we have ``map u atTop ≤ 𝓝 x₀``.
-- The inequality means the "direct image under ``u``" of
-- "the set of very big natural numbers" is "included" in "the set of points very close to ``x₀``."

现在我们可以直观地理解为什么一个序列 ``u ： ℕ → ℝ`` 收敛于点 ``x₀`` 当且仅当 ``map u atTop ≤ 𝓝 x₀`` 成立。这个不等式意味着在 “``u`` 作用下”的“非常大的自然数集合”的“直接像”包含在“非常接近 ``x₀`` 的点的集合”中。

-- As promised, the definition of ``Tendsto₂`` does not exhibit any quantifiers or sets.
-- It also leverages the algebraic properties of the pushforward operation.
-- First, each ``Filter.map f`` is monotone. And, second, ``Filter.map`` is compatible with
-- composition.

正如所承诺的那样，``Tendsto₂`` 的定义中没有任何量词或集合。
它还利用了前推操作的代数性质。
首先，每个 ``Filter.map f`` 都是单调的。其次，``Filter.map`` 与复合运算兼容。
EXAMPLES: -/
-- QUOTE:
#check (@Filter.map_mono : ∀ {α β} {m : α → β}, Monotone (map m))

#check
  (@Filter.map_map :
    ∀ {α β γ} {f : Filter α} {m : α → β} {m' : β → γ}, map m' (map m f) = map (m' ∘ m) f)
-- QUOTE.

/- TEXT:
-- Together these two properties allow us to prove that limits compose, yielding in one shot all 256 variants
-- of the composition lemma described in the introduction, and lots more.
-- You can practice proving the following statement using either the definition
-- of ``Tendsto₁`` in terms of the
-- universal quantifier or the algebraic definition,
-- together with the two lemmas above.

这两个性质结合起来使我们能够证明极限的复合性，从而一次性得出引言中描述的 256 种组合引理变体，以及更多。
您可以使用``Tendsto₁``的全称量词定义或代数定义，连同上述两个引理，来练习证明以下陈述。
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
-- The pushforward construction uses a map to push filters from the map source to the map target.
-- There also a *pullback* operation, ``Filter.comap``, going in the other direction.
-- This generalizes the
-- preimage operation on sets. For any map ``f``,
-- ``Filter.map f`` and ``Filter.comap f`` form what is known as a *Galois connection*,
-- which is to say, they satisfy

--   ``Filter.map_le_iff_le_comap : Filter.map f F ≤ G ↔ F ≤ Filter.comap f G``

-- for every ``F`` and ``G``.
-- This operation could be used to provided another formulation of ``Tendsto`` that would be provably
-- (but not definitionally) equivalent to the one in Mathlib.

-- The ``comap`` operation can be used to restrict filters to a subtype. For instance, suppose we have ``f : ℝ → ℝ``,
-- ``x₀ : ℝ`` and ``y₀ : ℝ``, and suppose we want to state that ``f x`` approaches ``y₀`` when ``x`` approaches ``x₀`` within the rational numbers.
-- We can pull the filter ``𝓝 x₀`` back to ``ℚ`` using the coercion map
-- ``(↑) : ℚ → ℝ`` and state ``Tendsto (f ∘ (↑) : ℚ → ℝ) (comap (↑) (𝓝 x₀)) (𝓝 y₀)``.

前推构造使用一个映射将滤子从映射源推送到映射目标。
还有一个“拉回”操作，即 ``Filter.comap`` ，其方向相反。
这推广了集合上的原像操作。对于任何映射 ``f`` ，
``Filter.map f`` 和 ``Filter.comap f`` 构成了所谓的**伽罗瓦连接**，也就是说，它们满足

``filter.map_le_iff_le_comap``：``f`` 映射下的 ``F`` 小于等于 ``G`` 当且仅当 ``F`` 小于等于 ``G`` 在 ``f`` 下的逆像。

对于每一个``F``和``G``。
此操作可用于提供“Tendsto”的另一种表述形式，该形式可证明（但不是定义上）等同于 Mathlib 中的那个。

``comap`` 操作可用于将滤子限制在子类型上。例如，假设我们有 ``f ： ℝ → ℝ``、``x₀ ： ℝ`` 和 ``y₀ ： ℝ``，并且假设我们想要说明当 ``x`` 在有理数范围内趋近于 ``x₀`` 时，``f x`` 趋近于 ``y₀``。我们可以使用强制转换映射 ``(↑) ： ℚ → ℝ`` 将滤子 ``𝓝 x₀`` 拉回到 ``ℚ``，并声明 ``Tendsto (f ∘ (↑) ： ℚ → ℝ) (comap (↑) (𝓝 x₀)) (𝓝 y₀)``。
EXAMPLES: -/
-- QUOTE:
variable (f : ℝ → ℝ) (x₀ y₀ : ℝ)

#check comap ((↑) : ℚ → ℝ) (𝓝 x₀)

#check Tendsto (f ∘ (↑)) (comap ((↑) : ℚ → ℝ) (𝓝 x₀)) (𝓝 y₀)
-- QUOTE.

/- TEXT:
-- The pullback operation is also compatible with composition, but it is *contravariant*,
-- which is to say, it reverses the order of the arguments.

拉回操作也与复合运算兼容，但它具有**反变性**，也就是说，它会颠倒参数的顺序。
EXAMPLES: -/
-- QUOTE:
section
variable {α β γ : Type*} (F : Filter α) {m : γ → β} {n : β → α}

#check (comap_comap : comap m (comap n F) = comap (n ∘ m) F)

end
-- QUOTE.

/- TEXT:
-- Let's now shift attention to the plane ``ℝ × ℝ`` and try to understand how the neighborhoods of a point
-- ``(x₀, y₀)`` are related to ``𝓝 x₀`` and ``𝓝 y₀``. There is a product operation
-- ``Filter.prod : Filter X → Filter Y → Filter (X × Y)``, denoted by ``×ˢ``, which answers this question:

现在让我们将注意力转向平面``ℝ × ℝ``，并尝试理解点``(x₀， y₀)``的邻域与``𝓝 x₀``和``𝓝 y₀``之间的关系。
存在一个乘积运算``Filter.prod ： Filter X → Filter Y → Filter (X × Y)``，记作``×ˢ``，它回答了这个问题：
EXAMPLES: -/
-- QUOTE:
example : 𝓝 (x₀, y₀) = 𝓝 x₀ ×ˢ 𝓝 y₀ :=
  nhds_prod_eq
-- QUOTE.

/- TEXT:
-- The product operation is defined in terms of the pullback operation and the ``inf`` operation:

--   ``F ×ˢ G = (comap Prod.fst F) ⊓ (comap Prod.snd G)``.

-- Here the ``inf`` operation refers to the lattice structure on ``Filter X`` for any type ``X``, whereby
-- ``F ⊓ G`` is the greatest filter that is smaller than both ``F`` and ``G``.
-- Thus the ``inf`` operation generalizes the notion of the intersection of sets.

-- A lot of proofs in Mathlib use all of the aforementioned structure (``map``, ``comap``, ``inf``, ``sup``, and ``prod``)
-- to give algebraic proofs about convergence without ever referring to members of filters.
-- You can practice doing this in a proof of the following lemma, unfolding the definition of ``Tendsto``
-- and ``Filter.prod`` if needed.

该乘积运算通过拉回运算和``inf``运算来定义：

``F ×ˢ G = (comap Prod.fst F) ⊓ (comap Prod.snd G)``

这里的``inf``操作指的是对于任何类型 X 的``Filter X``上的格结构，其中 ``F ⊓ G`` 是小于 ``F`` 和 ``G`` 的最大滤子。
因此，``inf``操作推广了集合交集的概念。

在 Mathlib 中的许多证明都使用了上述所有结构（``map``、``comap``、``inf``、``sup`` 和 ``prod``），从而给出关于收敛性的代数证明，而无需提及滤子的成员。您可以在以下引理的证明中练习这样做，如果需要，可以展开 ``Tendsto`` 和 ``Filter.prod`` 的定义。
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
-- The ordered type ``Filter X`` is actually a *complete* lattice,
-- which is to say, there is a bottom element, there is a top element, and
-- every set of filters on ``X`` has an ``Inf`` and a ``Sup``.

有序类型``Filter X``实际上是一个**完备**格，也就是说，存在一个最小元素，存在一个最大元素，并且 X 上的每个滤子集都有一个``Inf``和一个``Sup``。

-- Note that given the second property in the definition of a filter
-- (if ``U`` belongs to ``F`` then anything larger than ``U`` also belongs to ``F``),
-- the first property
-- (the set of all inhabitants of ``X`` belongs to ``F``) is
-- equivalent to the property that ``F`` is not the empty collection of sets.
-- This shouldn't be confused with the more subtle question as to whether
-- the empty set is an *element* of ``F``. The
-- definition of a filter does not prohibit ``∅ ∈ F``,
-- but if the empty set is in ``F`` then
-- every set is in ``F``, which is to say, ``∀ U : Set X, U ∈ F``.
-- In this case, ``F`` is a rather trivial filter, which is precisely the
-- bottom element of the complete lattice ``Filter X``.
-- This contrasts with the definition of filters in
-- Bourbaki, which doesn't allow filters containing the empty set.

请注意，根据滤子定义中的第二个性质（如果``U``属于``F``，那么任何包含``U``的集合也属于``F``），第一个性质（``X``的所有元素组成的集合属于``F``）等价于``F``不是空集合这一性质。这不应与更微妙的问题相混淆，即空集是否为``F``的一个**元素**。滤子的定义并不禁止``∅ ∈ F``，但如果空集在``F``中，那么每个集合都在``F``中，也就是说，``∀ U : Set X, U ∈ F``。在这种情况下，``F``是一个相当平凡的滤子，恰好是完备格``Filter X``的最小元素。这与布尔巴基对滤子的定义形成对比，布尔巴基的定义不允许滤子包含空集。

-- Because we include the trivial filter in our definition, we sometimes need to explicitly assume
-- nontriviality in some lemmas.
-- In return, however, the theory has nicer global properties.
-- We have already seen that including the trivial filter gives us a
-- bottom element. It also allows us to define ``principal : Set X → Filter X``,
-- which maps  ``∅`` to ``⊥``, without adding a precondition to rule out the empty set.
-- And it allows us to define the pullback operation without a precondition as well.
-- Indeed, it can happen that ``comap f F = ⊥`` although ``F ≠ ⊥``. For instance,
-- given ``x₀ : ℝ`` and ``s : Set ℝ``, the pullback of ``𝓝 x₀`` under the coercion
-- from the subtype corresponding to ``s`` is nontrivial if and only if ``x₀`` belongs to the
-- closure of ``s``.

由于我们在定义中包含了平凡滤子，所以在某些引理中有时需要明确假设非平凡性。不过作为回报，该理论具有更优的整体性质。我们已经看到，包含平凡滤子为我们提供了一个最小元素。它还允许我们定义``principal ： Set X → Filter X``，将``∅``映射到``⊥``，而无需添加预条件来排除空集。而且它还允许我们定义拉回操作时无需预条件。实际上，有可能``comap f F = ⊥``尽管``F ≠ ⊥``。例如，给定``x₀ ： ℝ``和``s : Set ℝ``，``𝓝 x₀``在从与``s``对应的子类型强制转换下的拉回非平凡当且仅当``x₀``属于``s``的闭包。

-- In order to manage lemmas that do need to assume some filter is nontrivial, Mathlib has
-- a type class ``Filter.NeBot``, and the library has lemmas that assume
-- ``(F : Filter X) [F.NeBot]``. The instance database knows, for example, that ``(atTop : Filter ℕ).NeBot``,
-- and it knows that pushing forward a nontrivial filter gives a nontrivial filter.
-- As a result, a lemma assuming ``[F.NeBot]`` will automatically apply to ``map u atTop`` for any sequence ``u``.

为了管理确实需要假设某些滤子非平凡的引理，Mathlib 设有类型类``Filter.NeBot``，并且库中存在假设``（F : Filter X）[F.NeBot]``的引理。实例数据库知道，例如，``(atTop : Filter ℕ).NeBot``，并且知道将非平凡滤子向前推进会得到一个非平凡滤子。因此，假设``[F.NeBot]``的引理将自动应用于任何序列``u``的``map u atTop``。

-- Our tour of the algebraic properties of filters and their relation to limits is essentially done,
-- but we have not yet justified our claim to have recaptured the usual limit notions.
-- Superficially, it may seem that ``Tendsto u atTop (𝓝 x₀)``
-- is stronger than the notion of convergence defined in :numref:`sequences_and_convergence` because we ask that *every* neighborhood of ``x₀``
-- has a preimage belonging to ``atTop``, whereas the usual definition only requires
-- this for the standard neighborhoods ``Ioo (x₀ - ε) (x₀ + ε)``.
-- The key is that, by definition, every neighborhood contains such a standard one.
-- This observation leads to the notion of a *filter basis*.


我们对滤子的代数性质及其与极限的关系的探讨基本上已经完成，但我们尚未证明我们所提出的重新捕捉通常极限概念的主张是合理的。
表面上看，``Tendsto u atTop (𝓝 x₀)``似乎比在 :numref:``sequences_and_convergence`` 中定义的收敛概念更强，因为我们要求``x₀``的**每个**邻域都有一个属于``atTop``的原像，而通常的定义仅要求对于标准邻域``Ioo (x₀ - ε) (x₀ + ε)``满足这一条件。关键在于，根据定义，每个邻域都包含这样的标准邻域。这一观察引出了**滤子基（filter basis）**的概念。

-- Given ``F : Filter X``,
-- a family of sets ``s : ι → Set X`` is a basis for ``F`` if for every set ``U``,
-- we have ``U ∈ F`` if and only if it contains some ``s i``. In other words, formally speaking,
-- ``s`` is a basis if it satisfies
-- ``∀ U : Set X, U ∈ F ↔ ∃ i, s i ⊆ U``. It is even more flexible to consider
-- a predicate on ``ι`` that selects only some of the values ``i`` in the indexing type.
-- In the case of ``𝓝 x₀``, we want ``ι`` to be ``ℝ``, we write ``ε`` for ``i``, and the predicate should select the positive values of ``ε``.
-- So the fact that the sets ``Ioo  (x₀ - ε) (x₀ + ε)`` form a basis for the
-- neighborhood topology on ``ℝ`` is stated as follows:

给定``F : Filter X``，如果对于每个集合``U``，我们有``U ∈ F``当且仅当它包含某个``s i``，那么集合族``s ： ι → Set X``就是``F``的基。
换句话说，严格说来，``s``是基当且仅当它满足``∀ U : Set X, U ∈ F ↔ ∃ i, s i ⊆ U``。考虑在索引类型中仅选择某些值``i``的``ι``上的谓词会更加灵活。
对于``𝓝 x₀``，我们希望``ι``为``ℝ``，用``ε``表示``i``，并且谓词应选择``ε``的正值。因此，集合``Ioo (x₀ - ε) (x₀ + ε)``构成``ℝ``上邻域拓扑的基这一事实可表述如下：
EXAMPLES: -/
-- QUOTE:
example (x₀ : ℝ) : HasBasis (𝓝 x₀) (fun ε : ℝ ↦ 0 < ε) fun ε ↦ Ioo (x₀ - ε) (x₀ + ε) :=
  nhds_basis_Ioo_pos x₀
-- QUOTE.

/- TEXT:
-- There is also a nice basis for the filter ``atTop``. The lemma
-- ``Filter.HasBasis.tendsto_iff`` allows
-- us to reformulate a statement of the form ``Tendsto f F G``
-- given bases for ``F`` and ``G``.
-- Putting these pieces together gives us essentially the notion of convergence
-- that we used in :numref:`sequences_and_convergence`.

还有一个很好的``atTop``滤子的基础。引理``Filter.HasBasis.tendsto_iff``允许我们在给定``F``和``G``的基础的情况下，重新表述形式为``Tendsto f F G``的陈述。将这些部分组合在一起，就基本上得到了我们在 :numref:``sequences_and_convergence`` 中使用的收敛概念。
EXAMPLES: -/
-- QUOTE:
example (u : ℕ → ℝ) (x₀ : ℝ) :
    Tendsto u atTop (𝓝 x₀) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, u n ∈ Ioo (x₀ - ε) (x₀ + ε) := by
  have : atTop.HasBasis (fun _ : ℕ ↦ True) Ici := atTop_basis
  rw [this.tendsto_iff (nhds_basis_Ioo_pos x₀)]
  simp
-- QUOTE.

/- TEXT:
-- We now show how filters facilitate working with properties that hold for sufficiently large numbers
-- or for points that are sufficiently close to a given point. In :numref:`sequences_and_convergence`, we were often faced with the situation where
-- we knew that some property ``P n`` holds for sufficiently large ``n`` and that some
-- other property ``Q n`` holds for sufficiently large ``n``.
-- Using ``cases`` twice gave us ``N_P`` and ``N_Q`` satisfying
-- ``∀ n ≥ N_P, P n`` and ``∀ n ≥ N_Q, Q n``. Using ``set N := max N_P N_Q``, we could
-- eventually prove ``∀ n ≥ N, P n ∧ Q n``.
-- Doing this repeatedly becomes tiresome.

现在我们展示一下滤子如何有助于处理对于足够大的数字或对于给定点足够近的点成立的性质。在 :numref:`sequences_and_convergence` 中，我们经常遇到这样的情况：我们知道某个性质 ``P n`` 对于足够大的 ``n`` 成立，而另一个性质 ``Q n`` 对于足够大的 ``n`` 也成立。使用两次 ``cases`` 得到了满足 ``∀ n ≥ N_P， P n`` 和 ``∀ n ≥ N_Q， Q n`` 的 ``N_P`` 和 ``N_Q``。通过 ``set N := max N_P N_Q``，我们最终能够证明 ``∀ n ≥ N， P n ∧ Q n``。反复这样做会让人感到厌烦。

-- We can do better by noting that the statement "``P n`` and ``Q n`` hold for large enough ``n``" means
-- that we have ``{n | P n} ∈ atTop`` and ``{n | Q n} ∈ atTop``.
-- The fact that ``atTop`` is a filter implies that the intersection of two elements of ``atTop``
-- is again in ``atTop``, so we have ``{n | P n ∧ Q n} ∈ atTop``.
-- Writing ``{n | P n} ∈ atTop`` is unpleasant,
-- but we can use the more suggestive notation ``∀ᶠ n in atTop, P n``.
-- Here the superscripted ``f`` stands for "Filter."
-- You can think of the notation as saying that for all ``n`` in the "set of very large numbers," ``P n`` holds. The ``∀ᶠ``
-- notation stands for ``Filter.Eventually``, and the lemma ``Filter.Eventually.and`` uses the intersection property of filters to do what we just described:

我们可以通过注意到“对于足够大的 n，``P n`` 和 ``Q n`` 成立”这一表述意味着我们有 ``{n | P n} ∈ atTop`` 和 ``{n | Q n} ∈ atTop`` 来做得更好。由于 ``atTop`` 是一个滤子，所以 ``atTop`` 中两个元素的交集仍在 ``atTop`` 中，因此我们有 ``{n | P n ∧ Q n} ∈ atTop``。书写 ``{n | P n} ∈ atTop`` 不太美观，但我们可以用更具提示性的记号 ``∀ᶠ n in atTop， P n``。这里的上标 ``f`` 表示“滤子”。你可以将这个记号理解为对于“非常大的数集”中的所有 ``n``，``P n`` 成立。``∀ᶠ`` 记号代表 ``Filter.Eventually``，而引理 ``Filter.Eventually.and`` 利用滤子的交集性质来实现我们刚才所描述的操作：
EXAMPLES: -/
-- QUOTE:
example (P Q : ℕ → Prop) (hP : ∀ᶠ n in atTop, P n) (hQ : ∀ᶠ n in atTop, Q n) :
    ∀ᶠ n in atTop, P n ∧ Q n :=
  hP.and hQ
-- QUOTE.

/- TEXT:
-- This notation is so convenient and intuitive that we also have specializations
-- when ``P`` is an equality or inequality statement. For example, let ``u`` and ``v`` be
-- two sequences of real numbers, and let us show that if
-- ``u n`` and ``v n`` coincide for sufficiently large ``n`` then
-- ``u`` tends to ``x₀`` if and only if ``v`` tends to ``x₀``.
-- First we'll use the generic ``Eventually`` and then the one
-- specialized for the equality predicate, ``EventuallyEq``. The two statements are
-- definitionally equivalent so the same proof work in both cases.

这种表示法如此方便且直观，以至于当``P``是一个等式或不等式陈述时，我们也有专门的表示形式。例如，设``u``和``v``是两个实数序列，让我们证明如果对于足够大的``n``，``u n``和``v n``相等，那么``u``趋向于``x₀``当且仅当``v``趋向于``x₀``。首先我们将使用通用的``Eventually``，然后使用专门针对等式谓词的``EventuallyEq``。这两个陈述在定义上是等价的，因此在两种情况下相同的证明都适用。
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
-- It is instructive to review the definition of filters in terms of ``Eventually``.
-- Given ``F : Filter X``, for any predicates ``P`` and ``Q`` on ``X``,

-- * the condition ``univ ∈ F`` ensures ``(∀ x, P x) → ∀ᶠ x in F, P x``,
-- * the condition ``U ∈ F → U ⊆ V → V ∈ F`` ensures ``(∀ᶠ x in F, P x) → (∀ x, P x → Q x) → ∀ᶠ x in F, Q x``, and
-- * the condition ``U ∈ F → V ∈ F → U ∩ V ∈ F`` ensures ``(∀ᶠ x in F, P x) → (∀ᶠ x in F, Q x) → ∀ᶠ x in F, P x ∧ Q x``.

从``Eventually``这一概念的角度来审视滤子的定义是很有启发性的。
给定滤子 ``F : Filter X`` ，对于 ``X`` 上的任意谓词 ``P`` 和 ``Q`` ，

条件``univ ∈ F``确保了``(∀ x, P x) → ∀ᶠ x in F, P x``，
条件``U ∈ F → U ⊆ V → V ∈ F``确保了``(∀ᶠ x in F, P x) → (∀ x, P x → Q x) → ∀ᶠ x in F, Q x``，并且
条件``U ∈ F → V ∈ F → U ∩ V ∈ F``确保了``(∀ᶠ x in F, P x) → (∀ᶠ x in F, Q x) → ∀ᶠ x in F, P x ∧ Q x``。
EXAMPLES: -/
-- QUOTE:
#check Eventually.of_forall
#check Eventually.mono
#check Eventually.and
-- QUOTE.

/- TEXT:
-- The second item, corresponding to ``Eventually.mono``, supports nice ways
-- of using filters, especially when combined
-- with ``Eventually.and``. The ``filter_upwards`` tactic allows us to combine them.
-- Compare:

第二个项目，对应于``Eventually.mono``，支持使用滤子的优雅方式，尤其是与``Eventually.and``结合使用时。``filter_upwards`` 策略使我们能够将它们组合起来。比较：
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
-- Readers who know about measure theory will note that the filter ``μ.ae`` of sets whose complement has measure zero
-- (aka "the set consisting of almost every point") is not very useful as the source or target of ``Tendsto``, but it can be conveniently
-- used with ``Eventually`` to say that a property holds for almost every point.

熟悉测度论的读者会注意到，补集测度为零的集合构成的滤子``μ.ae``（即“几乎每个点构成的集合”）作为``Tendsto``的源或目标并不是很有用，但它可以方便地与``Eventually``一起使用，以表明某个性质对几乎每个点都成立。

-- There is a dual version of ``∀ᶠ x in F, P x``, which is occasionally useful:
-- ``∃ᶠ x in F, P x`` means
-- ``{x | ¬P x} ∉ F``. For example, ``∃ᶠ n in atTop, P n`` means there are arbitrarily large ``n`` such that ``P n`` holds.
-- The ``∃ᶠ`` notation stands for ``Filter.Frequently``.

-- There is a dual version of ``∀ᶠ x in F, P x``, which is occasionally useful:
-- ``∃ᶠ x in F, P x`` means
-- ``{x | ¬P x} ∉ F``. For example, ``∃ᶠ n in atTop, P n`` means there are arbitrarily large ``n`` such that ``P n`` holds.
-- The ``∃ᶠ`` notation stands for ``Filter.Frequently``.

存在``∀ᶠ x in F, P x``的双重版本，有时会很有用：
用``∃ᶠ x in F, P x``表示
``{x | ¬P x} ∉ F``。例如，``∃ᶠ n in atTop, P n``意味着存在任意大的 ``n`` 使得 ``P n`` 成立。
``∃ᶠ``符号代表``Filter.Frequently``。

-- For a more sophisticated example, consider the following statement about a sequence
-- ``u``, a set ``M``, and a value ``x``:

对于一个更复杂的示例，请考虑以下关于序列 ``u``、集合 ``M`` 和值 ``x`` 的陈述：

  -- If ``u`` converges to ``x`` and ``u n`` belongs to ``M`` for
  -- sufficiently large ``n`` then ``x`` is in the closure of ``M``.

如果序列 ``u`` 收敛于 ``x`` ，且对于足够大的 ``n`` ，``u n`` 属于集合 ``M`` ，那么 ``x`` 就在集合 ``M`` 的闭包内。

-- This can be formalized as follows:

--   ``Tendsto u atTop (𝓝 x) → (∀ᶠ n in atTop, u n ∈ M) → x ∈ closure M``.

-- This is a special case of the theorem ``mem_closure_of_tendsto`` from the
-- topology library.
-- See if you can prove it using the quoted lemmas,
-- using the fact that ``ClusterPt x F`` means ``(𝓝 x ⊓ F).NeBot`` and that,
-- by definition, the assumption ``∀ᶠ n in atTop, u n ∈ M`` means  ``M ∈ map u atTop``.

这可以形式化表述如下：

  ``Tendsto u atTop (𝓝 x) → (∀ᶠ n in atTop, u n ∈ M) → x ∈ closure M``.

这是拓扑库中定理``mem_closure_of_tendsto``的一个特殊情况。
试着利用所引用的引理来证明它，利用``ClusterPt x F``意味着``(𝓝 x ⊓ F).NeBot``这一事实，以及根据定义，``∀ᶠ n in atTop， u n ∈ M``这一假设意味着``M ∈ map u atTop``。
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
