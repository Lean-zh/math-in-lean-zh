-- BOTH:
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Charpoly.Basic

import MIL.Common

/- TEXT:
.. index:: vector subspace

子空间和商空间
-----------------------

子空间
^^^^^^^^^

正如线性映射是打包结构，向量空间 `V` 的线性子空间同样是一个打包结构，包含 `V` 中的一个子集，称为子空间的载体（carrier），并具备相关的闭合性质。这里依然使用“模（module）”一词，而非向量空间，是因为 Mathlib 在线性代数中采用了更广泛的理论框架。
EXAMPLES: -/
-- QUOTE:

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

example (U : Submodule K V) {x y : V} (hx : x ∈ U) (hy : y ∈ U) :
    x + y ∈ U :=
  U.add_mem hx hy

example (U : Submodule K V) {x : V} (hx : x ∈ U) (a : K) :
    a • x ∈ U :=
  U.smul_mem a hx

-- QUOTE.

/- TEXT:
在上述例子中，需要理解的是，`Submodule K V` 表示 `V` 上的 `K`-线性子空间的类型，而非 `Set V` 中元素 `U` 的谓词 `IsSubmodule U`。`Submodule K V` 配备了到 `Set V` 的强制类型转换（coercion）以及对 `V` 的成员关系谓词。有关该设计的原因及实现方式，可参见 :numref:`section_hierarchies_subobjects`。

当然，两个子空间相等当且仅当它们包含相同的元素。此性质已被注册用于 `ext` 策略，后者可用来证明两个子空间相等，方式与证明两个集合相等相同。

例如，要表述并证明实数域 `ℝ` 是复数域 `ℂ` 上的一个 `ℝ`-线性子空间，实质上是构造一个类型为 `Submodule ℝ ℂ` 的项，使其强制转换为 `Set ℂ` 后正是 `ℝ`，或者更准确地说，是 `ℝ` 在 `ℂ` 中的像。
EXAMPLES: -/
-- QUOTE:
noncomputable example : Submodule ℝ ℂ where
  carrier := Set.range ((↑) : ℝ → ℂ)
  add_mem' := by
    rintro _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
    use n + m
    simp
  zero_mem' := by
    use 0
    simp
  smul_mem' := by
    rintro c - ⟨a, rfl⟩
    use c*a
    simp

-- QUOTE.

/- TEXT:
`Submodule` 中证明字段末尾的撇号与 `LinearMap` 中的类似。这些字段以 `carrier` 字段为基础定义，因为它们在 `Membership` 实例之前被定义。随后，它们被我们之前看到的 `Submodule.add_mem`、`Submodule.zero_mem` 和 `Submodule.smul_mem` 所取代。

作为操作子空间和线性映射的练习，你将定义线性映射下子空间的原像（pre-image）（当然，后面会看到 Mathlib 已经包含了相关定义）。
记住，可以使用 `Set.mem_preimage` 来对涉及成员资格和原像的陈述进行重写。除了上述关于 `LinearMap` 和 `Submodule` 的引理外，这是你唯一需要用到的引理。

BOTH: -/
-- QUOTE:
def preimage {W : Type*} [AddCommGroup W] [Module K W] (φ : V →ₗ[K] W) (H : Submodule K W) :
    Submodule K V where
  carrier := φ ⁻¹' H
  zero_mem' := by
/- EXAMPLES:
    dsimp
    sorry
SOLUTIONS: -/
    dsimp
    rw [Set.mem_preimage, map_zero]
    exact H.zero_mem
-- BOTH:
  add_mem' := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    rintro a b ha hb
    rw [Set.mem_preimage, map_add]
    apply H.add_mem <;> assumption
-- BOTH:
  smul_mem' := by
/- EXAMPLES:
    dsimp
    sorry
SOLUTIONS: -/
    dsimp
    rintro a v hv
    rw [Set.mem_preimage, map_smul]
    exact H.smul_mem a hv
-- BOTH:
-- QUOTE.

/- TEXT:

使用类型类，Mathlib 知道向量空间的子空间继承了向量空间结构。
EXAMPLES: -/
-- QUOTE:
example (U : Submodule K V) : Module K U := inferInstance
-- QUOTE.

/- TEXT:
这个例子很微妙。对象 ``U`` 不是一个类型，但 Lean 会通过将其解释为 ``V`` 的一个子类型来自动将其强制转换为一个类型。
因此，上面的例子可以更明确地重述为：
EXAMPLES: -/
-- QUOTE:
example (U : Submodule K V) : Module K {x : V // x ∈ U} := inferInstance
-- QUOTE.

/- TEXT:

完全格结构和内直和
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

拥有类型 `Submodule K V` 而非谓词 `IsSubmodule : Set V → Prop` 的一个重要好处是，可以方便地赋予 `Submodule K V` 额外的结构。
其中最重要的是它在包含关系下具有完备格结构。例如，不再需要单独的引理来说明两个子空间的交集仍是子空间，我们可以直接使用格的运算符 `⊓` 来构造交集。
随后便可对该结构应用任意格论相关的引理。

下面我们验证，两个子空间下确界对应的底层集合，正是它们的（定义上的）交集。
EXAMPLES: -/
-- QUOTE:
example (H H' : Submodule K V) :
    ((H ⊓ H' : Submodule K V) : Set V) = (H : Set V) ∩ (H' : Set V) := rfl
-- QUOTE.

/- TEXT:
对底层集合的交集使用不同符号表示可能看起来有些奇怪，但这种对应关系并不适用于上确界运算和集合的并集，因为子空间的并集通常并不是子空间。
取而代之的是，需要使用由并集生成的子空间，这通常通过 `Submodule.span` 来实现。
EXAMPLES: -/
-- QUOTE:
example (H H' : Submodule K V) :
    ((H ⊔ H' : Submodule K V) : Set V) = Submodule.span K ((H : Set V) ∪ (H' : Set V)) := by
  simp [Submodule.span_union]
-- QUOTE.

/- TEXT:
另一个细节是，向量空间本身 `V` 并不属于类型 `Submodule K V`，因此需要一种方式来表示将 `V` 视为自身的子空间。这也由格结构提供支持：整个空间作为该格的最大元存在。

EXAMPLES: -/
-- QUOTE:
example (x : V) : x ∈ (⊤ : Submodule K V) := trivial
-- QUOTE.

/- TEXT:
同样，这个格的底部元素是唯一元素为零元素的子空间。
EXAMPLES: -/
-- QUOTE:
example (x : V) : x ∈ (⊥ : Submodule K V) ↔ x = 0 := Submodule.mem_bot K
-- QUOTE.

/- TEXT:
特别地，我们可以讨论处于（内部）直和的子空间的情况。在两个子空间的情况下，我们使用通用谓词 ``IsCompl``，它适用于任何有界偏序类型。在一般子空间族的情况下，我们使用 ``DirectSum.IsInternal``。

EXAMPLES: -/
-- QUOTE:

-- 如果两个子空间是直和，则它们生成整个空间。
example (U V : Submodule K V) (h : IsCompl U V) :
  U ⊔ V = ⊤ := h.sup_eq_top

-- 如果两个子空间是直和，则它们的交集仅为零。
example (U V : Submodule K V) (h : IsCompl U V) :
  U ⊓ V = ⊥ := h.inf_eq_bot

section
open DirectSum
variable {ι : Type*} [DecidableEq ι]

-- 如果子空间是直和，则它们生成整个空间。
example (U : ι → Submodule K V) (h : DirectSum.IsInternal U) :
  ⨆ i, U i = ⊤ := h.submodule_iSup_eq_top

-- 如果子空间是直和，则它们的交集仅为零。
example {ι : Type*} [DecidableEq ι] (U : ι → Submodule K V) (h : DirectSum.IsInternal U)
    {i j : ι} (hij : i ≠ j) : U i ⊓ U j = ⊥ :=
  (h.submodule_independent.pairwiseDisjoint hij).eq_bot

-- 这些条件表征了直和。
#check DirectSum.isInternal_submodule_iff_independent_and_iSup_eq_top

-- 与外直和的关系：如果一族子空间是内直和，则它们的外直和映射到 `V` 的映射是线性同构。
noncomputable example {ι : Type*} [DecidableEq ι] (U : ι → Submodule K V)
    (h : DirectSum.IsInternal U) : (⨁ i, U i) ≃ₗ[K] V :=
  LinearEquiv.ofBijective (coeLinearMap U) h
end
-- QUOTE.

/- TEXT:

由集合生成的子空间
^^^^^^^^^^^^^^^^^^^^^^^^^

除了从现有子空间构建子空间，我们还可以使用 ``Submodule.span K s`` 从任何集合 ``s`` 构建子空间，该函数构建包含 ``s`` 的最小子空间。
在纸面上，通常使用该空间由 ``s`` 的所有线性组合构成的事实。但通常更有效的方法是使用其万有性质，即 ``Submodule.span_le``，以及整个 Galois 连接理论。

EXAMPLES: -/
-- QUOTE:
example {s : Set V} (E : Submodule K V) : Submodule.span K s ≤ E ↔ s ⊆ E :=
  Submodule.span_le

example : GaloisInsertion (Submodule.span K) ((↑) : Submodule K V → Set V) :=
  Submodule.gi K V
-- QUOTE.
/- TEXT:
当上述方法不够时，可以使用相关的归纳原理 `Submodule.span_induction`，它保证只要某性质对零元和集合 `s` 中的元素成立，且在加法和标量乘法下封闭，那么该性质对 `s` 的张成子空间中的每个元素都成立。

作为练习，我们重新证明 `Submodule.mem_sup` 的一个推论。记住你可以使用 `module` 策略，来解决基于 `V` 上各种代数运算公理的证明目标。
EXAMPLES: -/
-- QUOTE:


example {S T : Submodule K V} {x : V} (h : x ∈ S ⊔ T) :
    ∃ s ∈ S, ∃ t ∈ T, x = s + t  := by
  rw [← S.span_eq, ← T.span_eq, ← Submodule.span_union] at h
  induction h using Submodule.span_induction with
/- EXAMPLES:
  | mem y h =>
      sorry
  | zero =>
      sorry
  | add x y hx hy hx' hy' =>
      sorry
  | smul a x hx hx' =>
      sorry
SOLUTIONS: -/
  | mem x h =>
      rcases h with (hx|hx)
      · use x, hx, 0, T.zero_mem
        module
      · use 0, S.zero_mem, x, hx
        module
  | zero =>
      use 0, S.zero_mem, 0, T.zero_mem
      module
  | add x y hx hy hx' hy' =>
      rcases hx' with ⟨s, hs, t, ht, rfl⟩
      rcases hy' with ⟨s', hs', t', ht', rfl⟩
      use s + s', S.add_mem hs hs', t + t', T.add_mem ht ht'
      module
  | smul a x hx hx' =>
      rcases hx' with ⟨s, hs, t, ht, rfl⟩
      use a • s, S.smul_mem a hs, a • t, T.smul_mem a ht
      module

-- QUOTE.
/- TEXT:

拉回和推出子空间
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

如前所述，我们现在描述如何通过线性映射来拉回和推出子空间。
在 Mathlib 中，第一个操作称为 ``map``，第二个操作称为 ``comap``。
EXAMPLES: -/
-- QUOTE:

section

variable {W : Type*} [AddCommGroup W] [Module K W] (φ : V →ₗ[K] W)

variable (E : Submodule K V) in
#check (Submodule.map φ E : Submodule K W)

variable (F : Submodule K W) in
#check (Submodule.comap φ F : Submodule K V)
-- QUOTE.

/- TEXT:
这些函数定义在 `Submodule` 命名空间内，因此可以使用点记法写作 ``E.map φ`` 而不是``Submodule.map φ E``。不过这种写法阅读起来相当别扭（虽然有些 Mathlib 贡献者会这样写）。特别地，线性映射的像集和核都是子空间，这些特殊情况重要到有专门的声明支持。
EXAMPLES: -/
-- QUOTE:
example : LinearMap.range φ = .map φ ⊤ := LinearMap.range_eq_map φ

example : LinearMap.ker φ = .comap φ ⊥ := Submodule.comap_bot φ -- or `rfl`
-- QUOTE.


/- TEXT:
请注意，我们不能写成 `φ.ker` 来替代 `LinearMap.ker φ`，因为 `LinearMap.ker` 不仅适用于线性映射，还适用于保持更多结构的映射类，因此它不期望接收类型以 `LinearMap` 开头的参数，所以点记法在这里无法使用。然而，在右侧我们能够使用另一种点记法。因为 Lean 在展开左侧后，期望得到类型为 `Submodule K V` 的项，因此它会将 `.comap` 解析为 `Submodule.comap`。

以下引理描述了这些子模与线性映射 `φ` 的关键关系。
EXAMPLES: -/
-- QUOTE:

open Function LinearMap

example : Injective φ ↔ ker φ = ⊥ := ker_eq_bot.symm

example : Surjective φ ↔ range φ = ⊤ := range_eq_top.symm
-- QUOTE.
/- TEXT:
作为练习，我们来证明 ``map`` 和 ``comap`` 的 Galois 连接性质。
可以使用以下引理，但这不是必需的，因为它们是根据定义成立的。
EXAMPLES: -/
-- QUOTE:

#check Submodule.mem_map_of_mem
#check Submodule.mem_map
#check Submodule.mem_comap

example (E : Submodule K V) (F : Submodule K W) :
    Submodule.map φ E ≤ F ↔ E ≤ Submodule.comap φ F := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  constructor
  · intro h x hx
    exact h ⟨x, hx, rfl⟩
  · rintro h - ⟨x, hx, rfl⟩
    exact h hx
-- QUOTE.

/- TEXT:
商空间
^^^^^^^^^^^^^^^
商向量空间使用通用的商记号（输入为 `\quot`，而非普通的 `/`）。投影到商空间的映射是 `Submodule.mkQ`，其万有性质由 `Submodule.liftQ` 给出。
EXAMPLES: -/
-- QUOTE:

variable (E : Submodule K V)

example : Module K (V ⧸ E) := inferInstance

example : V →ₗ[K] V ⧸ E := E.mkQ

example : ker E.mkQ = E := E.ker_mkQ

example : range E.mkQ = ⊤ := E.range_mkQ

example (hφ : E ≤ ker φ) : V ⧸ E →ₗ[K] W := E.liftQ φ hφ

example (F : Submodule K W) (hφ : E ≤ .comap φ F) : V ⧸ E →ₗ[K] W ⧸ F := E.mapQ F φ hφ

noncomputable example : (V ⧸ LinearMap.ker φ) ≃ₗ[K] range φ := φ.quotKerEquivRange

-- QUOTE.
/- TEXT:
作为练习，我们来证明商空间子空间的对应定理。Mathlib 中有一个稍微更精确的版本，称为 ``Submodule.comapMkQRelIso``。
EXAMPLES: -/
-- QUOTE:

open Submodule

#check Submodule.map_comap_eq
#check Submodule.comap_map_eq

example : Submodule K (V ⧸ E) ≃ { F : Submodule K V // E ≤ F } where
/- EXAMPLES:
  toFun := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry
SOLUTIONS: -/
  toFun F := ⟨comap E.mkQ F, by
    conv_lhs => rw [← E.ker_mkQ, ← comap_bot]
    gcongr
    apply bot_le⟩
  invFun P := map E.mkQ P
  left_inv P := by
    dsimp
    rw [Submodule.map_comap_eq, E.range_mkQ]
    exact top_inf_eq P
  right_inv := by
    intro P
    ext x
    dsimp only
    rw [Submodule.comap_map_eq, E.ker_mkQ, sup_of_le_left]
    exact P.2
-- QUOTE.
