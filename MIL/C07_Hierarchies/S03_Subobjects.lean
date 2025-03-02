import MIL.Common
import Mathlib.GroupTheory.QuotientGroup.Basic

set_option autoImplicit true

/- TEXT:
.. _section_hierarchies_subobjects:

子对象
-----------

定义了一些代数结构及其态射之后，下一步是考虑继承这种代数结构的集合，例如子群或子环。
这在很大程度上与我们之前的话题重叠。实际上， ``X`` 中的一个集合是作为从 ``X`` 到 ``Prop`` 的函数来实现的，因此子对象是满足特定谓词的函数。
因此，我们可以重用许多导致 ``DFunLike`` 类及其后代的想法。
我们不会重用 ``DFunLike`` 本身，因为这会破坏从 ``Set X`` 到 ``X → Prop`` 的抽象屏障。取而代之的是有一个 ``SetLike`` 类。该类不是将一个嵌入包装到函数类型中，而是将其包装到 ``Set`` 类型中，并定义相应的强制转换和 ``Membership`` 实例。

BOTH: -/

-- QUOTE:
@[ext]
structure Submonoid₁ (M : Type) [Monoid M] where
  /-- 子幺半群的载体。 -/
  carrier : Set M
  /-- 子幺半群中两个元素的乘积属于该子幺半群。 -/
  mul_mem {a b} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier
  /-- 单位元素属于子幺半群。 -/
  one_mem : 1 ∈ carrier

/-- `M` 中的子幺半群可以被视为 `M` 中的集合 -/
instance [Monoid M] : SetLike (Submonoid₁ M) M where
  coe := Submonoid₁.carrier
  coe_injective' _ _ := Submonoid₁.ext

-- QUOTE.

/- TEXT:
借助上述的 ``SetLike`` 实例，我们已经可以很自然地表述子幺半群 ``N`` 包含 ``1`` ，而无需使用 ``N.carrier`` 。
我们还可以将 ``N`` 作为 ``M`` 中的一个集合来处理，或者在映射下取其直接像。
BOTH: -/

-- QUOTE:
example [Monoid M] (N : Submonoid₁ M) : 1 ∈ N := N.one_mem

example [Monoid M] (N : Submonoid₁ M) (α : Type) (f : M → α) := f '' N
-- QUOTE.

/- TEXT:
我们还有一个到 ``Type`` 的强制转换，它使用 ``Subtype`` ，因此，给定一个子幺半群 ``N`` ，我们可以写一个参数 ``(x : N)`` ，其可以被强制转换为属于 ``N`` 的 ``M`` 的一个元素。
BOTH: -/

-- QUOTE:
example [Monoid M] (N : Submonoid₁ M) (x : N) : (x : M) ∈ N := x.property
-- QUOTE.

/- TEXT:
利用这种到 ``Type`` 的强制转换，我们还可以解决为子幺半群配备幺半群结构的任务。我们将使用上述与 ``N`` 相关联的类型的强制转换，以及断言这种强制转换是单射的引理 ``SetCoe.ext`` 。这两者均由 ``SetLike`` 实例提供。
BOTH: -/

-- QUOTE:
instance SubMonoid₁Monoid [Monoid M] (N : Submonoid₁ M) : Monoid N where
  mul := fun x y ↦ ⟨x*y, N.mul_mem x.property y.property⟩
  mul_assoc := fun x y z ↦ SetCoe.ext (mul_assoc (x : M) y z)
  one := ⟨1, N.one_mem⟩
  one_mul := fun x ↦ SetCoe.ext (one_mul (x : M))
  mul_one := fun x ↦ SetCoe.ext (mul_one (x : M))
-- QUOTE.

/- TEXT:
请注意，在上述实例中，我们本可以使用解构绑定器，而不是使用到 ``M`` 的强制转换并调用 ``property`` 字段，如下所示。
BOTH: -/

-- QUOTE:
example [Monoid M] (N : Submonoid₁ M) : Monoid N where
  mul := fun ⟨x, hx⟩ ⟨y, hy⟩ ↦ ⟨x*y, N.mul_mem hx hy⟩
  mul_assoc := fun ⟨x, _⟩ ⟨y, _⟩ ⟨z, _⟩ ↦ SetCoe.ext (mul_assoc x y z)
  one := ⟨1, N.one_mem⟩
  one_mul := fun ⟨x, _⟩ ↦ SetCoe.ext (one_mul x)
  mul_one := fun ⟨x, _⟩ ↦ SetCoe.ext (mul_one x)
-- QUOTE.

/- TEXT:
为了将关于子幺半群的引理应用于子群或子环，我们需要一个类，就像对于同态一样。请注意，这个类将一个 ``SetLike`` 实例作为参数，因此它不需要载体字段，并且可以在其字段中使用成员符号。
BOTH: -/

-- QUOTE:
class SubmonoidClass₁ (S : Type) (M : Type) [Monoid M] [SetLike S M] : Prop where
  mul_mem : ∀ (s : S) {a b : M}, a ∈ s → b ∈ s → a * b ∈ s
  one_mem : ∀ s : S, 1 ∈ s

instance [Monoid M] : SubmonoidClass₁ (Submonoid₁ M) M where
  mul_mem := Submonoid₁.mul_mem
  one_mem := Submonoid₁.one_mem
-- QUOTE.

/- TEXT:
作为练习，您应该定义一个 ``Subgroup₁`` 结构，为其赋予一个 ``SetLike`` 实例和一个 ``SubmonoidClass₁`` 实例，在与 ``Subgroup₁`` 相关联的子类型上放置一个 ``Group`` 实例，并定义一个 ``SubgroupClass₁`` 类。

SOLUTIONS: -/
@[ext]
structure Subgroup₁ (G : Type) [Group G] extends Submonoid₁ G where
  /-- The inverse of an element of a subgroup belongs to the subgroup. -/
  inv_mem {a} : a ∈ carrier → a⁻¹ ∈ carrier


/-- Subgroups in `M` can be seen as sets in `M`. -/
instance [Group G] : SetLike (Subgroup₁ G) G where
  coe := fun H ↦ H.toSubmonoid₁.carrier
  coe_injective' _ _ := Subgroup₁.ext

instance [Group G] (H : Subgroup₁ G) : Group H :=
{ SubMonoid₁Monoid H.toSubmonoid₁ with
  inv := fun x ↦ ⟨x⁻¹, H.inv_mem x.property⟩
  inv_mul_cancel := fun x ↦ SetCoe.ext (inv_mul_cancel (x : G)) }

class SubgroupClass₁ (S : Type) (G : Type) [Group G] [SetLike S G]
    extends SubmonoidClass₁ S G  : Prop where
  inv_mem : ∀ (s : S) {a : G}, a ∈ s → a⁻¹ ∈ s

instance [Group G] : SubmonoidClass₁ (Subgroup₁ G) G where
  mul_mem := fun H ↦ H.toSubmonoid₁.mul_mem
  one_mem := fun H ↦ H.toSubmonoid₁.one_mem

instance [Group G] : SubgroupClass₁ (Subgroup₁ G) G :=
{ (inferInstance : SubmonoidClass₁ (Subgroup₁ G) G) with
  inv_mem := Subgroup₁.inv_mem }

/- TEXT:
在 Mathlib 中，关于给定代数对象的子对象，还有一点非常重要，那就是它们总是构成一个完备格，这种结构被大量使用。例如，您可能会寻找一个关于子幺半群交集仍是子幺半群的引理。但这不会是一个引理，而是一个下确界构造。我们来看两个子幺半群的情况。
BOTH: -/

-- QUOTE:
instance [Monoid M] : Inf (Submonoid₁ M) :=
  ⟨fun S₁ S₂ ↦
    { carrier := S₁ ∩ S₂
      one_mem := ⟨S₁.one_mem, S₂.one_mem⟩
      mul_mem := fun ⟨hx, hx'⟩ ⟨hy, hy'⟩ ↦ ⟨S₁.mul_mem hx hy, S₂.mul_mem hx' hy'⟩ }⟩
-- QUOTE.

/- TEXT:
这使得两个子幺半群的交集能够作为一个子幺半群得到。
BOTH: -/

-- QUOTE:
example [Monoid M] (N P : Submonoid₁ M) : Submonoid₁ M := N ⊓ P
-- QUOTE.

/- TEXT:
您可能会觉得在上面的例子中使用下确界符号 ``⊓`` 而不是交集符号 ``∩`` 很遗憾。但想想上确界。两个子幺半群的并集不是子幺半群。然而，子幺半群仍然构成一个格（甚至是完备格）。实际上， ``N ⊔ P`` 是由 ``N`` 和 ``P`` 的并集生成的子幺半群，当然用 ``N ∪ P`` 来表示会非常令人困惑。所以您可以看到使用 ``N ⊓ P`` 要一致得多。在各种代数结构中，这种表示法也更加一致。一开始看到两个子空间 ``E`` 和 ``F`` 的和用 ``E ⊔ F`` 而不是 ``E + F`` 表示可能会觉得有点奇怪。但您会习惯的。很快你就会觉得 ``E + F`` 这种表示法是一种干扰，它强调的是一个偶然的事实，即 ``E ⊔ F`` 的元素可以写成 ``E`` 的一个元素与 ``F`` 的一个元素之和，而不是强调 ``E ⊔ F`` 是包含 ``E`` 和 ``F`` 的最小向量子空间这一根本事实。

本章的最后一个主题是商的概念。同样，我们想要解释在 Mathlib 中如何构建方便的符号表示法以及如何避免代码重复。这里的主要手段是 ``HasQuotient`` 类，它允许使用诸如 ``M ⧸ N`` 这样的符号表示法。请注意，商符号 ``⧸`` 是一个特殊的 Unicode 字符，而不是普通的 ASCII 除法符号。

例如，我们将通过一个子幺半群来构建一个交换幺半群的商，证明留给你。在最后一个示例中，您可以使用 ``Setoid.refl`` ，但它不会自动获取相关的 ``Setoid`` 结构。您可以使用 ``@`` 语法提供所有参数来解决此问题，例如 ``@Setoid.refl M N.Setoid`` 。
BOTH: -/

-- QUOTE:
def Submonoid.Setoid [CommMonoid M] (N : Submonoid M) : Setoid M  where
  r := fun x y ↦ ∃ w ∈ N, ∃ z ∈ N, x*w = y*z
  iseqv := {
    refl := fun x ↦ ⟨1, N.one_mem, 1, N.one_mem, rfl⟩
    symm := fun ⟨w, hw, z, hz, h⟩ ↦ ⟨z, hz, w, hw, h.symm⟩
    trans := by
/- EXAMPLES:
      sorry
SOLUTIONS: -/
      rintro a b c ⟨w, hw, z, hz, h⟩ ⟨w', hw', z', hz', h'⟩
      refine ⟨w*w', N.mul_mem hw hw', z*z', N.mul_mem hz hz', ?_⟩
      rw [← mul_assoc, h, mul_comm b, mul_assoc, h', ← mul_assoc, mul_comm z, mul_assoc]
-- BOTH:
  }

instance [CommMonoid M] : HasQuotient M (Submonoid M) where
  quotient' := fun N ↦ Quotient N.Setoid

def QuotientMonoid.mk [CommMonoid M] (N : Submonoid M) : M → M ⧸ N := Quotient.mk N.Setoid

instance [CommMonoid M] (N : Submonoid M) : Monoid (M ⧸ N) where
  mul := Quotient.map₂' (· * ·) (by
/- EXAMPLES:
      sorry
SOLUTIONS: -/
    rintro a₁ b₁ ⟨w, hw, z, hz, ha⟩ a₂ b₂ ⟨w', hw', z', hz', hb⟩
    refine ⟨w*w', N.mul_mem hw hw', z*z', N.mul_mem hz hz', ?_⟩
    rw [mul_comm w, ← mul_assoc, mul_assoc a₁, hb, mul_comm, ← mul_assoc, mul_comm w, ha,
        mul_assoc, mul_comm z, mul_assoc b₂, mul_comm z', mul_assoc]
-- BOTH:
        )
  mul_assoc := by
/- EXAMPLES:
      sorry
SOLUTIONS: -/
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩
    apply Quotient.sound
    dsimp only
    rw [mul_assoc]
    apply @Setoid.refl M N.Setoid
-- BOTH:
  one := QuotientMonoid.mk N 1
  one_mul := by
/- EXAMPLES:
      sorry
SOLUTIONS: -/
    rintro ⟨a⟩ ; apply Quotient.sound ; dsimp only ; rw [one_mul] ; apply @Setoid.refl M N.Setoid
-- BOTH:
  mul_one := by
/- EXAMPLES:
      sorry
SOLUTIONS: -/
    rintro ⟨a⟩ ; apply Quotient.sound ; dsimp only ; rw [mul_one] ; apply @Setoid.refl M N.Setoid
-- QUOTE.
