-- BOTH:
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Charpoly.Basic

import MIL.Common

/- TEXT:

向量空间和线性映射
-----------------------------

向量空间
^^^^^^^^^^^^^

.. index:: vector space

We will start directly abstract linear algebra, taking place in a vector space over any field.
However you can find information about matrices in
:numref:`Section %s <matrices>` which does not logically depend on this abstract theory.
Mathlib actually deals with a more general version of linear algebra involving the word module,
but for now we will pretend this is only an eccentric spelling habit.

我们将直接开始抽象线性代数，它发生在任何域上的向量空间中。然而，您可以在
:numref:`Section %s <matrices>` 中找到关于矩阵的信息，这并不依赖于这个抽象理论。Mathlib实际上处
理的是涉及模的更一般的线性代数版本，但现在我们将假装这只是一种古怪的拼写习惯。

The way to say “let :math:`K` be a field and let :math:`V` be a vector space over :math:`K`”
(and make them implicit arguments to later results) is:

表述“设 :math:`K` 是一个域，并且设 :math:`V` 是 :math:`K` 上的一个向量空间”（并将它们作为后来的
结果的隐式参数）的方法是：

EXAMPLES: -/

-- QUOTE:

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
-- QUOTE.

/- TEXT:
We explained in :numref:`Chapter %s <hierarchies>` why we need two separate
typeclasses ``[AddCommGroup V] [Module K V]``.
The short version is the following.
Mathematically we want to say that having a :math:`K`-vector space structure
implies having an additive commutative group structure.
We could tell this to Lean. But then whenever Lean would need to find such a
group structure on a type :math:`V`, it would go hunting for vector space
structures using a *completely unspecified* field :math:`K` that cannot be inferred
from :math:`V`.
This would be very bad for the type class synthesis system.

我们在 :numref:`第%s章 <hierarchies>` 中解释了为什么需要两个独立的类型类 
``[AddCommGroup V] [Module K V]``。简而言之，数学上我们希望表示，拥有一个 :math:`K`-向量空间结
构隐含着拥有一个加法交换群结构。我们可以将这一点告知 Lean。但是，如果这样做，那么每当 Lean 需要
在某个类型 :math:`V` 上找到一个群结构时，它将会开始寻找向量空间结构，但使用的是一个*完全不确定*
的字段 :math:`K`，而这个字段无法从 :math:`V` 中推导出来。这对类型类综合系统而言将非常不利。

The multiplication of a vector `v` by a scalar `a` is denoted by
`a • v`. We list a couple of algebraic rules about the interaction of this
operation with addition in the following examples. Of course `simp` or `apply?`
would find those proofs. There is also a `module` tactic that solves goals
following from the axioms of vector spaces and fields, in the same way the
`ring` tactic is used in commutative rings or the `group` tactic is used in
groups. But it is still useful to remember that scalar
multiplication is abbreviated `smul` in lemma names.

向量 v 与标量 a 的乘积记为`a • v`。我们在以下示例中列出了一些关于此运算与加法交互的代数规则。
当然，`simp` 或 `apply?` 可以找到这些证明。还有一个 `module` 策略，可以解决基于向量空间和域公理
的目标，就像`ring` 策略用于交换环、`group` 策略用于群一样。但仍然有必要记住，在引理名称中，标量
乘法简写为 `smul`。

EXAMPLES: -/

-- QUOTE:
example (a : K) (u v : V) : a • (u + v) = a • u + a • v :=
  smul_add a u v

example (a b : K) (u : V) : (a + b) • u = a • u + b • u :=
  add_smul a b u

example (a b : K) (u : V) : a • b • u = b • a • u :=
  smul_comm a b u

-- QUOTE.
/- TEXT:
As a quick note for more advanced readers, let us point out that, as suggested by
terminology, Mathlib’s linear algebra also covers modules over (not necessarily commutative)
rings.

给进阶读者的一个简要提示，正如术语所暗示的那样，Mathlib 的线性代数还涵盖了（不一定交换的）环上
的模。

In fact it even covers semi-modules over semi-rings. If you think you do not need
this level of generality, you can meditate the following example that nicely captures
a lot of algebraic rules about ideals acting on submodules:

实际上，它甚至涵盖了半环上的半模。如果你认为不需要这种层次的普遍性，可以思考下面的例子，它很好
地捕捉了理想作用于子模的许多代数规则：

EXAMPLES: -/
-- QUOTE:
example {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] :
    Module (Ideal R) (Submodule R M) :=
  inferInstance


-- QUOTE.
/- TEXT:
线性映射
^^^^^^^^^^^

.. index:: linear map

Next we need linear maps. Like group morphisms, linear maps in Mathlib are bundled maps, i.e. packages
made of a map and proofs of its linearity properties.
Those bundled maps are converted to ordinary functions when applied.
See :numref:`Chapter %s <hierarchies>` for more information about this design.

接下来我们需要线性映射。与群同态类似，Mathlib 中的线性映射是捆绑映射，即由一个映射及其线性性质
的证明组成的包。当应用这些捆绑映射时，它们会被转换为普通函数。有关此设计的更多信息，请参见
:numref:Chapter %s <hierarchies>。

The type of linear maps between two ``K``-vector spaces
``V`` and ``W`` is denoted by ``V →ₗ[K] W``. The subscript `l` stands for linear.
At first it may feel odd to specify ``K`` in this notation.
But this is crucial when several fields come into play.
For instance real-linear maps from :math:`ℂ` to :math:`ℂ` are every map :math:`z ↦ az + b\bar{z}`
while only the maps :math:`z ↦ az` are complex linear, and this difference is crucial in
complex analysis.

两个 ``K``-向量空间 ``V`` 和 ``W`` 之间的线性映射类型记为 ``V →ₗ[K] W``。下标 `l` 表示线性。
起初在此符号中指定 ``K`` 可能会感觉有些奇怪，但当涉及多个字段时，这一点至关重要。例如，从
:math:`ℂ` 到 :math:`ℂ` 的实线性映射是每个形如 :math:`z ↦ az + b\bar{z}` 的映射，而仅有形如
:math:`z ↦ az` 的映射是复线性的，这一区别在复分析中至关重要。

EXAMPLES: -/
-- QUOTE:

variable {W : Type*} [AddCommGroup W] [Module K W]

variable (φ : V →ₗ[K] W)

example (a : K) (v : V) : φ (a • v) = a • φ v :=
  map_smul φ a v

example (v w : V) : φ (v + w) = φ v + φ w :=
  map_add φ v w

-- QUOTE.

/- TEXT:
Note that ``V →ₗ[K] W`` itself carries interesting algebraic structures (this
is part of the motivation for bundling those maps).
It is a ``K``-vector space so we can add linear maps and multiply them by scalars.

注意，``V →ₗ[K] W`` 本身带有有趣的代数结构（这也是将这些映射捆绑在一起的动机之一）。
它是一个 ``K``-向量空间，因此我们可以对线性映射进行加法运算，并用标量对其进行乘法运算。

EXAMPLES: -/
-- QUOTE:
variable (ψ : V →ₗ[K] W)

#check (2 • φ + ψ : V →ₗ[K] W)

-- QUOTE.

/- TEXT:
One downside of using bundled maps is that we cannot use ordinary function composition.
We need to use ``LinearMap.comp`` or the notation ``∘ₗ``.

使用捆绑映射的一个缺点是我们无法使用普通的函数复合。我们需要使用 ``LinearMap.comp`` 或符号 ``∘ₗ``。

EXAMPLES: -/
-- QUOTE:
variable (θ : W →ₗ[K] V)

#check (φ.comp θ : W →ₗ[K] W)
#check (φ ∘ₗ θ : W →ₗ[K] W)
-- QUOTE.

/- TEXT:
There are two main ways to construct linear maps.
First we can build the structure by providing the function and the linearity proof.
As usual, this is facilitated by the structure code action: you can type
``example : V →ₗ[K] V := _`` and use the code action “Generate a skeleton” attached to the
underscore.

构造线性映射主要有两种方法。首先，我们可以通过提供函数和线性性的证明来构建该结构。
通常，这可以通过结构代码操作来实现：你可以输入 ``example : V →ₗ[K] V := _``，然后使用附加在
下划线上的代码操作“生成骨架”。

EXAMPLES: -/
-- QUOTE:

example : V →ₗ[K] V where
  toFun v := 3 • v
  map_add' _ _ := smul_add ..
  map_smul' _ _ := smul_comm ..

-- QUOTE.

/- TEXT:
You may wonder why the proof fields of ``LinearMap`` have names ending with a prime.
This is because they are defined before the coercion to functions is defined, hence they are
phrased in terms of ``LinearMap.toFun``. Then they are restated as ``LinearMap.map_add``
and ``LinearMap.map_smul`` in terms of the coercion to function.

你可能会好奇为什么 ``LinearMap`` 的证明字段名称以撇号结尾。这是因为这些字段是在定义为函数的
强制转换之前定义的，因此它们是基于 ``LinearMap.toFun`` 表述的。然后它们在转换为函数后重新表
述为 ``LinearMap.map_add`` 和 ``LinearMap.map_smul``。

This is not yet the end of the story. One also wants a version of ``map_add`` that applies to
any (bundled) map preserving addition, such as additive group morphisms, linear maps, continuous
linear maps, ``K``-algebra maps etc… This one is ``map_add`` (in the root namespace).
The intermediate version, ``LinearMap.map_add`` is a bit redundant but allows to use dot notation, which
can be nice sometimes. A similar story exists for ``map_smul``, and the general framework
is explained in :numref:`Chapter %s <hierarchies>`.

这还不是故事的结尾。我们还希望有一个适用于任何保持加法的（捆绑）映射的 ``map_add`` 版本，
比如加法群同态、线性映射、连续线性映射、``K``-代数映射等。这一版本是根命名空间中的 ``map_add``。
中间版本 ``LinearMap.map_add`` 有点冗余，但允许使用点表示法，有时会很方便。类似的情况也适用于
``map_smul``，整体框架在 :numref:`Chapter %s <hierarchies>` 中有详细说明。

EXAMPLES: -/
-- QUOTE:

#check (φ.map_add' : ∀ x y : V, φ.toFun (x + y) = φ.toFun x + φ.toFun y)
#check (φ.map_add : ∀ x y : V, φ (x + y) = φ x + φ y)
#check (map_add φ : ∀ x y : V, φ (x + y) = φ x + φ y)

-- QUOTE.

/- TEXT:
One can also build linear maps from the ones that are already defined in Mathlib
using various combinators.
For instance the above example is already known as ``LinearMap.lsmul K V 3``.
There are several reason why ``K`` and ``V`` are explicit arguments here.
The most pressing one is that from a bare ``LinearMap.lsmul 3`` there would be no way
for Lean to infer ``V`` or even ``K``.
But also ``LinearMap.lsmul K V`` is an interesting object by itself: it has type
``K →ₗ[K] V →ₗ[K] V``, meaning it is a ``K``-linear map from ``K``
—seen as a vector space over itself— to the space of ``K``-linear maps from ``V`` to ``V``.

还可以通过各种组合器，从 Mathlib 中已定义的线性映射构造新的线性映射。例如，上述示例已被称为
``LinearMap.lsmul K V 3``。这里将 ``K`` 和 ``V`` 作为显式参数有几个原因。最主要的原因是，如果只有
``LinearMap.lsmul 3``，Lean 将无法推断出 ``V`` 或甚至 ``K``。另外，``LinearMap.lsmul K V`` 本身也
是一个有趣的对象：它的类型为 ``K →ₗ[K] V →ₗ[K] V``，这意味着它是一个从 ``K``（视为其自身上的向量空间）
到 ``K`` 线性映射空间 ``V`` 到 ``V`` 的 ``K``-线性映射。
EXAMPLES: -/
-- QUOTE:

#check (LinearMap.lsmul K V 3 : V →ₗ[K] V)
#check (LinearMap.lsmul K V : K →ₗ[K] V →ₗ[K] V)

-- QUOTE.

/- TEXT:
There is also a type ``LinearEquiv`` of linear isomorphisms denoted by ``V ≃ₗ[K] W``.
The inverse of ``f : V ≃ₗ[K] W`` is ``f.symm : W ≃ₗ[K] V``,
composition of ``f`` and ``g`` is ``f.trans g`` also denoted by ``f ≪≫ₗ g``, and
the identity isomorphism of ``V`` is ``LinearEquiv.refl K V``.
Elements of this type are automatically coerced to morphisms and functions when necessary.

还有一个表示线性同构的类型 ``LinearEquiv``，记作 ``V ≃ₗ[K] W``。对于 ``f : V ≃ₗ[K] W``，其逆映射为 
``f.symm : W ≃ₗ[K] V``，``f`` 和 ``g`` 的复合为 ``f.trans g``，也可以记作 ``f ≪≫ₗ g``，``V`` 的恒等
同构为 ``LinearEquiv.refl K V``。该类型的元素在必要时会自动转换为态射和函数。
EXAMPLES: -/
-- QUOTE:
example (f : V ≃ₗ[K] W) : f ≪≫ₗ f.symm = LinearEquiv.refl K V :=
  f.self_trans_symm
-- QUOTE.

/- TEXT:
One can use ``LinearEquiv.ofBijective`` to build an isomorphism from a bijective morphism.
Doing so makes the inverse function noncomputable.

可以使用 ``LinearEquiv.ofBijective`` 从双射态射构建同构。这样做会使逆函数变为不可计算的（noncomputable）。
EXAMPLES: -/
-- QUOTE:
noncomputable example (f : V →ₗ[K] W) (h : Function.Bijective f) : V ≃ₗ[K] W :=
  .ofBijective f h
-- QUOTE.

/- TEXT:
Note that in the above example, Lean uses the announced type to understand that ``.ofBijective``
refers to ``LinearEquiv.ofBijective`` (without needing to open any namespace).

请注意，在上述示例中，Lean 使用已声明的类型来理解 ``.ofBijective`` 指的是 ``LinearEquiv.ofBijective``
（无需打开任何命名空间）。

向量空间的和与积
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

We can build new vector spaces out of old ones using direct sums and direct
products.
Let us start with two vectors spaces. In this case there is no difference between sum and product,
and we can simply use the product type.
In the following snippet of code we simply show how to get all the structure maps (inclusions
and projections) as linear maps, as well as the universal properties constructing linear maps
into products and out of sums (if you are not familiar with the category-theoretic distinction
between sums and products, you can simply ignore the universal property vocabulary and focus
on the types of the following examples).

我们可以通过直和与直积从已有的向量空间构建新的向量空间。让我们从两个向量空间开始。在这种情况下，
和与积没有区别，我们可以直接使用乘积类型。在以下代码片段中，我们展示了如何获得所有结构映射（包含映射
和投影）作为线性映射，以及如何通过通用性质构造到乘积的线性映射和从和出的线性映射（如果你不熟悉范畴论
中和与积的区别，可以简单忽略通用性质的术语，专注于以下示例的类型）。
EXAMPLES: -/
-- QUOTE:

section binary_product

variable {W : Type*} [AddCommGroup W] [Module K W]
variable {U : Type*} [AddCommGroup U] [Module K U]
variable {T : Type*} [AddCommGroup T] [Module K T]

-- First projection map
example : V × W →ₗ[K] V := LinearMap.fst K V W

-- Second projection map
example : V × W →ₗ[K] W := LinearMap.snd K V W

-- Universal property of the product
example (φ : U →ₗ[K] V) (ψ : U →ₗ[K] W) : U →ₗ[K]  V × W := LinearMap.prod φ ψ

-- The product map does the expected thing, first component
example (φ : U →ₗ[K] V) (ψ : U →ₗ[K] W) : LinearMap.fst K V W ∘ₗ LinearMap.prod φ ψ = φ := rfl

-- The product map does the expected thing, second component
example (φ : U →ₗ[K] V) (ψ : U →ₗ[K] W) : LinearMap.snd K V W ∘ₗ LinearMap.prod φ ψ = ψ := rfl

-- We can also combine maps in parallel
example (φ : V →ₗ[K] U) (ψ : W →ₗ[K] T) : (V × W) →ₗ[K] (U × T) := φ.prodMap ψ

-- This is simply done by combining the projections with the universal property
example (φ : V →ₗ[K] U) (ψ : W →ₗ[K] T) :
  φ.prodMap ψ = (φ ∘ₗ .fst K V W).prod (ψ ∘ₗ .snd K V W) := rfl

-- First inclusion map
example : V →ₗ[K] V × W := LinearMap.inl K V W

-- Second inclusion map
example : W →ₗ[K] V × W := LinearMap.inr K V W

-- Universal property of the sum (aka coproduct)
example (φ : V →ₗ[K] U) (ψ : W →ₗ[K] U) : V × W →ₗ[K] U := φ.coprod ψ

-- The coproduct map does the expected thing, first component
example (φ : V →ₗ[K] U) (ψ : W →ₗ[K] U) : φ.coprod ψ ∘ₗ LinearMap.inl K V W = φ :=
  LinearMap.coprod_inl φ ψ

-- The coproduct map does the expected thing, second component
example (φ : V →ₗ[K] U) (ψ : W →ₗ[K] U) : φ.coprod ψ ∘ₗ LinearMap.inr K V W = ψ :=
  LinearMap.coprod_inr φ ψ

-- The coproduct map is defined in the expected way
example (φ : V →ₗ[K] U) (ψ : W →ₗ[K] U) (v : V) (w : W) :
    φ.coprod ψ (v, w) = φ v + ψ w :=
  rfl

end binary_product

-- QUOTE.
/- TEXT:
Let us now turn to sums and products of arbitrary families of vector spaces.
Here we will simply see how to define a family of vector spaces and access the universal
properties of sums and products.
Note that the direct sum notation is scoped to the ``DirectSum`` namespace, and
that the universal property of direct sums requires decidable equality on the
indexing type (this is somehow an implementation accident).

现在让我们转向任意向量空间族的和与积。在这里，我们将简单了解如何定义向量空间族，并访问和与积的通用性质。
请注意，直和符号限定在 ``DirectSum`` 命名空间中，且直和的通用性质需要索引类型具有可判定的相等性（这在某
种程度上是实现上的偶然情况）。
EXAMPLES: -/

-- QUOTE:
section families
open DirectSum

variable {ι : Type*} [DecidableEq ι]
         (V : ι → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]

-- The universal property of the direct sum assembles maps from the summands to build
-- a map from the direct sum
example (φ : Π i, (V i →ₗ[K] W)) : (⨁ i, V i) →ₗ[K] W :=
  DirectSum.toModule K ι W φ

-- The universal property of the direct product assembles maps into the factors
-- to build a map into the direct product
example (φ : Π i, (W →ₗ[K] V i)) : W →ₗ[K] (Π i, V i) :=
  LinearMap.pi φ

-- The projection maps from the product
example (i : ι) : (Π j, V j) →ₗ[K] V i := LinearMap.proj i

-- The inclusion maps into the sum
example (i : ι) : V i →ₗ[K] (⨁ i, V i) := DirectSum.lof K ι V i

-- The inclusion maps into the product
example (i : ι) : V i →ₗ[K] (Π i, V i) := LinearMap.single K V i

-- In case `ι` is a finite type, there is an isomorphism between the sum and product.
example [Fintype ι] : (⨁ i, V i) ≃ₗ[K] (Π i, V i) :=
  linearEquivFunOnFintype K ι V

end families
-- QUOTE.
