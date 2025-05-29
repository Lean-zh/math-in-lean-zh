-- BOTH:
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Charpoly.Basic

import MIL.Common

/- TEXT:
向量空间与线性映射
--------------------

向量空间
^^^^^^^^^

.. index:: vector space

我们将直接从抽象线性代数开始，讨论定义在任意域上的向量空间。 不过，你也可以在 :numref:`Section %s <matrices>` 中找到关于矩阵的信息，该部分在逻辑上并不依赖于本抽象理论。Mathlib 实际上处理的是更广义的线性代数，使用模（module）一词，但现在我们暂时当作这只是一个古怪的拼写习惯。

“设 :math:`K` 是一个域，且 :math:`V` 是定义在 :math:`K` 上的向量空间”（并将其作为后续结论的隐式参数）的表达方式是：
EXAMPLES: -/

-- QUOTE:

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
-- QUOTE.

/- TEXT:

我们在 :numref:`Chapter %s <hierarchies>` 中解释了为什么需要两个独立的类型类 `[AddCommGroup V]` 和 `[Module K V]`。

简而言之，数学上我们想表达的是：拥有一个域 :math:`K` 上的向量空间结构意味着拥有一个加法交换群结构。虽然可以告诉 Lean 这一点，但如果这样做，每当 Lean 需要在类型 :math:`V` 上寻找该群结构时，它就会尝试去寻找带有完全未指定域 :math:`K` 的向量空间结构，而这个 :math:`K` 无法从 :math:`V` 中推断出来。
这会严重影响类型类合成系统的效率和稳定性。

向量 `v` 与标量 `a` 的乘法记作 `a • v`。下面示例列举了该操作与加法之间的若干代数规则。当然，`simp` 或 `apply?` 策略可以自动找到这些证明。还有一个 `module` 策略，类似于在交换环中使用 `ring` 策略、在群中使用 `group` 策略，可以根据向量空间和域的公理自动解决相关目标。但需要记住的是，在引理名称中，标量乘法通常缩写为 `smul`。

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
作为对更高级读者的简要提示，正如术语所暗示的那样，Mathlib 的线性代数不仅涵盖了定义在（不一定是交换）环上的模（modules）。事实上，它甚至涵盖了半环上的半模（semi-modules）。如果你认为不需要如此广泛的泛化，可以思考下面这个例子，它很好地体现了理想对子模作用的许多代数规则：

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

接下来我们需要引入线性映射。类似于群同态，Mathlib 中的线性映射是“打包”的映射，即由一个映射和其线性性质证明组成的整体。这些打包映射在应用时会自动转换为普通函数。关于这一设计的更多信息，请参见 :numref:`Chapter %s <hierarchies>`。

两个域 ``K`` 上的向量空间 ``V`` 和 ``W`` 之间的线性映射类型记作 ``V →ₗ[K] W`` ，其中下标的 `l` 表示“linear”（线性）。一开始在符号中显式指定 ``K`` 可能感觉有些奇怪，但当涉及多个域时，这一点尤为重要。例如，从复数域 :math:`ℂ` 到 :math:`ℂ` 的实线性映射形式为 :math:`z ↦ az + b\bar{z}` ，而复线性映射则仅限于形式为 :math:`z ↦ az` 的映射，这一区别在复分析中极为关键。

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
注意，`V →ₗ[K] W` 本身也携带了丰富的代数结构（这也是将这些映射打包的动机之一）。
它是一个 `K`-向量空间，因此我们可以对线性映射进行加法运算，也可以对它们进行标量乘法。
EXAMPLES: -/
-- QUOTE:
variable (ψ : V →ₗ[K] W)

#check (2 • φ + ψ : V →ₗ[K] W)

-- QUOTE.

/- TEXT:
使用打包映射的一个缺点是，无法直接使用普通函数的组合运算。
我们需要使用专门的组合函数 `LinearMap.comp`，或者使用专用符号 `∘ₗ` 来表示线性映射的组合。
EXAMPLES: -/
-- QUOTE:
variable (θ : W →ₗ[K] V)

#check (φ.comp θ : W →ₗ[K] W)
#check (φ ∘ₗ θ : W →ₗ[K] W)
-- QUOTE.

/- TEXT:
构造线性映射主要有两种方式。第一种是通过提供函数本体和线性性质的证明来构建该结构。
通常，可以借助代码操作快速完成：你只需输入 ``example : V →ₗ[K] V := _`` 然后对下划线使用“生成骨架”（Generate a skeleton）代码操作，即可自动生成所需的结构框架。
EXAMPLES: -/
-- QUOTE:

example : V →ₗ[K] V where
  toFun v := 3 • v
  map_add' _ _ := smul_add ..
  map_smul' _ _ := smul_comm ..

-- QUOTE.

/- TEXT:
你可能会好奇为什么 `LinearMap` 结构中用于证明的字段名称都带有撇号。这是因为这些证明是在函数强制转换（coercion）之前定义的，因此它们是基于 `LinearMap.toFun` 表达的。随后，它们又被重新表达为基于函数强制转换的 `LinearMap.map_add` 和 `LinearMap.map_smul`。事情还没结束。我们还需要一个适用于任意保持加法的（打包）映射的 `map_add` 版本，比如加法群同态、线性映射、连续线性映射、`K`-代数映射等。这个版本是定义在根命名空间的 `map_add`。而中间版本 `LinearMap.map_add` 虽有些冗余，但支持点记法（dot notation），在某些情况下使用起来更方便。`map_smul` 也有类似情况。整体框架请参见 :numref:`Chapter %s <hierarchies>` 的详细解释。
EXAMPLES: -/
-- QUOTE:

#check (φ.map_add' : ∀ x y : V, φ.toFun (x + y) = φ.toFun x + φ.toFun y)
#check (φ.map_add : ∀ x y : V, φ (x + y) = φ x + φ y)
#check (map_add φ : ∀ x y : V, φ (x + y) = φ x + φ y)

-- QUOTE.

/- TEXT:
我们也可以利用 Mathlib 中已有的线性映射，通过各种组合子（combinators）来构造新的线性映射。
例如，上述例子已经在 Mathlib 中以 `LinearMap.lsmul K V 3` 的形式存在。这里 `K` 和 `V` 是显式参数，原因有几个：最主要的是，如果只写 `LinearMap.lsmul 3`，Lean 无法推断出 `V`，甚至无法推断出 `K`。此外，`LinearMap.lsmul K V` 本身也是一个有趣的对象：它的类型是 ``K →ₗ[K] V →ₗ[K] V`` ，意味着它是一个从域 `K`（视为其自身上的向量空间）到从 `V` 到 `V` 的 `K`-线性映射空间的线性映射。
EXAMPLES: -/
-- QUOTE:

#check (LinearMap.lsmul K V 3 : V →ₗ[K] V)
#check (LinearMap.lsmul K V : K →ₗ[K] V →ₗ[K] V)

-- QUOTE.

/- TEXT:
还有一个线性同构类型 `LinearEquiv`，用符号表示为 ``V ≃ₗ[K] W`` ，对于 `f : V ≃ₗ[K] W`，它的逆映射是 ``f.symm : W ≃ₗ[K] V`` 。两个线性同构 `f` 和 `g` 的复合是 ``f.trans g`` ，也可用符号 ``f ≪≫ₗ g`` 表示。`V` 的恒等同构是 ``LinearEquiv.refl K V`` ，该类型的元素在需要时会自动强制转换为对应的同态映射或函数。
EXAMPLES: -/
-- QUOTE:
example (f : V ≃ₗ[K] W) : f ≪≫ₗ f.symm = LinearEquiv.refl K V :=
  f.self_trans_symm
-- QUOTE.

/- TEXT:
可以使用 `LinearEquiv.ofBijective` 从一个双射的同态构造线性同构。这样构造的逆映射函数是不可计算的。
EXAMPLES: -/
-- QUOTE:
noncomputable example (f : V →ₗ[K] W) (h : Function.Bijective f) : V ≃ₗ[K] W :=
  .ofBijective f h
-- QUOTE.

/- TEXT:
请注意，在上述例子中，Lean 利用声明的类型自动识别 `.ofBijective` 是指 `LinearEquiv.ofBijective`，无需显式打开命名空间。

向量空间的直和与直积
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

我们可以利用已有的向量空间，通过直和和直积构造新的向量空间。从两个向量空间开始，在该情形下直和与直积无区别，我们可以直接使用积类型。下面的代码片段展示了如何将所有结构映射（含入（inclusion）映射和投影映射）构造为线性映射，以及构造映射到积空间和从和空间出的万有性质（universal properties）。如果你对范畴论中和与积的区别不熟悉，可以忽略“万有性质”相关术语，专注于示例中的类型即可。
EXAMPLES: -/
-- QUOTE:

section binary_product

variable {W : Type*} [AddCommGroup W] [Module K W]
variable {U : Type*} [AddCommGroup U] [Module K U]
variable {T : Type*} [AddCommGroup T] [Module K T]

-- 第一投影映射
example : V × W →ₗ[K] V := LinearMap.fst K V W

-- 第二投影映射
example : V × W →ₗ[K] W := LinearMap.snd K V W

-- 直积的万有性质
example (φ : U →ₗ[K] V) (ψ : U →ₗ[K] W) : U →ₗ[K]  V × W := LinearMap.prod φ ψ

-- 直积映射满足预期行为，第一分量
example (φ : U →ₗ[K] V) (ψ : U →ₗ[K] W) : LinearMap.fst K V W ∘ₗ LinearMap.prod φ ψ = φ := rfl

-- 直积映射满足预期行为，第二分量
example (φ : U →ₗ[K] V) (ψ : U →ₗ[K] W) : LinearMap.snd K V W ∘ₗ LinearMap.prod φ ψ = ψ := rfl

-- 我们也可以并行组合映射
example (φ : V →ₗ[K] U) (ψ : W →ₗ[K] T) : (V × W) →ₗ[K] (U × T) := φ.prodMap ψ

-- 这只是通过将投影与万有性质结合实现
example (φ : V →ₗ[K] U) (ψ : W →ₗ[K] T) :
  φ.prodMap ψ = (φ ∘ₗ .fst K V W).prod (ψ ∘ₗ .snd K V W) := rfl

-- 第一包含（inclusion）映射
example : V →ₗ[K] V × W := LinearMap.inl K V W

-- 第二含入映射
example : W →ₗ[K] V × W := LinearMap.inr K V W

-- 直和（又称余积）的万有性质
example (φ : V →ₗ[K] U) (ψ : W →ₗ[K] U) : V × W →ₗ[K] U := φ.coprod ψ

-- 余积映射满足预期行为，第一分量
example (φ : V →ₗ[K] U) (ψ : W →ₗ[K] U) : φ.coprod ψ ∘ₗ LinearMap.inl K V W = φ :=
  LinearMap.coprod_inl φ ψ

-- 余积映射满足预期行为，第二分量
example (φ : V →ₗ[K] U) (ψ : W →ₗ[K] U) : φ.coprod ψ ∘ₗ LinearMap.inr K V W = ψ :=
  LinearMap.coprod_inr φ ψ

-- 余积映射的定义符合预期
example (φ : V →ₗ[K] U) (ψ : W →ₗ[K] U) (v : V) (w : W) :
    φ.coprod ψ (v, w) = φ v + ψ w :=
  rfl

end binary_product

-- QUOTE.
/- TEXT:
现在我们转向任意族向量空间的直和与直积。这里我们将展示如何定义一个向量空间族，并访问直和与直积的万有性质。请注意，直和符号限定在 `DirectSum` 命名空间中，且直和的万有性质要求索引类型具备可判定等价性（这在某种程度上是实现上的偶然情况）。
EXAMPLES: -/

-- QUOTE:
section families
open DirectSum

variable {ι : Type*} [DecidableEq ι]
         (V : ι → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]

-- 直和的万有性质将从各个直和因子映射出的映射组装成从直和映射出的映射
example (φ : Π i, (V i →ₗ[K] W)) : (⨁ i, V i) →ₗ[K] W :=
  DirectSum.toModule K ι W φ

-- 直积的万有性质将映射到各个因子的映射组装成映射到直积
example (φ : Π i, (W →ₗ[K] V i)) : W →ₗ[K] (Π i, V i) :=
  LinearMap.pi φ

-- 来自直积的投影映射
example (i : ι) : (Π j, V j) →ₗ[K] V i := LinearMap.proj i

-- 含入映射到直和
example (i : ι) : V i →ₗ[K] (⨁ i, V i) := DirectSum.lof K ι V i

-- 含入映射到直积
example (i : ι) : V i →ₗ[K] (Π i, V i) := LinearMap.single K V i

-- 若 `ι` 是有限类型，直和与直积之间存在线性同构
example [Fintype ι] : (⨁ i, V i) ≃ₗ[K] (Π i, V i) :=
  linearEquivFunOnFintype K ι V

end families
-- QUOTE.
