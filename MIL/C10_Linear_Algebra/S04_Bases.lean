-- BOTH:
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Charpoly.Basic

import MIL.Common

/- TEXT:

.. _matrices_bases_dimension:

矩阵、基和维度
-----------------------------

.. _matrices:

矩阵
^^^^^^^^

.. index:: matrices

在介绍抽象向量空间的基之前，我们先回到更基础的线性代数设置——定义在某域 :math:`K` 上的 :math:`K^n` 。这里的主要对象是向量和矩阵。对于具体向量，可以使用 `![…]` 记法，分量之间用逗号分隔。对于具体矩阵，可以使用 `!![…]` 记法，行之间用分号分隔，行内分量用冒号分隔。当矩阵元素类型是可计算类型（例如 `ℕ` 或 `ℚ`）时，可以使用 `eval` 命令来进行基本运算操作的试验。

EXAMPLES: -/
-- QUOTE:

section matrices

-- Adding vectors
#eval !![1, 2] + !![3, 4]  -- !![4, 6]

-- Adding matrices
#eval !![1, 2; 3, 4] + !![3, 4; 5, 6]  -- !![4, 6; 8, 10]

-- Multiplying matrices
#eval !![1, 2; 3, 4] * !![3, 4; 5, 6]  -- !![4, 6; 8, 10]

-- QUOTE.
/- TEXT:
需要理解的是，`#eval` 的使用主要用于探索和试验，并不旨在替代如 Sage 这类计算机代数系统。这里矩阵的数据表示方式 *并不* 在计算上高效，它采用函数而非数组，优化目标是证明而非计算。而且，`#eval` 所用的虚拟机也未针对这种用途进行优化。

请注意，矩阵表示中列出了多行，而向量表示既不是行向量也不是列向量。矩阵与向量的乘法，若从左乘，则将向量视为行向量；若从右乘，则将向量视为列向量。

对应的操作为：

* `Matrix.vecMul`，符号为 `ᵥ*`
* `Matrix.mulVec`，符号为 `*ᵥ`

这些符号限定在 `Matrix` 命名空间，因此我们需要打开该命名空间才能使用。
EXAMPLES: -/
-- QUOTE:
open Matrix

-- 矩阵左作用于向量
#eval !![1, 2; 3, 4] *ᵥ ![1, 1] -- ![3, 7]

-- 矩阵左作用于向量，结果为一维矩阵
#eval !![1, 2] *ᵥ ![1, 1]  -- ![3]

-- 矩阵右作用于向量
#eval  ![1, 1, 1] ᵥ* !![1, 2; 3, 4; 5, 6] -- ![9, 12]
-- QUOTE.
/- TEXT:
为了生成由某向量指定的相同行或列的矩阵，我们使用 `Matrix.row` 和 `Matrix.column`，它们的参数分别是用于索引行或列的类型以及该向量。
例如，可以得到单行矩阵或单列矩阵（更准确地说，是行或列由 `Fin 1` 索引的矩阵）。
EXAMPLES: -/
-- QUOTE:
#eval row (Fin 1) ![1, 2] -- !![1, 2]

#eval col (Fin 1) ![1, 2] -- !![1; 2]
-- QUOTE.
/- TEXT:
其它熟悉的操作包括向量点积、矩阵转置，以及对于方阵的行列式和迹。
EXAMPLES: -/
-- QUOTE:

-- 向量点积
#eval ![1, 2] ⬝ᵥ ![3, 4] -- `11`

-- 矩阵转置
#eval !![1, 2; 3, 4]ᵀ -- `!![1, 3; 2, 4]`

-- 行列式
#eval !![(1 : ℤ), 2; 3, 4].det -- `-2`

-- 迹
#eval !![(1 : ℤ), 2; 3, 4].trace -- `5`


-- QUOTE.
/- TEXT:
当矩阵元素类型不可计算时，比如实数，`#eval` 就无能为力了。而且，这类计算也不能直接用于证明中，否则需要大幅扩展受信任代码库（即在检验证明时必须信任的 Lean 核心部分）。

因此，在证明中推荐使用 `simp` 和 `norm_num` 策略，或者它们对应的命令形式来进行快速探索和简化。
EXAMPLES: -/
-- QUOTE:

#simp !![(1 : ℝ), 2; 3, 4].det -- `4 - 2*3`

#norm_num !![(1 : ℝ), 2; 3, 4].det -- `-2`

#norm_num !![(1 : ℝ), 2; 3, 4].trace -- `5`

variable (a b c d : ℝ) in
#simp !![a, b; c, d].det -- `a * d – b * c`

-- QUOTE.
/- TEXT:
下一个关于方阵的重要操作是求逆。类似于数的除法总是定义的，且对除以零的情况返回人为设定的零值，矩阵求逆操作也定义在所有矩阵上，对于不可逆矩阵返回零矩阵。

更具体地，存在一个通用函数 `Ring.inverse`，它在任意环中实现此功能；对于任意矩阵 `A`，其逆矩阵定义为 ``Ring.inverse A.det • A.adjugate`` 根据Cramer’s rule，当矩阵行列式不为零时，上述定义确实是矩阵 `A` 的逆矩阵。
EXAMPLES: -/
-- QUOTE:

#norm_num [Matrix.inv_def] !![(1 : ℝ), 2; 3, 4]⁻¹ -- !![-2, 1; 3 / 2, -(1 / 2)]

-- QUOTE.
/- TEXT:
当然这种定义确实只对可逆矩阵有用。存在一个通用类型类 ``Invertible`` 来帮助记录这一点。例如，下面例子中的 ``simp`` 调用将使用 ``inv_mul_of_invertible`` 引理，该引理具有 ``Invertible`` 类型类假设，因此只有在类型类合成系统能够找到它时才会触发。在这里，我们使用 ``have`` 语句使这一事实可用。
EXAMPLES: -/
-- QUOTE:

example : !![(1 : ℝ), 2; 3, 4]⁻¹ * !![(1 : ℝ), 2; 3, 4] = 1 := by
  have : Invertible !![(1 : ℝ), 2; 3, 4] := by
    apply Matrix.invertibleOfIsUnitDet
    norm_num
  simp

-- QUOTE.
/- TEXT:
在这个完全具体的例子中，我们也可以使用 ``norm_num`` 工具，和 ``apply?`` 来找到最后一行：
EXAMPLES: -/
-- QUOTE:
example : !![(1 : ℝ), 2; 3, 4]⁻¹ * !![(1 : ℝ), 2; 3, 4] = 1 := by
  norm_num [Matrix.inv_def]
  exact one_fin_two.symm

-- QUOTE.
/- TEXT:
之前所有具体矩阵的行和列均由某个 `Fin n` 索引（行列的 `n` 不一定相同）。但有时使用任意有限类型作为矩阵的行列索引更为方便。例如，有限图的邻接矩阵，其行和列自然由图的顶点索引。

实际上，如果仅定义矩阵而不涉及运算，索引类型的有限性甚至不是必须的，矩阵元素的类型也无需具备任何代数结构。因此，Mathlib 直接将 `Matrix m n α` 定义为 `m → n → α`，其中 `m`、`n`、`α` 是任意类型。我们之前使用的矩阵类型多如 `Matrix (Fin 2) (Fin 2) ℝ`。当然，代数运算对 `m`、`n` 和 `α` 有更严格的假设。

我们不直接使用 `m → n → α` 的主要原因，是让类型类系统能正确理解我们的意图。举例来说，对于环 `R`，类型 `n → R` 自带逐点乘法（point-wise multiplication），而 `m → n → R` 也有类似操作，但这并不是我们想在矩阵上使用的乘法。

下面第一个示例中，我们强制 Lean 展开 `Matrix` 定义，接受陈述的意义，并通过逐个元素检查完成证明。

而后面两个示例展示了 Lean 对 `Fin 2 → Fin 2 → ℤ` 使用逐点乘法，而对 `Matrix (Fin 2) (Fin 2) ℤ` 使用矩阵乘法。
EXAMPLES: -/
-- QUOTE:
section

example : (fun _ ↦ 1 : Fin 2 → Fin 2 → ℤ) = !![1, 1; 1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

example : (fun _ ↦ 1 : Fin 2 → Fin 2 → ℤ) * (fun _ ↦ 1 : Fin 2 → Fin 2 → ℤ) = !![1, 1; 1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

example : !![1, 1; 1, 1] * !![1, 1; 1, 1] = !![2, 2; 2, 2] := by
  norm_num
-- QUOTE.
/- TEXT:
为了定义矩阵作为函数而不失去 ``Matrix`` 在类型类合成中的好处，我们可以使用函数和矩阵之间的等价关系 ``Matrix.of``。这个等价关系是通过 ``Equiv.refl`` 隐式定义的。

例如，我们可以定义与向量 ``v`` 对应的范德蒙德矩阵。
EXAMPLES: -/
-- QUOTE:

example {n : ℕ} (v : Fin n → ℝ) :
    Matrix.vandermonde v = Matrix.of (fun i j : Fin n ↦ v i ^ (j : ℕ)) :=
  rfl
end
end matrices
-- QUOTE.
/- TEXT:
基
^^^^^
我们现在讨论向量空间的基。非正式地说，这一概念有多种定义方式：

* 可以通过万有性质来定义；
* 可以说基是一族线性无关且张成全空间的向量；
* 或结合这两个性质，直接说基是一族向量，使得每个向量都能唯一地表示为基向量的线性组合；
* 另一种说法是，基提供了与基域 ``K`` 的某个幂（作为 ``K`` 上的向量空间）的线性同构。

实际上，Mathlib 在底层采用的是最后一种同构的定义，并从中推导出其他性质。
对于无限基的情况，需稍加注意“基域的幂”这一说法。因为在代数环境中，只考虑有限线性组合有意义，
所以我们参考的向量空间不是基域的直积，而是直和。
我们可以用 `⨁ i : ι, K` 表示某个类型 `ι` 索引的基向量集合对应的直和，
但更常用的是更专门的表示法 `ι →₀ K`，表示“具有有限支集的函数”，即在 `ι` 上除有限点外值为零的函数（这个有限集合不是固定的，依赖于函数本身）。

对于基 `B` 中的函数，给定向量 `v` 和索引 `i : ι`，函数的值即为 `v` 在第 `i` 个基向量上的坐标分量。

以类型 `ι` 索引的向量空间 `V` 的基类型为 `Basis ι K V`，对应的同构称为 `Basis.repr`。
EXAMPLES: -/
-- QUOTE:
variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

section

variable {ι : Type*} (B : Basis ι K V) (v : V) (i : ι)

-- 索引为 ``i`` 的基向量
#check (B i : V)

-- 与模空间 ``B`` 给出的线性同构
#check (B.repr : V ≃ₗ[K] ι →₀ K)

-- ``v`` 的分量函数
#check (B.repr v : ι →₀ K)

-- ``v`` 在索引为 ``i`` 的基向量上的分量
#check (B.repr v i : K)

-- QUOTE.
/- TEXT:
与其从同构出发，也可以从一族线性无关且张成的向量族 `b` 开始构造基，这就是 `Basis.mk`。“张成”的假设表达为 ``⊤ ≤ Submodule.span K (Set.range b)``，这里的 `⊤` 是 `V` 的最大子模，即 `V` 自身作为自身的子模。这个表达看起来有些拗口，但下面我们将看到它与更易理解的表达式 ``∀ v, v ∈ Submodule.span K (Set.range b)`` 几乎是定义等价的（下面代码中的下划线表示无用信息 `v ∈ ⊤`）。
EXAMPLES: -/
-- QUOTE:
noncomputable example (b : ι → V) (b_indep : LinearIndependent K b)
    (b_spans : ∀ v, v ∈ Submodule.span K (Set.range b)) : Basis ι K V :=
  Basis.mk b_indep (fun v _ ↦ b_spans v)

-- 该基的底层向量族确实是 ``b``。
example (b : ι → V) (b_indep : LinearIndependent K b)
    (b_spans : ∀ v, v ∈ Submodule.span K (Set.range b)) (i : ι) :
    Basis.mk b_indep (fun v _ ↦ b_spans v) i = b i :=
  Basis.mk_apply b_indep (fun v _ ↦ b_spans v) i

-- QUOTE.
/- TEXT:
特别地，模型向量空间 `ι →₀ K` 具有所谓的标准基（canonical basis），其 `repr` 函数在任意向量上的值即为恒等同构。该基称为 `Finsupp.basisSingleOne`，其中 `Finsupp` 表示有限支集函数，`basisSingleOne` 指的是基向量是除单个输入点外，其余点值皆为零的函数。更具体地，索引为 `i : ι` 的基向量是 ``Finsupp.single i 1``，这是一个有限支集函数，在点 `i` 取值为 `1`，其余点取值为 `0`。

EXAMPLES: -/
-- QUOTE:
variable [DecidableEq ι]

example : Finsupp.basisSingleOne.repr = LinearEquiv.refl K (ι →₀ K) :=
  rfl

example (i : ι) : Finsupp.basisSingleOne i = Finsupp.single i 1 :=
  rfl

-- QUOTE.
/- TEXT:
当索引类型是有限集合时，有限支集函数的概念就不再需要。这时，我们可以使用更简单的 `Pi.basisFun`，它直接构造了整个 `ι → K` 的一组基。
EXAMPLES: -/
-- QUOTE:

example [Finite ι] (x : ι → K) (i : ι) : (Pi.basisFun K ι).repr x i = x i := by
  simp

-- QUOTE.
/- TEXT:
回到抽象向量空间基的通用情况，我们可以将任何向量表示为基向量的线性组合。让我们首先看看有限基的简单情况。
EXAMPLES: -/
-- QUOTE:

example [Fintype ι] : ∑ i : ι, B.repr v i • (B i) = v :=
  B.sum_repr v

-- QUOTE.

/- TEXT:
当索引类型 `ι` 不是有限集时，上述直接对 `ι` 求和的说法在理论上没有意义，因为无法对无限集合进行直接求和。不过，被求和的函数的支集是有限的（即 `B.repr v` 的支集），这就允许对有限支集进行求和。为了处理这种情况，Mathlib 使用了一个特殊的函数，虽然需要一些时间适应，它是 `Finsupp.linearCombination`（建立在更通用的 `Finsupp.sum` 之上）。

给定一个从类型 `ι` 到基域 `K` 的有限支集函数 `c`，以及任意从 `ι` 到向量空间 `V` 的函数 `f`，`Finsupp.linearCombination K f c` 定义为对 `c` 的支集上所有元素的 `c • f` 进行标量乘法后求和。特别地，我们也可以将求和范围替换为任何包含 `c` 支集的有限集合。

When ``ι`` is not finite, the above statement makes no sense a priori: we cannot take a sum over ``ι``.
However the support of the function being summed is finite (it is the support of ``B.repr v``).
But we need to apply a construction that takes this into account.
Here Mathlib uses a special purpose function that requires some time to get used to:
``Finsupp.linearCombination`` (which is built on top of the more general ``Finsupp.sum``).
Given a finitely supported function ``c`` from a type ``ι`` to the base field ``K`` and any
function ``f`` from ``ι`` to ``V``, ``Finsupp.linearCombination K f c`` is the
sum over the support of ``c`` of the scalar multiplication ``c • f``. In
particular, we can replace it by a sum over any finite set containing the
support of ``c``.

EXAMPLES: -/
-- QUOTE:

example (c : ι →₀ K) (f : ι → V) (s : Finset ι) (h : c.support ⊆ s) :
    Finsupp.linearCombination K f c = ∑ i ∈ s, c i • f i :=
  Finsupp.linearCombination_apply_of_mem_supported K h
-- QUOTE.
/- TEXT:
也可以假设 `f` 是有限支集函数，这样依然能得到良定义的求和结果。但 `Finsupp.linearCombination` 所作的选择更贴合我们关于基的讨论，因为它支持陈述 `Basis.sum_repr` 的推广版本。
EXAMPLES: -/
-- QUOTE:

example : Finsupp.linearCombination K B (B.repr v) = v :=
  B.linearCombination_repr v
-- QUOTE.
/- TEXT:
你可能会好奇，为什么这里的 `K` 是显式参数，尽管它可以从 `c` 的类型中推断出来。关键在于，部分应用的 `Finsupp.linearCombination K f` 本身就是一个有趣的对象。
它不仅仅是一个从 `ι →₀ K` 到 `V` 的普通函数，更是一个 `K`-线性映射。
EXAMPLES: -/
-- QUOTE:
variable (f : ι → V) in
#check (Finsupp.linearCombination K f : (ι →₀ K) →ₗ[K] V)
-- QUOTE.
/- TEXT:
上述细节也解释了为什么不能用点记法写成 `c.linearCombination K f` 来代替 `Finsupp.linearCombination K f c`。
事实上，`Finsupp.linearCombination` 本身并不直接接收 `c` 作为参数，而是先部分应用 `K` 和 `f`，得到一个被强制转换为函数类型的对象，随后该函数才接收 `c` 作为参数。

回到数学讨论，理解基下向量的具体表示在形式化数学中往往没有你想象的那么有用非常重要。实际上，直接利用基的更抽象性质通常更加高效。
特别是，基的通用性质将其与代数中的其他自由对象连接起来，使得我们可以通过指定基向量的像来构造线性映射。这就是 `Basis.constr`。对于任意 `K`-向量空间 `W`，我们的基 `B` 提供了一个线性同构 `Basis.constr B K : (ι → W) ≃ₗ[K] (V →ₗ[K] W)`。该同构的特点是，对于任意函数 `u : ι → W`，它对应的线性映射将基向量 `B i` 映射为 `u i`，其中 `i : ι`。
EXAMPLES: -/
-- QUOTE:
section

variable {W : Type*} [AddCommGroup W] [Module K W]
         (φ : V →ₗ[K] W) (u : ι → W)

#check (B.constr K : (ι → W) ≃ₗ[K] (V →ₗ[K] W))

#check (B.constr K u : V →ₗ[K] W)

example (i : ι) : B.constr K u (B i) = u i :=
  B.constr_basis K u i

-- QUOTE.
/- TEXT:
这个性质实际上是特征性的，因为线性映射是由它们在基上的值决定的：
EXAMPLES: -/
-- QUOTE:
example (φ ψ : V →ₗ[K] W) (h : ∀ i, φ (B i) = ψ (B i)) : φ = ψ :=
  B.ext h


-- QUOTE.
/- TEXT:
如果我们在目标空间上也有一个基 ``B'``，那么我们可以将线性映射与矩阵进行识别。
这种识别是一个 ``K``-线性同构。
EXAMPLES: -/
-- QUOTE:


variable {ι' : Type*} (B' : Basis ι' K W) [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']

open LinearMap

#check (toMatrix B B' : (V →ₗ[K] W) ≃ₗ[K] Matrix ι' ι K)

open Matrix -- 获取对矩阵和向量之间乘法的 ``*ᵥ`` 记法的访问。

example (φ : V →ₗ[K] W) (v : V) : (toMatrix B B' φ) *ᵥ (B.repr v) = B'.repr (φ v) :=
  toMatrix_mulVec_repr B B' φ v


variable {ι'' : Type*} (B'' : Basis ι'' K W) [Fintype ι''] [DecidableEq ι'']

example (φ : V →ₗ[K] W) : (toMatrix B B'' φ) = (toMatrix B' B'' .id) * (toMatrix B B' φ) := by
  simp

end

-- QUOTE.
/- TEXT:
作为本主题的练习，我们将证明一部分定理，保证自同态的行列式是良定义的。具体来说，我们要证明：当两个基由相同类型索引时，它们对应任意自同态的矩阵具有相同的行列式。
然后，结合所有基的索引类型彼此线性同构，便可得到完整结论。

当然，Mathlib 已经包含了这一结论，且 `simp` 策略可以立即解决此目标，因此你不应过早使用它，而应先尝试使用相关引理进行证明。
EXAMPLES: -/
-- QUOTE:

open Module LinearMap Matrix

-- 一些来自于 `LinearMap.toMatrix` 是一个代数同态的事实的引理。
#check toMatrix_comp
#check id_comp
#check comp_id
#check toMatrix_id

-- 一些来自于 ``Matrix.det`` 是一个乘法单元环同态的事实的引理。
#check Matrix.det_mul
#check Matrix.det_one

example [Fintype ι] (B' : Basis ι K V) (φ : End K V) :
    (toMatrix B B φ).det = (toMatrix B' B' φ).det := by
  set M := toMatrix B B φ
  set M' := toMatrix B' B' φ
  set P := (toMatrix B B') LinearMap.id
  set P' := (toMatrix B' B) LinearMap.id
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  have F : M = P' * M' * P := by
    rw [← toMatrix_comp, ← toMatrix_comp, id_comp, comp_id]
  have F' : P' * P = 1 := by
    rw [← toMatrix_comp, id_comp, toMatrix_id]
  rw [F, Matrix.det_mul, Matrix.det_mul,
      show P'.det * M'.det * P.det = P'.det * P.det * M'.det by ring, ← Matrix.det_mul, F',
      Matrix.det_one, one_mul]
-- BOTH:
end

-- QUOTE.
/- TEXT:

维度
^^^^^^^

回到单个向量空间的情况，基也用于定义维度的概念。在这里，我们再次遇到有限维向量空间的基本情况。
对于这样的空间，我们期望维度是一个自然数。这就是 ``Module.finrank``。它将基域作为显式参数，因为给定的阿贝尔群可以是不同域上的向量空间。

EXAMPLES: -/
-- QUOTE:
section
#check (Module.finrank K V : ℕ)

-- `Fin n → K` 是维度为 `n` 的典型空间。
example (n : ℕ) : Module.finrank K (Fin n → K) = n :=
  Module.finrank_fin_fun K

-- 作为自身的向量空间，`ℂ` 的维度为1。
example : Module.finrank ℂ ℂ = 1 :=
  Module.finrank_self ℂ

-- 但作为实向量空间，它的维度为2。
example : Module.finrank ℝ ℂ = 2 :=
  Complex.finrank_real_complex

-- QUOTE.
/- TEXT:
注意到 ``Module.finrank`` 是为任何向量空间定义的。它对于无限维向量空间返回零，就像除以零返回零一样。

当然，许多引理都需要有限维度的假设。这就是 ``FiniteDimensional`` 类型类的作用。例如，考虑下一个例子在没有这个假设的情况下是如何失败的。
EXAMPLES: -/
-- QUOTE:

example [FiniteDimensional K V] : 0 < Module.finrank K V ↔ Nontrivial V  :=
  Module.finrank_pos_iff

-- QUOTE.
/- TEXT:
在上述陈述中，`Nontrivial V` 表示 `V` 至少包含两个不同元素。注意，`Module.finrank_pos_iff` 没有显式参数。
从左向右使用时没问题，但从右向左使用时会遇到困难，因为 Lean 无法从 `Nontrivial V` 这一命题中推断出域 `K`。
此时，使用命名参数语法会很有帮助，前提是确认该引理是在一个名为 `R` 的环上陈述的。因此我们可以写成：
EXAMPLES: -/
-- QUOTE:

example [FiniteDimensional K V] (h : 0 < Module.finrank K V) : Nontrivial V := by
  apply (Module.finrank_pos_iff (R := K)).1
  exact h

-- QUOTE.
/- TEXT:
上述写法看起来有些奇怪，因为我们已经有了假设 `h`，因此完全可以直接写成 `Module.finrank_pos_iff.1 h` 来使用该引理。不过，了解命名参数的用法对于更复杂的情况仍然很有帮助。

根据定义，`FiniteDimensional K V` 可以通过任意一组基来判定。
EXAMPLES: -/
-- QUOTE:
variable {ι : Type*} (B : Basis ι K V)

example [Finite ι] : FiniteDimensional K V := FiniteDimensional.of_fintype_basis B

example [FiniteDimensional K V] : Finite ι :=
  (FiniteDimensional.fintypeBasisIndex B).finite
end
-- QUOTE.
/- TEXT:
使用与线性子空间对应的子类型具有向量空间结构，我们可以讨论子空间的维度。
EXAMPLES: -/
-- QUOTE:

section
variable (E F : Submodule K V) [FiniteDimensional K V]

open Module

example : finrank K (E ⊔ F : Submodule K V) + finrank K (E ⊓ F : Submodule K V) =
    finrank K E + finrank K F :=
  Submodule.finrank_sup_add_finrank_inf_eq E F

example : finrank K E ≤ finrank K V := Submodule.finrank_le E
-- QUOTE.
/- TEXT:
在第一条语句中，类型注释的目的是确保对 ``Type*`` 的强制转换不会过早触发。

我们现在准备进行一个关于 ``finrank`` 和子空间的练习。
EXAMPLES: -/
-- QUOTE:
example (h : finrank K V < finrank K E + finrank K F) :
    Nontrivial (E ⊓ F : Submodule K V) := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  rw [← finrank_pos_iff (R := K)]
  have := Submodule.finrank_sup_add_finrank_inf_eq E F
  have := Submodule.finrank_le E
  have := Submodule.finrank_le F
  have := Submodule.finrank_le (E ⊔ F)
  linarith
-- BOTH:
end
-- QUOTE.

/- TEXT:
我们现在转向一般的维数理论情形。此时，`finrank` 就不再适用，但我们依然知道，对于同一向量空间的任意两组基，其索引类型之间存在一个双射。因此，我们仍然可以期望将秩定义为基数（cardinal），即“类型集合在存在双射的等价关系下的商集”中的元素。

在讨论基数时，难以像本书其他部分那样忽略类似罗素悖论的基础性问题。因为不存在“所有类型的类型”，否则会导致逻辑矛盾。
这一问题通过宇宙层级（universe hierarchy）来解决，而我们通常会尝试忽略这些细节。

每个类型都有一个宇宙层级，该层级行为类似自然数。特别地，有一个零层级，对应的宇宙 `Type 0` 简写为 `Type`，这个宇宙足以容纳几乎所有经典数学对象，比如 `ℕ` 和 `ℝ` 都属于类型 `Type`。每个层级 `u` 有一个后继层级 `u + 1`，且 `Type u` 的类型是 `Type (u + 1)`。

但宇宙层级不是自然数，它们本质不同且没有对应的类型。例如，无法在 Lean 中声明 `u ≠ u + 1`，因为不存在一个类型可以表达这个命题。即使声明 `Type u ≠ Type (u+1)` 也没有意义，因为两者属于不同的类型。

当我们写 `Type*` 时，Lean 会自动插入一个名为 `u_n` 的宇宙变量，其中 `n` 是一个数字，允许定义和陈述在所有宇宙层级中成立。

给定宇宙层级 `u`，我们可以在 `Type u` 上定义等价关系：当且仅当两个类型 `α` 和 `β` 存在双射时它们等价。
商类型 `Cardinal.{u}` 属于 `Type (u + 1)`，花括号表示这是一个宇宙变量。类型 `α : Type u` 在商中的像为 `Cardinal.mk α : Cardinal.{u}`。

但我们不能直接比较不同宇宙层级中的基数。因此技术上讲，不能将向量空间 `V` 的秩定义为索引 `V` 基的所有类型的基数。
相反，秩定义为 `Module.rank K V`，即 `V` 中所有线性无关集基数的上确界。如果 `V` 属于宇宙层级 `u`，则其秩属于 `Cardinal.{u}` 类型。
EXAMPLES: -/
-- QUOTE:
#check V -- Type u_2
#check Module.rank K V -- Cardinal.{u_2}

-- QUOTE.
/- TEXT:
这个定义仍然可以与基联系起来。实际上，宇宙层级上存在一个交换的 `max` 运算，对于任意两个宇宙层级 `u` 和 `v`，存在一个操作
`Cardinal.lift.{u, v} : Cardinal.{v} → Cardinal.{max v u}`，该操作允许将基数提升到共同的宇宙层级中，从而陈述维数定理。
EXAMPLES: -/
-- QUOTE:

universe u v -- `u` 和 `v` 将表示宇宙层级

variable {ι : Type u} (B : Basis ι K V)
         {ι' : Type v} (B' : Basis ι' K V)

example : Cardinal.lift.{v, u} (.mk ι) = Cardinal.lift.{u, v} (.mk ι') :=
  mk_eq_mk_of_basis B B'
-- QUOTE.
/- TEXT:
我们可以将有限维情况与此讨论联系起来，使用从自然数到有限基数的强制转换（更准确地说，是生活在 ``Cardinal.{v}`` 中的有限基数，其中 ``v`` 是 ``V`` 的宇宙层级）。
EXAMPLES: -/
-- QUOTE:

example [FiniteDimensional K V] :
    (Module.finrank K V : Cardinal) = Module.rank K V :=
  Module.finrank_eq_rank K V
-- QUOTE.
