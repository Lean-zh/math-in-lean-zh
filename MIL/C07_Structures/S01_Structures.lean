import MIL.Common
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Real.Basic

namespace C06S01
noncomputable section

/- TEXT:
.. _section_structures:

定义结构体
-------------------

广义上来说， **结构体** 是对特定形式数据集合的约定，包括包含数据的形式以及这些数据要满足的一些约束条件。
而结构体的 **实例** 则是某一组满足约束的具体数据。例如，我们可以规定一个点是由三个实数组成的三元组：
BOTH: -/
-- QUOTE:
@[ext]
structure Point where
  x : ℝ
  y : ℝ
  z : ℝ
-- QUOTE.

/- TEXT:
上面用到的 ``@[ext]`` 注解让 Lean 自动生成一个定理，内容是当该结构体的两个实例各组成部分对应相同时，这两个实例相等。
该属性也称为 **外延性（extensionality）** 。
EXAMPLES: -/
-- QUOTE:
#check Point.ext

example (a b : Point) (hx : a.x = b.x) (hy : a.y = b.y) (hz : a.z = b.z) : a = b := by
  ext
  repeat' assumption
-- QUOTE.

/- TEXT:
接着我们定义一个 ``Point`` 结构体的实例。
Lean 提供多种实例化方式来达成目的。
EXAMPLES: -/
-- QUOTE:
def myPoint1 : Point where
  x := 2
  y := -1
  z := 4

def myPoint2 : Point :=
  ⟨2, -1, 4⟩

def myPoint3 :=
  Point.mk 2 (-1) 4
-- QUOTE.

/- TEXT:
..
  Because Lean knows that the expected type of
  ``myPoint1`` is a ``Point``, you can start the definition by
  writing an underscore, ``_``. Clicking on the light bulb
  that appears nearby in VS Code will then
  give you the option of inserting a template definition
  with the field names listed for you.

第一个例子中，我们明确地指明了结构体的各个字段。
在定义 ``myPoint3`` 时用到的函数 ``Point.mk`` 叫做 ``Point`` 结构体的 **构造函数（constructor）** ，用于构造结构体成员。
你也可以为构造函数指定一个不同的名字，比如 ``build``。
EXAMPLES: -/
-- QUOTE:
structure Point' where build ::
  x : ℝ
  y : ℝ
  z : ℝ

#check Point'.build 2 (-1) 4
-- QUOTE.

/- TEXT:
接下来的两个例子展示了如何定义结构体的函数。
第二个例子中明确指出了构造函数 ``Point.mk`` 中的字段名，而第一个例子则使用更为简洁的匿名构造函数。
Lean 能根据 ``add`` 的目标类型推断出所需的构造函数。
通常，我们会将与结构体（例如这里的 ``Point``）相关的定义和定理放在一个同名的命名空间（namespace）中。
在下面的示例中，由于我们启用了 ``Point`` 命名空间，所以 ``add`` 的完整名称实际是 ``Point.add``。
当命名空间没被启用时，就得使用完整名称。
不过这时也可以使用匿名投影记号（anonymous projection notation），它允许我们用 ``a.add b`` 代替 ``Point.add a b``。
因为 a 的类型是 ``Point``，Lean 能在没有开启对应命名空间的时候将 ``a.add b`` 推断为 ``Point.add a b``。
BOTH: -/
-- QUOTE:
namespace Point

def add (a b : Point) : Point :=
  ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

-- EXAMPLES:
def add' (a b : Point) : Point where
  x := a.x + b.x
  y := a.y + b.y
  z := a.z + b.z

#check add myPoint1 myPoint2
#check myPoint1.add myPoint2

end Point

#check Point.add myPoint1 myPoint2
#check myPoint1.add myPoint2
-- QUOTE.

/- TEXT:
接下来我们继续在相关命名空间中添加定义，但在引用的代码片段中会省略开关命名空间相关的指令。
在证明加法函数性质时，可使用 ``rw`` 来展开定义，并用 ``ext`` 将结构体两个实例之间的等号转化为它们各个组成部分之间的等号。
下面的代码使用 ``protected`` 关键字，使得在命名空间打开的情况下定理的名字依然是 ``Point.add_comm``。
当我们希望避免与泛型定理如 ``add_comm`` 产生歧义时，这样做是有帮助的。
EXAMPLES: -/
namespace Point

-- QUOTE:
protected theorem add_comm (a b : Point) : add a b = add b a := by
  rw [add, add]
  ext <;> dsimp
  repeat' apply add_comm

example (a b : Point) : add a b = add b a := by simp [add, add_comm]
-- QUOTE.

/- TEXT:
因为 Lean 能在内部自动展开定义并简化投影，所以有时我们需要的等式在定义上就自动成立。
EXAMPLES: -/
-- QUOTE:
theorem add_x (a b : Point) : (a.add b).x = a.x + b.x :=
  rfl
-- QUOTE.

/- TEXT:
与在
:numref:`section_induction_and_recursion`
中定义递归函数类似，我们定义函数时也可以使用模式匹配。
下面定义的 ``addAlt`` 和 ``addAlt'`` 本质上是相同的，形式上的的区别在于我们在后者的定义中使用了匿名构造函数。
虽然以此方式定义函数有时会显得更加简洁，并且结构化 η-规约（structural eta-reduction）也确保了这种简写在定义上的等价性，但这么做可能会为后续的证明带来不便。
EXAMPLES: -/
-- QUOTE:
def addAlt : Point → Point → Point
  | Point.mk x₁ y₁ z₁, Point.mk x₂ y₂ z₂ => ⟨x₁ + x₂, y₁ + y₂, z₁ + z₂⟩

def addAlt' : Point → Point → Point
  | ⟨x₁, y₁, z₁⟩, ⟨x₂, y₂, z₂⟩ => ⟨x₁ + x₂, y₁ + y₂, z₁ + z₂⟩

theorem addAlt_x (a b : Point) : (a.addAlt b).x = a.x + b.x := by
  rfl

theorem addAlt_comm (a b : Point) : addAlt a b = addAlt b a := by
  rw [addAlt, addAlt]
  -- the same proof still works, but the goal view here is harder to read
  ext <;> dsimp
  repeat' apply add_comm
-- QUOTE.

/- TEXT:
数学构造通常涉及将捆绑的信息拆分开来，并以不同的方式重新组合。
这也是 Lean 和 Mathlib 提供如此多方法来高效处理这些操作的原因。
作为练习，请尝试证明 ``Point.add`` 是满足结合律的。
然后请定义点的标量乘法并证明其满足对加法的分配律。
BOTH: -/
-- QUOTE:
protected theorem add_assoc (a b c : Point) : (a.add b).add c = a.add (b.add c) := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  simp [add, add_assoc]
-- BOTH:

def smul (r : ℝ) (a : Point) : Point :=
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  ⟨r * a.x, r * a.y, r * a.z⟩
-- BOTH:

theorem smul_distrib (r : ℝ) (a b : Point) :
    (smul r a).add (smul r b) = smul r (a.add b) := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  simp [add, smul, mul_add]
-- BOTH:
-- QUOTE.

end Point

/- TEXT:
使用结构体是走向代数抽象的第一步。
我们目前还没有方法将 ``Point.add`` 与泛型的 ``+`` 符号联系起来，
抑或是将 ``Point.add_comm``、``Point.add_assoc`` 与泛型的 ``add_comm``、``add_assoc`` 定理联系起来。
这些任务属于结构体在 **代数层面** 的应用，我们将在下一节介绍如何具体实现。
对现在来说，我们只需要把结构体视作一种捆绑对象和信息的方法。

在结构体中我们不仅可以指定数据类型，还可以指定数据需要满足的约束。
在 Lean 中，后者被表示为类型 ``Prop`` 的字段。
例如， **标准2-单纯形（standard 2-simplex）** 定义为满足 :math:`x ≥ 0`，:math:`y ≥ 0`，:math:`z ≥ 0`，:math:`x + y + z = 1` 的点 :math:`(x, y, z)` 的集合。
如果你不熟悉这个概念，可以画个图，其实这个集合就是三维空间中以 :math:`(1, 0, 0)`，:math:`(0, 1, 0)`，和 :math:`(0, 0, 1)` 为顶点的等边三角形以及其内部。
在 Lean 中可以这样形式化表示：
BOTH: -/
-- QUOTE:
structure StandardTwoSimplex where
  x : ℝ
  y : ℝ
  z : ℝ
  x_nonneg : 0 ≤ x
  y_nonneg : 0 ≤ y
  z_nonneg : 0 ≤ z
  sum_eq : x + y + z = 1
-- QUOTE.

/- TEXT:
请注意，最后四个字段用到的 ``x``，``y``，``z`` 指的就是前三个字段。
我们可以定义一个从2-单纯形到其自身的映射，该映射交换 ``x`` 和 ``y``：
BOTH: -/
namespace StandardTwoSimplex

-- EXAMPLES:
-- QUOTE:
def swapXy (a : StandardTwoSimplex) : StandardTwoSimplex
    where
  x := a.y
  y := a.x
  z := a.z
  x_nonneg := a.y_nonneg
  y_nonneg := a.x_nonneg
  z_nonneg := a.z_nonneg
  sum_eq := by rw [add_comm a.y a.x, a.sum_eq]
-- QUOTE.

-- OMIT: (TODO) add a link when we have a good explanation of noncomputable section.
/- TEXT:
有趣的来了，我们可以计算单纯形内两个点的中点。
为此需要先在文件开头加上 ``noncomputable section`` 语句以便使用实数上的除法。
BOTH: -/
-- QUOTE:
noncomputable section

-- EXAMPLES:
def midpoint (a b : StandardTwoSimplex) : StandardTwoSimplex
    where
  x := (a.x + b.x) / 2
  y := (a.y + b.y) / 2
  z := (a.z + b.z) / 2
  x_nonneg := div_nonneg (add_nonneg a.x_nonneg b.x_nonneg) (by norm_num)
  y_nonneg := div_nonneg (add_nonneg a.y_nonneg b.y_nonneg) (by norm_num)
  z_nonneg := div_nonneg (add_nonneg a.z_nonneg b.z_nonneg) (by norm_num)
  sum_eq := by field_simp; linarith [a.sum_eq, b.sum_eq]
-- QUOTE.

/- TEXT:
上面的代码中，对于 ``x_nonneg``，``y_nonneg``，``z_nonneg``，我们用简洁的证明项即可建立。
而对于 ``sum_eq`` ，我们选择使用 ``by`` 在策略模式下进行证明。

给定参数 :math:`\lambda` 满足 :math:`0 \le \lambda \le 1`，
可定义标准2-单纯形中 :math:`a` 和 :math:`b` 两点的加权平均为 :math:`\lambda a + (1 - \lambda) b`。
请尝试参考前面的 ``midpoint`` 形式化定义该加权平均。
BOTH: -/
-- QUOTE:
def weightedAverage (lambda : Real) (lambda_nonneg : 0 ≤ lambda) (lambda_le : lambda ≤ 1)
/- EXAMPLES:
    (a b : StandardTwoSimplex) : StandardTwoSimplex :=
  sorry
SOLUTIONS: -/
  (a b : StandardTwoSimplex) : StandardTwoSimplex
where
  x := lambda * a.x + (1 - lambda) * b.x
  y := lambda * a.y + (1 - lambda) * b.y
  z := lambda * a.z + (1 - lambda) * b.z
  x_nonneg := add_nonneg (mul_nonneg lambda_nonneg a.x_nonneg) (mul_nonneg (by linarith) b.x_nonneg)
  y_nonneg := add_nonneg (mul_nonneg lambda_nonneg a.y_nonneg) (mul_nonneg (by linarith) b.y_nonneg)
  z_nonneg := add_nonneg (mul_nonneg lambda_nonneg a.z_nonneg) (mul_nonneg (by linarith) b.z_nonneg)
  sum_eq := by
    trans (a.x + a.y + a.z) * lambda + (b.x + b.y + b.z) * (1 - lambda)
    · ring
    simp [a.sum_eq, b.sum_eq]
-- QUOTE.
-- BOTH:

end

end StandardTwoSimplex

/- TEXT:
结构体还可以依赖于参数。
例如，可以将标准2-单纯形推广到任意维数 :math:`n` 下的 :math:`n` -单纯形。
目前阶段，你不需要对 ``Fin n`` 了解太多，只需知道它有 :math:`n` 个元素，并且 Lean 知道如何在其上进行就和操作即可。
BOTH: -/
-- QUOTE:
open BigOperators

structure StandardSimplex (n : ℕ) where
  V : Fin n → ℝ
  NonNeg : ∀ i : Fin n, 0 ≤ V i
  sum_eq_one : (∑ i, V i) = 1

namespace StandardSimplex

def midpoint (n : ℕ) (a b : StandardSimplex n) : StandardSimplex n
    where
  V i := (a.V i + b.V i) / 2
  NonNeg := by
    intro i
    apply div_nonneg
    · linarith [a.NonNeg i, b.NonNeg i]
    norm_num
  sum_eq_one := by
    simp [div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_add_distrib,
      a.sum_eq_one, b.sum_eq_one]
    field_simp

end StandardSimplex
-- QUOTE.

/- TEXT:
作为额外练习，请尝试定义一下标准 :math:`n` -单纯形中两点的加权平均。
可以使用 ``Finset.sum_add_distrib`` 和 ``Finset.mul_sum`` 来实现相关的求和操作。

SOLUTIONS: -/
namespace StandardSimplex

def weightedAverage {n : ℕ} (lambda : Real) (lambda_nonneg : 0 ≤ lambda) (lambda_le : lambda ≤ 1)
    (a b : StandardSimplex n) : StandardSimplex n
    where
  V i := lambda * a.V i + (1 - lambda) * b.V i
  NonNeg i :=
    add_nonneg (mul_nonneg lambda_nonneg (a.NonNeg i)) (mul_nonneg (by linarith) (b.NonNeg i))
  sum_eq_one := by
    trans (lambda * ∑ i, a.V i) + (1 - lambda) * ∑ i, b.V i
    · rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    simp [a.sum_eq_one, b.sum_eq_one]

end StandardSimplex

/- TEXT:
前面我们已经了解到结构体可以用来将数据和属性打包在一起。
有趣的是，结构体也可以用来打包脱离具体数据的抽象属性。
例如，下面的结构体 ``IsLinear``，将线性性（linearity）的两个主要组成部分打包在了一起。
EXAMPLES: -/
-- QUOTE:
structure IsLinear (f : ℝ → ℝ) where
  is_additive : ∀ x y, f (x + y) = f x + f y
  preserves_mul : ∀ x c, f (c * x) = c * f x

section
variable (f : ℝ → ℝ) (linf : IsLinear f)

#check linf.is_additive
#check linf.preserves_mul

end
-- QUOTE.

/- TEXT:
值得一提的是，结构体并不是打包数据的唯一方法。
前面提到的 ``Point`` 数据结构也可以用泛型乘积类型来定义，而 ``IsLinear`` 可以使用简单的 ``and`` 来定义。
EXAMPLES: -/
-- QUOTE:
def Point'' :=
  ℝ × ℝ × ℝ

def IsLinear' (f : ℝ → ℝ) :=
  (∀ x y, f (x + y) = f x + f y) ∧ ∀ x c, f (c * x) = c * f x
-- QUOTE.

/- TEXT:
泛型类型构造甚至可以替代包含依赖关系的结构体。
例如， **子类型（subtype）** 构造结合了一段数据以及一条属性。
你可以将下面例子中的 ``PReal`` 看作正实数类型。
每个 ``x : PReal`` 都有两个分量：它的值，以及“它是正的”这一属性。
你可以分别用 ``x.val`` 与 ``x.property`` 来访问这两个分量，其中前者的类型为 ``ℝ``，后者是一个属性 ``0 < x.val``。
EXAMPLES: -/
-- QUOTE:
def PReal :=
  { y : ℝ // 0 < y }

section
variable (x : PReal)

#check x.val
#check x.property
#check x.1
#check x.2

end
-- QUOTE.

/- TEXT:
我们也可以用子类型来定义前面的标准2-单纯形，以及任意维数 :math:`n` 下的标准 :math:`n` -单纯形。
EXAMPLES: -/
-- QUOTE:
def StandardTwoSimplex' :=
  { p : ℝ × ℝ × ℝ // 0 ≤ p.1 ∧ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.1 + p.2.1 + p.2.2 = 1 }

def StandardSimplex' (n : ℕ) :=
  { v : Fin n → ℝ // (∀ i : Fin n, 0 ≤ v i) ∧ (∑ i, v i) = 1 }
-- QUOTE.

/- TEXT:
类似地， **Sigma 类型** 是有序对的推广，其中第二个分量的类型依赖于第一个分量。
EXAMPLES: -/
-- QUOTE:
def StdSimplex := Σ n : ℕ, StandardSimplex n

section
variable (s : StdSimplex)

#check s.fst
#check s.snd

#check s.1
#check s.2

end
-- QUOTE.

/- TEXT:
给定 ``s : StdSimplex``，它的第一个分量 ``s.fst`` 是个自然数，第二个分量是对应维数下标准单纯形中的一个元素 ``StandardSimplex s.fst``。
Sigma 类型与子类型的区别在于 Sigma 类型的第二个分量是数据而非属性。

尽管可以使用乘积类型、子类型、 Sigma 类型等替代结构体，但使用结构体其实有许多好处。
定义结构体可以抽象出底层的表达，且能为成员提供自定义的名称以供访问。
这使得证明更加健壮：
对于那些仅依赖结构体接口的证明，通常只需用新接口替换旧接口，就能让证明代码在结构体定义变更后依然有效。
此外，正如我们即将看到的，Lean 支持将各种结构体编织成一个丰富的、相互关联的层次体系，以管理它们之间的交互关系。
TEXT. -/
/- OMIT: (TODO)
Comments from Patrick:
We could make this paragraph much less abstract by showing how to access the components of a point with the definition def point'' := ℝ × ℝ × ℝ. However if we do that it would probably be honest to also mention the possibility of using fin 3 → ℝ as the definition. This interesting anyhow, because I think very few mathematician realize that defining ℝ^n as an iterated cartesian product is a polite lie that would be a nightmare if taken seriously.

By the way, should be include some comment about similarities and differences with object-oriented programming? All the examples from that page would clearly fit very well with classes in python say. And we'll have to face the name-clash between classes in Lean and classes in C++ or python sooner or later. Life would be so much simpler if classes in Lean could use another name...
OMIT. -/
