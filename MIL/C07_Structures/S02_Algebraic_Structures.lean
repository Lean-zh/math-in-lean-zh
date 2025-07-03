import MIL.Common
import Mathlib.Data.Real.Basic

namespace C06S02

/- TEXT:
.. _section_algebraic_structures:

代数结构
--------------------

为了阐明我们所说的 **代数结构** 这一短语的含义，考虑一些例子会有所帮助。

#. **偏序集** 由集合 :math:`P` 以及定义在 :math:`P` 上的二元关系 :math:`\le` 组成，该关系具有传递性和自反性。

#. **群** 由集合 :math:`G` 以及其上的一个结合二元运算、一个单位元 :math:`1` 和一个将 :math:`G` 中每个元素 :math:`g` 映射为其逆元 :math:`g^{-1}` 的函数 :math:`g \mapsto g^{-1}` 构成。若运算满足交换律，则称该群为阿贝尔群或交换群。

#. **格** 是一种具有交和并运算的部分有序集。

#. **环** 由一个（加法表示的）阿贝尔群 :math:`(R, +, 0, x \mapsto -x)` 以及一个结合的乘法运算 :math:`\cdot` 和一个单位元 :math:`1` 组成，并且乘法对加法满足分配律。如果乘法是可交换的，则称环为 **交换环** 。

#. 一个 **有序环** :math:`(R, +, 0, -, \cdot, 1, \le)` 由一个环以及其元素上的一个偏序关系组成，满足以下条件：对于 :math:`R` 中的任意 :math:`a`、:math:`b` 和 :math:`c`，若 :math:`a \le b`，则 :math:`a + c \le b + c`；对于 :math:`R` 中的任意 :math:`a` 和 :math:`b`，若 :math:`0 \le a` 且 :math:`0 \le b`，则 :math:`0 \le a b`。

#. **度量空间** 由一个集合 :math:`X` 和一个函数 :math:`d : X \times X \to \mathbb{R}` 组成，满足以下条件：
- 对于集合 X 中的任意 x 和 y，有 :math:`d(x, y) \ge 0` 。
- 当且仅当 x = y 时，:math:`d(x， y) = 0` 。
- 对于集合 X 中的任意 x 和 y，有 :math:`d(x， y) = d(y， x)` 。
- 对于集合 X 中的任意 x、y 和 z，有 :math:`d(x, z) \le d(x, y) + d(y， z)` 。

#. **拓扑空间** 由集合 :math:`X` 以及 :math:`X` 的子集所构成的集合 :math:`\mathcal T` 组成，这些子集被称为 :math:`X` 的开子集，且满足以下条件：
- 空集和 :math:`X` 是开集。
- 两个开集的交集是开集。
- 任意多个开集的并集是开集。

在上述每个例子中，结构的元素都属于一个集合，即 **载体集** ，有时它可代表整个结构。例如，当我们说“设 :math:`G` 是一个群”，然后说“设 :math:`g \in G`”，这里 :math:`G` 既代表结构本身，也代表其载体。并非每个代数结构都以这种方式与单个载体集相关联。例如， **二部图** 涉及两个集合之间的关系，**伽罗瓦连接** 也是如此。 **范畴** 也涉及两个感兴趣的集合，通常称为 **对象** 和 **态射** 。
这些示例表明了证明助手为了支持代数推理需要完成的一些工作。
首先，它需要识别结构的具体实例。
数系 :math:`\mathbb{Z}`、:math:`\mathbb{Q}` 和 :math:`\mathbb{R}` 都是有序环，
我们应当能够在这些实例中的任何一个上应用关于有序环的一般定理。
有时，一个具体的集合可能以不止一种方式成为某个结构的实例。
例如，除了构成实分析基础的通常的 :math:`\mathbb{R}` 上的拓扑外，
我们还可以考虑 :math:`\mathbb{R}` 上的 **离散** 拓扑，在这种拓扑中，每个集合都是开集。
其次，证明助手需要支持结构上的通用符号表示。在 Lean 中，符号 ``*`` 用于所有常见数系中的乘法，也用于泛指群和环中的乘法。当我们使用像 ``f x * y`` 这样的表达式时，Lean 必须利用关于 ``f`` 、 ``x`` 和 ``y`` 的类型信息来确定我们所指的乘法运算。
第三，它需要处理这样一个事实，即结构可以通过多种方式从其他结构继承定义、定理和符号。有些结构通过添加更多公理来扩展其他结构。交换环仍然是环，因此在环中有意义的任何定义在交换环中也有意义，任何在环中成立的定理在交换环中也成立。有些结构通过添加更多数据来扩展其他结构。例如，任何环的加法部分都是加法群。环结构添加了乘法和单位元，以及管理它们并将其与加法部分相关联的公理。有时我们可以用另一种结构来定义一种结构。任何度量空间都有一个与之相关的标准拓扑，即“度量空间拓扑”，并且任何线性序都可以关联多种拓扑。
最后，重要的是要记住，数学使我们能够像使用函数和运算来定义数字一样，使用函数和运算来定义结构。群的乘积和幂次仍然是群。对于每个 :math:`n`，模 :math:`n` 的整数构成一个环，对于每个 :math:`k > 0`，该环中系数的 :math:`k \times k` 多项式矩阵再次构成一个环。因此，我们能够像计算其元素一样轻松地计算结构。这意味着代数结构在数学中有着双重身份，既是对象集合的容器，又是独立的对象。证明助手必须适应这种双重角色。
在处理具有代数结构相关联的类型的元素时，证明助手需要识别该结构并找到相关的定义、定理和符号。这一切听起来似乎工作量很大，确实如此。但 Lean 使用一小部分基本机制来完成这些任务。本节的目标是解释这些机制并展示如何使用它们。
第一个要素几乎无需提及，因为它太过显而易见：从形式上讲，代数结构是 :numref:`section_structures` 中所定义的那种结构。代数结构是对满足某些公理假设的数据束的规范，我们在 :numref:`section_structures` 中看到，这正是 ``structure`` 命令所设计要容纳的内容。这简直是天作之合！
给定一种数据类型 ``α`` ，我们可以按如下方式定义 ``α`` 上的群结构。
EXAMPLES: -/
-- QUOTE:
structure Group₁ (α : Type*) where
  mul : α → α → α
  one : α
  inv : α → α
  mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z)
  mul_one : ∀ x : α, mul x one = x
  one_mul : ∀ x : α, mul one x = x
  inv_mul_cancel : ∀ x : α, mul (inv x) x = one
-- QUOTE.

-- OMIT: TODO: explain the extends command later, and also redundant inheritance
/- TEXT:
请注意，在 ``group₁`` 的定义中，类型 ``α`` 是一个 **参数** 。因此，您应当将对象 ``struc : Group₁ α`` 视为是在 ``α`` 上的一个群结构。我们在 :numref:`proving_identities_in_algebraic_structures` 中看到，与 ``inv_mul_cancel`` 相对应的 ``mul_inv_cancel`` 可以从其他群公理推导出来，所以无需将其添加到定义中。

这个群的定义与 Mathlib 中的 ``Group`` 定义类似，我们选择使用 ``Group₁`` 这个名称来区分我们的版本。如果您输入 ``#check Group`` 并点击定义，您会看到 Mathlib 版本的 ``Group`` 被定义为扩展了另一个结构；我们稍后会解释如何做到这一点。如果您输入 ``#print Group`` ，您还会看到 Mathlib 版本的 ``Group`` 具有许多额外的字段。出于稍后会解释的原因，有时在结构中添加冗余信息是有用的，这样就有额外的字段用于从核心数据定义的对象和函数。现在先别担心这个问题。请放心，我们的简化版本 ``Group₁`` 在本质上与 Mathlib 使用的群定义相同。

有时将类型与结构捆绑在一起是有用的，Mathlib 中也包含一个与以下定义等价的 ``GroupCat`` 结构定义：
EXAMPLES: -/
-- QUOTE:
structure Group₁Cat where
  α : Type*
  str : Group₁ α
-- QUOTE.

/- TEXT:
Mathlib 版本位于 ``Mathlib.Algebra.Category.GroupCat.Basic`` 中，如果您在示例文件开头的导入中添加此内容，可以使用 ``#check`` 查看它。

出于下文会更清楚说明的原因，通常更有用的做法是将类型 ``α`` 与结构 ``Group α`` 分开。我们将这两个对象一起称为 **部分捆绑结构** ，因为其表示将大部分但并非全部的组件组合成一个结构。在 Mathlib 中，当某个类型被用作群的载体类型时，通常会使用大写罗马字母如 ``G`` 来表示该类型。

让我们构建一个群，也就是说，一个 ``Group₁`` 类型的元素。对于任意的类型α和β，Mathlib 定义了类型 ``Equiv α β`` ，表示α和β之间的 **等价关系** 。
Mathlib 还为这个类型定义了具有提示性的记号 ``α ≃ β`` 。
一个元素 ``f : α ≃ β`` 是α和β之间的双射，由四个部分表示：
从α到β的函数 ``f.toFun`` ，
从β到α的逆函数 ``f.invFun`` ，
以及两个指定这些函数确实是彼此逆函数的性质。
EXAMPLES: -/
section
-- QUOTE:
variable (α β γ : Type*)
variable (f : α ≃ β) (g : β ≃ γ)

#check Equiv α β
#check (f.toFun : α → β)
#check (f.invFun : β → α)
#check (f.right_inv : ∀ x : β, f (f.invFun x) = x)
#check (f.left_inv : ∀ x : α, f.invFun (f x) = x)
#check (Equiv.refl α : α ≃ α)
#check (f.symm : β ≃ α)
#check (f.trans g : α ≃ γ)
-- QUOTE.

/- TEXT:
请注意最后三个构造的创造性命名。我们将恒等函数 ``Equiv.refl`` 、逆运算 ``Equiv.symm`` 和复合运算 ``Equiv.trans`` 视为明确的证据，表明处于双射对应关系的性质是一个等价关系。

还要注意， ``f.trans g`` 要求将前向函数按相反的顺序组合。Mathlib 已经声明了从 ``Equiv α β`` 到函数类型 ``α → β`` 的一个 **强制转换** ，因此我们可以省略书写 ``.toFun`` ，让 Lean 为我们插入。
EXAMPLES: -/
-- QUOTE:
example (x : α) : (f.trans g).toFun x = g.toFun (f.toFun x) :=
  rfl

example (x : α) : (f.trans g) x = g (f x) :=
  rfl

example : (f.trans g : α → γ) = g ∘ f :=
  rfl
-- QUOTE.

end

/- TEXT:
Mathlib 还定义了 ``α`` 与其自身的等价关系类型 ``perm α`` 。
EXAMPLES: -/
-- QUOTE:
example (α : Type*) : Equiv.Perm α = (α ≃ α) :=
  rfl
-- QUOTE.

/- TEXT:
显然， ``Equiv.Perm α`` 在等价关系的组合下形成了一个群。我们将乘法定义为 ``mul f g`` 等于 ``g.trans f`` ，其前向函数为 ``f ∘ g`` 。换句话说，乘法就是我们通常所认为的双射的组合。这里我们定义这个群：
EXAMPLES: -/
-- QUOTE:
def permGroup {α : Type*} : Group₁ (Equiv.Perm α)
    where
  mul f g := Equiv.trans g f
  one := Equiv.refl α
  inv := Equiv.symm
  mul_assoc f g h := (Equiv.trans_assoc _ _ _).symm
  one_mul := Equiv.trans_refl
  mul_one := Equiv.refl_trans
  inv_mul_cancel := Equiv.self_trans_symm
-- QUOTE.

/- TEXT:
实际上，Mathlib 在文件 ``GroupTheory.Perm.Basic`` 中为 ``Equiv.Perm α`` 精确地定义了这个 ``Group`` 结构。
和往常一样，您可以将鼠标悬停在 ``permGroup`` 定义中使用的定理上以查看其陈述，并且可以跳转到原始文件中的定义以了解它们是如何实现的。

在普通数学中，我们通常认为符号表示与结构是相互独立的。
例如，我们可以考虑群 :math:`(G_1, \cdot, 1, \cdot^{-1})`、:math:`(G_2， \circ， e， i(\cdot))` 和 :math:`(G_3， +， 0, -)`。
在第一种情况下，我们将二元运算写为 :math:`\cdot`，单位元为 :math:`1`，逆函数为 :math:`x \mapsto x^{-1}`。
在第二种和第三种情况下，我们使用所示的符号替代形式。
然而，在 Lean 中对群的概念进行形式化时，符号表示与结构的联系更为紧密。
在 Lean 中，任何 ``Group`` 的组成部分都命名为 ``mul`` 、 ``one`` 和 ``inv`` ，稍后我们将看到乘法符号是如何与它们关联的。
如果我们想使用加法符号，则使用同构结构 ``AddGroup`` （加法群的基础结构）。其组成部分命名为 ``add`` 、 ``zero`` 和 ``neg`` ，相关符号也是您所期望的那样。

回想一下我们在 :numref:`section_structures` 中定义的类型 ``Point`` ，以及在那里定义的加法函数。这些定义在本节附带的示例文件中有所重现。作为练习，请定义一个类似于我们上面定义的 ``Group₁`` 结构的 ``AddGroup₁`` 结构，但使用刚刚描述的加法命名方案。在 ``Point`` 数据类型上定义否定和零，并在 ``Point`` 上定义 ``AddGroup₁`` 结构。
BOTH: -/
-- QUOTE:
structure AddGroup₁ (α : Type*) where
/- EXAMPLES:
  (add : α → α → α)
  -- fill in the rest
SOLUTIONS: -/
  add : α → α → α
  zero : α
  neg : α → α
  add_assoc : ∀ x y z : α, add (add x y) z = add x (add y z)
  add_zero : ∀ x : α, add x zero = x
  zero_add : ∀ x : α, add x zero = x
  neg_add_cancel : ∀ x : α, add (neg x) x = zero

-- BOTH:
@[ext]
structure Point where
  x : ℝ
  y : ℝ
  z : ℝ

namespace Point

def add (a b : Point) : Point :=
  ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

/- EXAMPLES:
def neg (a : Point) : Point := sorry

def zero : Point := sorry

def addGroupPoint : AddGroup₁ Point := sorry

SOLUTIONS: -/
def neg (a : Point) : Point :=
  ⟨-a.x, -a.y, -a.z⟩

def zero : Point :=
  ⟨0, 0, 0⟩

def addGroupPoint : AddGroup₁ Point where
  add := Point.add
  zero := Point.zero
  neg := Point.neg
  add_assoc := by simp [Point.add, add_assoc]
  add_zero := by simp [Point.add, Point.zero]
  zero_add := by simp [Point.add, Point.zero]
  neg_add_cancel := by simp [Point.add, Point.neg, Point.zero]

-- BOTH:
end Point
-- QUOTE.

/- TEXT:
我们正在取得进展。
现在我们知道了如何在 Lean 中定义代数结构，也知道如何定义这些结构的实例。
但我们还希望将符号与结构相关联，以便在每个实例中使用它。
此外，我们希望安排好，以便可以在结构上定义一个操作，并在任何特定实例中使用它，还希望安排好，以便可以在结构上证明一个定理，并在任何实例中使用它。

实际上，Mathlib 已经设置好使用通用群表示法、定义和定理来处理 ``Equiv.Perm α`` 。
EXAMPLES: -/
section
-- QUOTE:
variable {α : Type*} (f g : Equiv.Perm α) (n : ℕ)

#check f * g
#check mul_assoc f g g⁻¹

-- 群幂，定义适用于任何群
#check g ^ n

example : f * g * g⁻¹ = f := by rw [mul_assoc, mul_inv_cancel, mul_one]

example : f * g * g⁻¹ = f :=
  mul_inv_cancel_right f g

example {α : Type*} (f g : Equiv.Perm α) : g.symm.trans (g.trans f) = f :=
  mul_inv_cancel_right f g
-- QUOTE.

end

/- TEXT:
您可以检查一下，对于上面要求您定义的 ``Point`` 上的加法群结构，情况并非如此。
我们现在要做的就是理解幕后发生的神奇操作，以便让 ``Equiv.Perm α`` 的示例能够像预期那样运行。

问题在于，Lean 需要能够根据我们输入的表达式中所包含的信息来 **找到** 相关的符号表示和隐含的群结构。同样地，当我们输入 ``x + y`` 且表达式 ``x`` 和 ``y`` 的类型为 ``ℝ`` 时，Lean 需要将 ``+`` 符号解释为实数上的相关加法函数。它还必须识别类型 ``ℝ`` 是交换环的一个实例，这样所有关于交换环的定义和定理才能被使用。再举个例子，连续性在 Lean 中是相对于任意两个拓扑空间来定义的。当我们有 ``f ： ℝ → ℂ`` 并输入 ``Continuous f`` 时，Lean 必须找到 ``ℝ`` 和 ``ℂ`` 上的相关拓扑。

这种魔力是通过三者的结合实现的。

#. **逻辑** 。在任何群组中都应如此解释的定义，其参数应包含群组的类型和群组结构。同样，关于任意群组元素的定理，其开头应包含对群组类型和群组结构的全称量词。

#. **隐式参数** 。类型和结构的参数通常被隐式省略，这样我们就不必书写它们，也不必在 Lean 的信息窗口中看到它们。Lean 会默默地为我们补充这些信息。

#. **类型类推断** 。也称为 **类推断** ，这是一种简单但强大的机制，使我们能够为 Lean 注册信息以供日后使用。当 Lean 被要求为定义、定理或符号填写隐式参数时，它可以利用已注册的信息。

而注释 ``(grp : Group G)`` 告诉 Lean 它应该期望明确给出该参数，注释 ``{grp : Group G}`` 告诉 Lean 它应该尝试从表达式中的上下文线索中推断出来，注释 ``[grp ： Group G]`` 则告诉 Lean 应该使用类型类推断来合成相应的参数。由于使用此类参数的全部意义在于我们通常无需明确引用它们，Lean 允许我们写成 ``[Group G]`` 并将名称匿名化。您可能已经注意到，Lean 会选择诸如 ``_inst_1`` 这样的名称。自动地。
当我们使用带有 ``variables`` 命令的匿名方括号注释时，只要变量仍在作用域内，Lean 就会自动为提及 ``G`` 的任何定义或定理添加参数 ``[Group G]`` 。

我们如何注册 Lean 进行搜索所需的信息？
回到我们的群示例，我们只需做两个改动。
首先，我们不用 ``structure`` 命令来定义群结构，而是使用关键字 ``class`` 来表明它是一个类推断的候选对象。
其次，我们不用 ``def`` 来定义特定实例，而是使用关键字 ``instance`` 来给Lean注册特定实例。与类变量的名称一样，我们也可以让实例定义的名称保持匿名，因为通常我们希望 Lean 能够找到它并加以利用，而不必让我们操心其中的细节。
EXAMPLES: -/
-- QUOTE:
class Group₂ (α : Type*) where
  mul : α → α → α
  one : α
  inv : α → α
  mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z)
  mul_one : ∀ x : α, mul x one = x
  one_mul : ∀ x : α, mul one x = x
  inv_mul_cancel : ∀ x : α, mul (inv x) x = one

instance {α : Type*} : Group₂ (Equiv.Perm α) where
  mul f g := Equiv.trans g f
  one := Equiv.refl α
  inv := Equiv.symm
  mul_assoc f g h := (Equiv.trans_assoc _ _ _).symm
  one_mul := Equiv.trans_refl
  mul_one := Equiv.refl_trans
  inv_mul_cancel := Equiv.self_trans_symm
-- QUOTE.

/- TEXT:
以下说明了它们的用法。
EXAMPLES: -/
-- QUOTE:
#check Group₂.mul

def mySquare {α : Type*} [Group₂ α] (x : α) :=
  Group₂.mul x x

#check mySquare

section
variable {β : Type*} (f g : Equiv.Perm β)

example : Group₂.mul f g = g.trans f :=
  rfl

example : mySquare f = f.trans f :=
  rfl

end
-- QUOTE.

/- TEXT:
 ``#check`` 命令显示， ``Group₂.mul`` 有一个隐式参数 ``[Group₂ α]`` ，我们期望它通过类推断找到，其中 ``α`` 是 ``Group₂.mul`` 参数的类型。换句话说， ``{α ： Type*}`` 是群元素类型的隐式参数，而 ``[Group₂ α]`` 是 ``α`` 上的群结构的隐式参数。同样地，当我们为 ``Group₂`` 定义一个通用的平方函数 ``my_square`` 时，我们使用隐式参数 ``{α ： Type*}`` 来表示元素的类型，使用隐式参数 ``[Group₂ α]`` 来表示 ``α`` 上的 ``Group₂`` 结构。

在第一个示例中，当我们编写 ``Group₂.mul f g`` 时，f 和 g 的类型告诉 Lean 在 ``Group₂.mul`` 的参数 ``α`` 中必须实例化为 ``Equiv.Perm β`` 。这意味着 Lean 必须找到 ``Group₂ (Equiv.Perm β)`` 中的一个元素。前面的 ``instance`` 声明确切地告诉 Lean 如何做到这一点。问题解决了！

这种用于注册信息以便 Lean 在需要时能够找到它的简单机制非常有用。
这里有一个例子。
在 Lean 的基础中，数据类型“α”可能是空的。
然而，在许多应用中，知道一个类型至少有一个元素是有用的。
例如，函数 ``List.headI`` ，它返回列表的第一个元素，可以在列表为空时返回默认值。
为了实现这一点，Lean 库定义了一个类 ``Inhabited α`` ，它所做的只是存储一个默认值。
我们可以证明 ``Point`` 类型是其一个实例：
EXAMPLES: -/
-- QUOTE:
instance : Inhabited Point where default := ⟨0, 0, 0⟩

#check (default : Point)

example : ([] : List Point).headI = default :=
  rfl
-- QUOTE.

/- TEXT:
类推断机制也用于泛型表示法。
表达式 ``x + y`` 是 ``Add.add x y`` 的缩写，你猜对了————其中 ``Add α`` 是一个存储 ``α`` 上二元函数的类。
书写 ``x + y`` 会告诉 Lean 查找已注册的 ``[Add.add α]`` 实例并使用相应的函数。
下面，我们为 ``Point`` 注册加法函数。
EXAMPLES: -/
-- QUOTE:
instance : Add Point where add := Point.add

section
variable (x y : Point)

#check x + y

example : x + y = Point.add x y :=
  rfl

end
-- QUOTE.

/- TEXT:
通过这种方式，我们也可以将符号 ``+`` 用于其他类型的二元运算。
但我们还能做得更好。我们已经看到， ``*`` 可以用于任何群， ``+`` 可以用于任何加法群，而两者都可以用于任何环。
当我们在 Lean 中定义一个新的环实例时，我们不必为该实例定义 ``+`` 和 ``*`` ，因为 Lean 知道这些运算符对于每个环都是已定义的。
我们可以使用这种方法为我们的 `Group₂` 类指定符号表示法：
EXAMPLES: -/
-- QUOTE:
instance hasMulGroup₂ {α : Type*} [Group₂ α] : Mul α :=
  ⟨Group₂.mul⟩

instance hasOneGroup₂ {α : Type*} [Group₂ α] : One α :=
  ⟨Group₂.one⟩

instance hasInvGroup₂ {α : Type*} [Group₂ α] : Inv α :=
  ⟨Group₂.inv⟩

section
variable {α : Type*} (f g : Equiv.Perm α)

#check f * 1 * g⁻¹

def foo : f * 1 * g⁻¹ = g.symm.trans ((Equiv.refl α).trans f) :=
  rfl

end
-- QUOTE.

/- TEXT:
在这种情况下，我们必须为实例提供名称，因为Lean 很难想出好的默认值。
使这种方法奏效的是 Lean 进行递归搜索的能力。
根据我们声明的实例，Lean 可以通过找到 ``Group₂ (Equiv.Perm α)`` 的实例来找到 ``Mul (Equiv.Perm α)`` 的实例，而它能够找到 ``Group₂ (Equiv.Perm α)`` 的实例是因为我们已经提供了一个。
Lean 能够找到这两个事实并将它们串联起来。

我们刚刚给出的例子是危险的，因为 Lean 的库中也有一个 ``Group (Equiv.Perm α)`` 的实例，并且乘法在任何群上都有定义。所以，找到的是哪个实例是不明确的。实际上，除非您明确指定不同的优先级，否则 Lean 会倾向于更近的声明。此外，还有另一种方法可以告诉 Lean 一个结构是另一个结构的实例，即使用 ``extends`` 关键字。这就是 Mathlib 指定例如每个交换环都是环的方式。
您可以在 :numref:`hierarchies` 以及 *Theorem Proving in Lean* 中的 `关于类推断的章节 <https://leanprover.github.io/theorem_proving_in_lean4/type_classes.html#managing-type-class-inference>`_ 中找到更多信息。

一般来说，对于已经定义了记号的代数结构的实例，指定值为 ``*`` 是一个不好的主意。
在 Lean 中重新定义 ``Group`` 的概念是一个人为的例子。
然而，在这种情况下，群记号的两种解释都以相同的方式展开为 ``Equiv.trans`` 、 ``Equiv.refl`` 和 ``Equiv.symm`` 。

作为一项类似的构造性练习，仿照 ``Group₂`` 定义一个名为 ``AddGroup₂`` 的类。使用 ``Add`` 、 ``Neg`` 和 ``Zero`` 类为任何 ``AddGroup₂`` 定义加法、取反和零的常规表示法。然后证明 ``Point`` 是 ``AddGroup₂`` 的一个实例。尝试一下并确保加法群的表示法对 ``Point`` 的元素有效。
BOTH: -/
-- QUOTE:
class AddGroup₂ (α : Type*) where
/- EXAMPLES:
  add : α → α → α
  -- 请将剩余部分填写完整
-- QUOTE.
SOLUTIONS: -/
  add : α → α → α
  zero : α
  neg : α → α
  add_assoc : ∀ x y z : α, add (add x y) z = add x (add y z)
  add_zero : ∀ x : α, add x zero = x
  zero_add : ∀ x : α, add x zero = x
  neg_add_cancel : ∀ x : α, add (neg x) x = zero

instance hasAddAddGroup₂ {α : Type*} [AddGroup₂ α] : Add α :=
  ⟨AddGroup₂.add⟩

instance hasZeroAddGroup₂ {α : Type*} [AddGroup₂ α] : Zero α :=
  ⟨AddGroup₂.zero⟩

instance hasNegAddGroup₂ {α : Type*} [AddGroup₂ α] : Neg α :=
  ⟨AddGroup₂.neg⟩

instance : AddGroup₂ Point where
  add := Point.add
  zero := Point.zero
  neg := Point.neg
  add_assoc := by simp [Point.add, add_assoc]
  add_zero := by simp [Point.add, Point.zero]
  zero_add := by simp [Point.add, Point.zero]
  neg_add_cancel := by simp [Point.add, Point.neg, Point.zero]

section
variable (x y : Point)

#check x + -y + 0

end

/- TEXT:
我们上面已经为 ``Point`` 声明了实例 ``Add`` 、 ``Neg`` 和 ``Zero`` ，这并不是什么大问题。再次强调，这两种符号合成方式应该得出相同的答案。
类推断是微妙的，在使用时必须小心谨慎，因为它配置了无形中控制我们所输入表达式解释的自动化机制。然而，如果明智地使用，类推断则是一个强大的工具。正是它使得在 Lean 中进行代数推理成为可能。
TEXT. -/
