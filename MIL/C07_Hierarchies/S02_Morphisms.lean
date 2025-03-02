import MIL.Common
import Mathlib.Topology.Instances.Real

set_option autoImplicit true

/- TEXT:
.. _section_hierarchies_morphisms:

态射
---------

到目前为止，在本章我们讨论了如何创建数学结构的层次结构。
但定义结构的工作尚未完成，除非我们有了态射。这里主要有两种方法。最显而易见的方法是在函数上定义一个谓词。
BOTH: -/

-- QUOTE:
def isMonoidHom₁ [Monoid G] [Monoid H] (f : G → H) : Prop :=
  f 1 = 1 ∧ ∀ g g', f (g * g') = f g * f g'
-- QUOTE.
/- TEXT:
在这个定义中，使用合取有点不自然。特别是用户在想要访问这两个条件时，需要记住我们选择的顺序。所以我们可以使用一个结构来替代。

BOTH: -/
-- QUOTE:
structure isMonoidHom₂ [Monoid G] [Monoid H] (f : G → H) : Prop where
  map_one : f 1 = 1
  map_mul : ∀ g g', f (g * g') = f g * f g'
-- QUOTE.
/- TEXT:
一旦到了这里，不禁让人考虑将其设计为一个类，并使用类型类实例解析过程自动推断复杂函数的 ``isMonoidHom₂`` ，基于简单函数的实例。例如，两个幺半群态射的复合也是一个幺半群态射，这似乎是一个有用的实例。然而，这样的实例对于解析过程来说会非常棘手，因为它需要在每个地方寻找 ``g ∘ f`` 。在 ``g (f x)`` 中找不到它会非常令人沮丧。更一般地说，必须始终牢记，识别给定表达式中应用了哪个函数是一个非常困难的问题，称为“高阶合一问题”。因此，Mathlib 并不采用这种类的方法。

一个更根本的问题在于，我们是像上面那样使用谓词（无论是使用 ``def`` 还是 ``structure`` ），还是使用将函数和谓词捆绑在一起的结构。这在一定程度上是一个心理问题。考虑两个幺半群之间的函数，而该函数不是同态的情况极为罕见。感觉“幺半群同态”不是一个可以赋予裸函数的形容词，而是一个名词。另一方面，有人可能会说，拓扑空间之间的连续函数实际上是一个恰好连续的函数。这就是为什么 Mathlib 有一个 ``Continuous`` 谓词的原因。例如，您可以这样写：

BOTH: -/
-- QUOTE:
example : Continuous (id : ℝ → ℝ) := continuous_id
-- QUOTE.
/- TEXT:
我们仍然有连续函数的束，这在例如为连续函数空间赋予拓扑时很方便，但它们不是处理连续性的主要工具。

相比之下，单子（或其他代数结构）之间的态射是捆绑在一起的，例如：
BOTH: -/
-- QUOTE:
@[ext]
structure MonoidHom₁ (G H : Type) [Monoid G] [Monoid H]  where
  toFun : G → H
  map_one : toFun 1 = 1
  map_mul : ∀ g g', toFun (g * g') = toFun g * toFun g'

-- QUOTE.
/- TEXT:
当然，我们不想到处都输入 ``toFun`` ，所以我们使用 ``CoeFun`` 类型类来注册一个强制转换。它的第一个参数是我们想要强制转换为函数的类型。第二个参数描述目标函数类型。在我们的例子中，对于每个 ``f : MonoidHom₁ G H`` ，它总是 ``G → H`` 。我们还用 ``coe`` 属性标记 ``MonoidHom₁.toFun`` ，以确保它在策略状态中几乎不可见，仅通过 ``↑`` 前缀显示。
BOTH: -/
-- QUOTE:
instance [Monoid G] [Monoid H] : CoeFun (MonoidHom₁ G H) (fun _ ↦ G → H) where
  coe := MonoidHom₁.toFun

attribute [coe] MonoidHom₁.toFun
-- QUOTE.

/- TEXT:
让我们检查一下我们是否确实可以将捆绑的单子态射应用于一个元素。

BOTH: -/

-- QUOTE:
example [Monoid G] [Monoid H] (f : MonoidHom₁ G H) : f 1 = 1 :=  f.map_one
-- QUOTE.
/- TEXT:
于其他类型的态射，我们也可以做同样的事情，直到我们遇到环态射。
BOTH: -/

-- QUOTE:
@[ext]
structure AddMonoidHom₁ (G H : Type) [AddMonoid G] [AddMonoid H]  where
  toFun : G → H
  map_zero : toFun 0 = 0
  map_add : ∀ g g', toFun (g + g') = toFun g + toFun g'

instance [AddMonoid G] [AddMonoid H] : CoeFun (AddMonoidHom₁ G H) (fun _ ↦ G → H) where
  coe := AddMonoidHom₁.toFun

attribute [coe] AddMonoidHom₁.toFun

@[ext]
structure RingHom₁ (R S : Type) [Ring R] [Ring S] extends MonoidHom₁ R S, AddMonoidHom₁ R S

-- QUOTE.

/- TEXT:
这种方法存在一些问题。一个小问题是，我们不太清楚在哪里放置 ``coe`` 属性，因为 ``RingHom₁.toFun`` 并不存在，相关函数是 ``MonoidHom₁.toFun ∘ RingHom₁.toMonoidHom₁`` ，这并不是一个可以标记属性的声明（但我们仍然可以定义一个 ``CoeFun  (RingHom₁ R S) (fun _ ↦ R → S)`` 实例）。一个更重要的问题是，关于单子态射的引理不能直接应用。这将归结为要么每次应用单群同态引理时都与 ``RingHom₁.toMonoidHom₁`` 打交道，要么为环同态重新陈述每个这样的引理。这两种选择都不吸引人，因此 Mathlib 在这里使用了一个新的层次结构技巧。其想法是定义一个至少为单群同态的对象的类型类，用单群同态和环同态实例化该类，并使用它来陈述每个引理。在下面的定义中，  ``F``  可以是   ``MonoidHom₁ M N``  ，或者如果   ``M``   和   ``N``   具有环结构，则为   ``RingHom₁ M N``  。
BOTH: -/

-- QUOTE:
class MonoidHomClass₁ (F : Type) (M N : Type) [Monoid M] [Monoid N] where
  toFun : F → M → N
  map_one : ∀ f : F, toFun f 1 = 1
  map_mul : ∀ f g g', toFun f (g * g') = toFun f g * toFun f g'
-- QUOTE.

/- TEXT:
然而，上述实现存在一个问题。我们尚未注册到函数实例的强制转换。让我们现在尝试这样做。

BOTH: -/

-- QUOTE:
def badInst [Monoid M] [Monoid N] [MonoidHomClass₁ F M N] : CoeFun F (fun _ ↦ M → N) where
  coe := MonoidHomClass₁.toFun
-- QUOTE.

/- TEXT:
将此设为实例是不好的。当面对类似   ``f x``   的情况，而   ``f``   的类型不是函数类型时，Lean 会尝试查找一个   ``CoeFun``   实例来将   ``f``   转换为函数。上述函数的类型为：
 ``{M N F : Type} → [Monoid M] → [Monoid N] → [MonoidHomClass₁ F M N] → CoeFun F (fun x ↦ M → N)``
因此，在尝试应用它时，Lean 无法预先确定未知类型   ``M``  、  ``N``  和   ``F``   应该以何种顺序进行推断。这与我们之前看到的情况略有不同，但归根结底是同一个问题：在不知道   ``M``   的情况下，Lean 将不得不在未知类型上搜索单子实例，从而无望地尝试数据库中的每一个单子实例。如果您想看看这种实例的效果，可以在上述声明的顶部输入   ``set_option synthInstance.checkSynthOrder false in``  ，将   ``def badInst``   替换为   ``instance``  ，然后在这个文件中查找随机出现的错误。

在这里，解决方案很简单，我们需要告诉 Lean 先查找什么是 ``F`` ，然后再推导出 ``M`` 和 ``N`` 。这可以通过使用 ``outParam`` 函数来实现。该函数被定义为恒等函数，但仍会被类型类机制识别，并触发所需的行为。因此，我们可以重新定义我们的类，注意使用 ``outParam`` 函数：
BOTH: -/

-- QUOTE:
class MonoidHomClass₂ (F : Type) (M N : outParam Type) [Monoid M] [Monoid N] where
  toFun : F → M → N
  map_one : ∀ f : F, toFun f 1 = 1
  map_mul : ∀ f g g', toFun f (g * g') = toFun f g * toFun f g'

instance [Monoid M] [Monoid N] [MonoidHomClass₂ F M N] : CoeFun F (fun _ ↦ M → N) where
  coe := MonoidHomClass₂.toFun

attribute [coe] MonoidHomClass₂.toFun
-- QUOTE.

/- TEXT:
现在我们可以继续执行我们的计划，实例化这个类了。

BOTH: -/

-- QUOTE:
instance (M N : Type) [Monoid M] [Monoid N] : MonoidHomClass₂ (MonoidHom₁ M N) M N where
  toFun := MonoidHom₁.toFun
  map_one := fun f ↦ f.map_one
  map_mul := fun f ↦ f.map_mul

instance (R S : Type) [Ring R] [Ring S] : MonoidHomClass₂ (RingHom₁ R S) R S where
  toFun := fun f ↦ f.toMonoidHom₁.toFun
  map_one := fun f ↦ f.toMonoidHom₁.map_one
  map_mul := fun f ↦ f.toMonoidHom₁.map_mul
-- QUOTE.

/- TEXT:
正如所承诺的那样，我们对 ``f : F`` 在假设存在 ``MonoidHomClass₁ F`` 的实例的情况下所证明的每个引理，都将同时适用于幺半群同态和环同态。让我们来看一个示例引理，并检查它是否适用于这两种情况。
BOTH: -/

-- QUOTE:
lemma map_inv_of_inv [Monoid M] [Monoid N] [MonoidHomClass₂ F M N] (f : F) {m m' : M} (h : m*m' = 1) :
    f m * f m' = 1 := by
  rw [← MonoidHomClass₂.map_mul, h, MonoidHomClass₂.map_one]

example [Monoid M] [Monoid N] (f : MonoidHom₁ M N) {m m' : M} (h : m*m' = 1) : f m * f m' = 1 :=
map_inv_of_inv f h

example [Ring R] [Ring S] (f : RingHom₁ R S) {r r' : R} (h : r*r' = 1) : f r * f r' = 1 :=
map_inv_of_inv f h

-- QUOTE.

/- TEXT:
乍一看，可能会觉得我们又回到了之前那个糟糕的想法，即把   ``MonoidHom₁``   设为一个类。
但其实并非如此。一切都提升了一个抽象层次。类型类解析过程不会寻找函数，而是寻找   ``MonoidHom₁``   或者   ``RingHom₁``   。

我们方法中仍存在的一个问题是在围绕   ``toFun``   字段以及相应的   ``CoeFun``   实例和   ``coe``   属性的地方存在重复代码。另外，最好记录下这种模式仅用于具有额外属性的函数，这意味着对函数的强制转换应该是单射的。因此，Mathlib 在这个基础层之上又增加了一层抽象，即基础类   ``DFunLike``  （其中“DFun”代表依赖函数）。让我们基于这个基础层重新定义我们的   ``MonoidHomClass``  。

BOTH: -/

-- QUOTE:
class MonoidHomClass₃ (F : Type) (M N : outParam Type) [Monoid M] [Monoid N] extends
    DFunLike F M (fun _ ↦ N) where
  map_one : ∀ f : F, f 1 = 1
  map_mul : ∀ (f : F) g g', f (g * g') = f g * f g'

instance (M N : Type) [Monoid M] [Monoid N] : MonoidHomClass₃ (MonoidHom₁ M N) M N where
  coe := MonoidHom₁.toFun
  coe_injective' _ _ := MonoidHom₁.ext
  map_one := MonoidHom₁.map_one
  map_mul := MonoidHom₁.map_mul
-- QUOTE.

/- TEXT:
当然，态射的层次结构不止于此。我们还可以继续定义一个类   ``RingHomClass₃``   来扩展   ``MonoidHomClass₃``   ，然后将其实例化为   ``RingHom``   ，之后再实例化为   ``AlgebraHom``   （代数是具有某些额外结构的环）。不过，我们已经涵盖了 Mathlib 中用于态射的主要形式化思想，您应该已经准备好理解 Mathlib 中态射的定义方式了。
作为练习，您应当尝试定义有序类型之间的保序函数类，以及保序幺半群同态。这仅用于训练目的。与连续函数类似，在 Mathlib 中保序函数主要是未打包的，它们通过   ``Monotone``   预言来定义。当然，您需要完成下面的类定义。
BOTH: -/

-- QUOTE:
@[ext]
structure OrderPresHom (α β : Type) [LE α] [LE β] where
  toFun : α → β
  le_of_le : ∀ a a', a ≤ a' → toFun a ≤ toFun a'

@[ext]
structure OrderPresMonoidHom (M N : Type) [Monoid M] [LE M] [Monoid N] [LE N] extends
MonoidHom₁ M N, OrderPresHom M N

class OrderPresHomClass (F : Type) (α β : outParam Type) [LE α] [LE β]
-- SOLUTIONS:
extends DFunLike F α (fun _ ↦ β) where
  le_of_le : ∀ (f : F) a a', a ≤ a' → f a ≤ f a'
-- BOTH:

instance (α β : Type) [LE α] [LE β] : OrderPresHomClass (OrderPresHom α β) α β where
-- SOLUTIONS:
  coe := OrderPresHom.toFun
  coe_injective' _ _ := OrderPresHom.ext
  le_of_le := OrderPresHom.le_of_le
-- BOTH:

instance (α β : Type) [LE α] [Monoid α] [LE β] [Monoid β] :
    OrderPresHomClass (OrderPresMonoidHom α β) α β where
-- SOLUTIONS:
  coe := fun f ↦ f.toOrderPresHom.toFun
  coe_injective' _ _ := OrderPresMonoidHom.ext
  le_of_le := fun f ↦ f.toOrderPresHom.le_of_le
-- BOTH:

instance (α β : Type) [LE α] [Monoid α] [LE β] [Monoid β] :
    MonoidHomClass₃ (OrderPresMonoidHom α β) α β
/- EXAMPLES:
  := sorry
SOLUTIONS: -/
where
  coe := fun f ↦ f.toOrderPresHom.toFun
  coe_injective' _ _ := OrderPresMonoidHom.ext
  map_one := fun f ↦ f.toMonoidHom₁.map_one
  map_mul := fun f ↦ f.toMonoidHom₁.map_mul
-- QUOTE.
