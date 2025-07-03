import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Fintype.BigOperators

/- TEXT:
.. _finsets_and_fintypes:

有限集合和有限类型
--------------------

在 Mathlib 中处理有限集合和有限类型可能会令人困惑，因为库提供了多种处理方式。在这一节中，我们将讨论最常见的方法。

我们已经在 :numref:`section_induction_and_recursion` 和 :numref:`section_infinitely_many_primes` 中遇到了类型 ``Finset``。
顾名思义，类型 ``Finset α`` 的元素是类型 ``α`` 的元素的有限集合。
我们将这些称为"有限集合"。
``Finset`` 数据类型设计为具有计算解释，
``Finset α`` 的许多基本操作都假设 ``α`` 具有可判定的相等性，
这保证了有一个算法可以测试 ``a : α`` 是否是有限集合 ``s`` 的元素。
EXAMPLES: -/
-- QUOTE:
section
variable {α : Type*} [DecidableEq α] (a : α) (s t : Finset α)

#check a ∈ s
#check s ∩ t

end
-- QUOTE.

/- TEXT:
如果你删除声明 ``[DecidableEq α]``，Lean 会在 ``#check s ∩ t`` 这一行报错，
因为它无法计算交集。
然而，所有你应该能够计算的数据类型都具有可判定的相等性，
如果你通过打开 ``Classical`` 命名空间并声明 ``noncomputable section`` 来进行经典推理，
你可以对任何类型的元素的有限集合进行推理。

有限集合支持集合论的大部分运算：
EXAMPLES: -/
-- QUOTE:
open Finset

variable (a b c : Finset ℕ)
variable (n : ℕ)

#check a ∩ b
#check a ∪ b
#check a \ b
#check (∅ : Finset ℕ)

example : a ∩ (b ∪ c) = (a ∩ b) ∪ (a ∩ c) := by
  ext x; simp only [mem_inter, mem_union]; tauto

example : a ∩ (b ∪ c) = (a ∩ b) ∪ (a ∩ c) := by rw [inter_union_distrib_left]
-- QUOTE.

/- TEXT:
请注意，我们已经打开了 ``Finset`` 命名空间，
在这里可以找到特定于有限集合的定理。
如果你逐步执行下面的最后一个例子，你会看到应用 ``ext`` 后跟 ``simp``
将恒等式简化为命题逻辑的问题。
作为练习，你可以尝试证明 :numref:`第 %s 章 <sets_and_functions>` 中的一些集合恒等式，
并将它们转换为有限集合。

你已经见过记法 ``Finset.range n`` 表示自然数的有限集合 :math:`\{ 0, 1, \ldots, n-1 \}`。
``Finset`` 还允许你通过枚举元素来定义有限集合：
TEXT. -/
-- QUOTE:
#check ({0, 2, 5} : Finset Nat)

def example1 : Finset ℕ := {0, 1, 2}
-- QUOTE.

/- TEXT:
有多种方式可以让 Lean 识别出以这种方式呈现的集合中元素的顺序和重复
项都无关紧要。
EXAMPLES: -/
-- QUOTE:
example : ({0, 1, 2} : Finset ℕ) = {1, 2, 0} := by decide

example : ({0, 1, 2} : Finset ℕ) = {0, 1, 1, 2} := by decide

example : ({0, 1} : Finset ℕ) = {1, 0} := by rw [Finset.pair_comm]

example (x : Nat) : ({x, x} : Finset ℕ) = {x} := by simp

example (x y z : Nat) : ({x, y, z, y, z, x} : Finset ℕ) = {x, y, z} := by
  ext i; simp [or_comm, or_assoc, or_left_comm]

example (x y z : Nat) : ({x, y, z, y, z, x} : Finset ℕ) = {x, y, z} := by
  ext i; simp; tauto
-- QUOTE.

/- TEXT:
你可以使用 ``insert`` 向 Finset 中添加单个元素，使用 ``Finset.erase``
删除单个元素。
请注意，``erase`` 在 ``Finset`` 命名空间中，但 ``insert`` 在根命名空间中。
EXAMPLES: -/
-- QUOTE:
example (s : Finset ℕ) (a : ℕ) (h : a ∉ s) : (insert a s |>.erase a) = s :=
  Finset.erase_insert h

example (s : Finset ℕ) (a : ℕ) (h : a ∈ s) : insert a (s.erase a) = s :=
  Finset.insert_erase h
-- QUOTE.

/- TEXT:
实际上，``{0, 1, 2}`` 只是 ``insert 0 (insert 1 (singleton 2))`` 的记法。
EXAMPLES: -/
-- QUOTE:
set_option pp.notation false in
#check ({0, 1, 2} : Finset ℕ)
-- QUOTE.

/- TEXT:
给定一个有限集合 ``s`` 和一个谓词 ``P``，我们可以使用集合构造记法 ``{x ∈ s | P x}`` 来
定义 ``s`` 中满足 ``P`` 的元素的集合。
这是 ``Finset.filter P s`` 的记法，也可以写作 ``s.filter P``。
EXAMPLES: -/
-- QUOTE:
example : {m ∈ range n | Even m} = (range n).filter Even := rfl
example : {m ∈ range n | Even m ∧ m ≠ 3} = (range n).filter (fun m ↦ Even m ∧ m ≠ 3) := rfl

example : {m ∈ range 10 | Even m} = {0, 2, 4, 6, 8} := by decide
-- QUOTE.

/- TEXT:
Mathlib 知道有限集合在函数下的像是有限集合。
EXAMPLES: -/
-- QUOTE:
#check (range 5).image (fun x ↦ x * 2)

example : (range 5).image (fun x ↦ x * 2) = {x ∈ range 10 | Even x} := by decide
-- QUOTE.

/- TEXT:
Lean 也知道两个有限集合的笛卡尔积 ``s ×ˢ t`` 是有限集合，
以及有限集合的幂集是有限集合。（请注意，记法 ``s ×ˢ t`` 也适用于集合。）
EXAMPLES: -/
section
variable (s t : Finset Nat)
-- QUOTE:
#check s ×ˢ t
#check s.powerset
-- QUOTE.

end

/- TEXT:
根据有限集合的元素来定义运算是很棘手的，因为任何这样的定义都必须
与元素呈现的顺序无关。
当然，你总是可以通过组合现有的运算来定义函数。
你还可以做的另一件事是使用 ``Finset.fold`` 对元素进行二元运算的折叠，
前提是运算具有结合律和交换律，
因为这些性质保证了结果与运算应用的顺序无关。有限和、有限积和有限并都是这样定义的。
在下面的最后一个例子中，``biUnion`` 表示"有界索引并"。
用传统的数学记法，这个表达式会写作 :math:`\bigcup_{i ∈ s} g(i)`。
EXAMPLES: -/
namespace finsets_and_fintypes
-- QUOTE:
#check Finset.fold

def f (n : ℕ) : Int := (↑n)^2

#check (range 5).fold (fun x y : Int ↦ x + y) 0 f
#eval (range 5).fold (fun x y : Int ↦ x + y) 0 f

#check ∑ i ∈ range 5, i^2
#check ∏ i ∈ range 5, i + 1

variable (g : Nat → Finset Int)

#check (range 5).biUnion g
-- QUOTE.

end finsets_and_fintypes

/- TEXT:
有限集合有一个自然的归纳原理：要证明每个有限集合都有某个性质，
需要证明空集有这个性质，并且当我们向有限集合中添加一个新元素时，
这个性质得到保持。（在下一个例子的归纳步骤中，``@insert`` 中的 ``@`` 符号是必需的，
用于给参数 ``a`` 和 ``s`` 命名，因为它们被标记为隐式参数。）
EXAMPLES: -/
-- QUOTE:
#check Finset.induction

example {α : Type*} [DecidableEq α] (f : α → ℕ)  (s : Finset α) (h : ∀ x ∈ s, f x ≠ 0) :
    ∏ x ∈ s, f x ≠ 0 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s anins ih =>
    rw [prod_insert anins]
    apply mul_ne_zero
    · apply h; apply mem_insert_self
    apply ih
    intros x xs
    exact h x (mem_insert_of_mem xs)
-- QUOTE.

/- TEXT:
如果 ``s`` 是有限集合，``Finset.Nonempty s`` 定义为 ``∃ x, x ∈ s``。
你可以使用经典选择来从非空有限集合中选择一个元素。类似地，
库定义了 ``Finset.toList s``，它使用选择按某种顺序选择 ``s`` 的元素。
EXAMPLES: -/
-- QUOTE:
noncomputable example (s : Finset ℕ) (h : s.Nonempty) : ℕ := Classical.choose h

example (s : Finset ℕ) (h : s.Nonempty) : Classical.choose h ∈ s := Classical.choose_spec h

noncomputable example (s : Finset ℕ) : List ℕ := s.toList

example (s : Finset ℕ) (a : ℕ) : a ∈ s.toList ↔ a ∈ s := mem_toList
-- QUOTE.

/- TEXT:
你可以使用 ``Finset.min`` 和 ``Finset.max`` 来选择线性序的有限集合中的最小或最大元素，
类似地，你可以对格的有限集合使用 ``Finset.inf`` 和 ``Finset.sup``，但有一个问题。
空有限集合的最小元素应该是什么？
你可以检查下面函数的带撇版本添加了有限集合非空的前提条件。
不带撇的版本 ``Finset.min`` 和 ``Finset.max`` 分别向输出类型添加一个顶元素或底元素，
以处理有限集合为空的情况。
不带撇的版本 ``Finset.inf`` 和 ``Finset.sup`` 假设格分别配备了顶元素或底元素。
EXAMPLES: -/
-- QUOTE:
#check Finset.min
#check Finset.min'
#check Finset.max
#check Finset.max'
#check Finset.inf
#check Finset.inf'
#check Finset.sup
#check Finset.sup'

example : Finset.Nonempty {2, 6, 7} := ⟨6, by trivial⟩
example : Finset.min' {2, 6, 7} ⟨6, by trivial⟩ = 2 := by trivial
-- QUOTE.

/- TEXT:
每个有限集合 ``s`` 都有一个有限的基数 ``Finset.card s``，当 ``Finset`` 命名空间打开时，
可以写作 ``#s``。

EXAMPLES: -/
-- QUOTE:
#check Finset.card

#eval (range 5).card

example (s : Finset ℕ) : s.card = #s := by rfl

example (s : Finset ℕ) : s.card = ∑ i ∈ s, 1 := by rw [card_eq_sum_ones]

example (s : Finset ℕ) : s.card = ∑ i ∈ s, 1 := by simp
-- QUOTE.

/- TEXT:
下一节完全是关于对基数的推理。

在形式化数学时，人们经常需要决定是用集合还是用类型来表达
定义和定理。
使用类型通常简化记法和证明，但使用类型的子集可能更灵活。
有限集合的基于类型的对应物是 *有限类型*，即某个 ``α`` 的类型 ``Fintype α``。
根据定义，有限类型只是一个数据类型，它配备了一个包含所有其元素的有限集合 ``univ``。
EXAMPLES: -/
section
-- QUOTE:
variable {α : Type*} [Fintype α]

example : ∀ x : α, x ∈ Finset.univ := by
  intro x; exact mem_univ x
-- QUOTE.

/- TEXT:
``Fintype.card α`` 等于相应有限集合的基数。
EXAMPLES: -/
-- QUOTE:
example : Fintype.card α = (Finset.univ : Finset α).card := rfl
-- QUOTE.
end

/- TEXT:
我们已经见过有限类型的一个原型例子，即对每个 ``n`` 的类型 ``Fin n``。
Lean 识别出有限类型在像积运算这样的运算下是封闭的。
EXAMPLES: -/
-- QUOTE:
example : Fintype.card (Fin 5) = 5 := by simp
example : Fintype.card ((Fin 5) × (Fin 3)) = 15 := by simp
-- QUOTE.

/- TEXT:
``Finset α`` 的任何元素 ``s`` 都可以强制转换为类型 ``(↑s : Finset α)``，
即包含在 ``s`` 中的 ``α`` 的元素的子类型。
EXAMPLES: -/
section
-- QUOTE:
variable (s : Finset ℕ)

example : (↑s : Type) = {x : ℕ // x ∈ s} := rfl
example : Fintype.card ↑s = s.card := by simp
-- QUOTE.
end

/- TEXT:
Lean 和 Mathlib 使用 *类型类推断* 来追踪有限类型上的附加结构，
即包含所有元素的通用有限集合。
换句话说，你可以将有限类型看作是配备了额外数据的代数结构。
:numref:`第 %s 章 <structures>` 解释了这是如何工作的。
EXAMPLES: -/
