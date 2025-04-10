import MIL.Common
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Real.Basic

set_option autoImplicit true

/- TEXT:
.. _section_hierarchies_basics:

基础
------

在Lean的所有层次结构的最底层，我们能找到承载数据的类。下面这个类记录了给定类型 ``α`` 具有一个被称为 ``one`` 的特殊元素。在现阶段，它没有任何属性。
BOTH: -/

-- QUOTE:
class One₁ (α : Type) where
  /-- The element one -/
  one : α
-- QUOTE.

/- TEXT:
由于在本章中我们将更频繁地使用类，所以我们需要进一步了解 ``class`` 命令的作用。
首先，上述的 ``class`` 命令定义了一个结构体 ``One₁`` ，其参数为 ``α : Type`` ，且只有一个字段 ``one`` 。它还标记此结构体为类，这样对于某些类型 ``α`` 的 ``One₁ α`` 类型的参数，只要它们被标记为实例隐式参数（即出现在方括号中），就可以通过实例解析过程进行推断。
这两个效果也可以通过带有 ``class`` 属性的 ``structure`` 命令来实现，即写成 ``@[class] structure`` 的形式。但 ``class`` 命令还确保了 ``One₁ α`` 在其自身的字段中以实例隐式参数的形式出现。比较：
BOTH: -/

-- QUOTE:
#check One₁.one -- One₁.one {α : Type} [self : One₁ α] : α

@[class] structure One₂ (α : Type) where
  /-- The element one -/
  one : α

#check One₂.one
-- QUOTE.

/- TEXT:
在第二次检查中，我们可以看到 ``self : One₂ α`` 是一个显式参数。
让我们确保第一个版本确实可以在没有任何显式参数的情况下使用。
BOTH: -/

-- QUOTE:
example (α : Type) [One₁ α] : α := One₁.one
-- QUOTE.

/- TEXT:
备注：在上述示例中，参数 ``One₁ α`` 被标记为实例隐式，这有点蠢，因为这仅影响该声明的 **使用** ，而由 ``example`` 命令创建的声明无法被使用。不过，这使我们能够避免为该参数命名，更重要的是，它开始养成将 ``One₁ α`` 参数标记为实例隐式的良好习惯。

另一个需要注意的地方是，只有当 Lean 知道 ``α`` 是什么时，上述所有内容才会起作用。在上述示例中，如果省略类型标注 ``: α`` ，则会生成类似以下的错误消息：
 ``typeclass instance problem is stuck, it is often due to metavariables One₁ (?m.263 α)``
其中 ``?m.263 α`` 表示“依赖于 ``α`` 的某种类型”（263 只是一个自动生成的索引，用于区分多个未知事物）。另一种避免此问题的方法是使用类型注解，例如：
BOTH: -/
-- QUOTE:
example (α : Type) [One₁ α] := (One₁.one : α)
-- QUOTE.

/- TEXT:
如果您在 :numref:`sequences_and_convergence` 中尝试处理数列的极限时遇到过这个问题，那么您可能已经遇到过这种情况，比如您试图声明 ``0 < 1`` ，但没有告诉 Lean 您是想表示自然数之间的不等式还是实数之间的不等式。

我们的下一个任务是为 ``One₁.one`` 指定一个符号。由于我们不想与内置的 ``1`` 符号发生冲突，我们将使用 ``𝟙`` 。这是通过以下命令实现的，其中第一行告诉 Lean 使用 ``One₁.one`` 的文档作为符号 ``𝟙`` 的文档。
BOTH: -/
-- QUOTE:
@[inherit_doc]
notation "𝟙" => One₁.one

example {α : Type} [One₁ α] : α := 𝟙

example {α : Type} [One₁ α] : (𝟙 : α) = 𝟙 := rfl
-- QUOTE.

/- TEXT:
我们现在想要一个记录二元运算的数据承载类。目前我们不想在加法和乘法之间做出选择，所以我们将使用菱形。
BOTH: -/

-- QUOTE:
class Dia₁ (α : Type) where
  dia : α → α → α

infixl:70 " ⋄ "   => Dia₁.dia
-- QUOTE.

/- TEXT:
与 ``One₁`` 示例一样，此时该运算没有任何属性。现在让我们定义一个半群结构类，其中运算用 ``⋄`` 表示。目前，我们手动将其定义为具有两个字段的结构，一个 ``Dia₁`` 实例和一个值为 ``Prop`` 的字段 ``dia_assoc`` ，用于断言 ``⋄`` 的结合性。
BOTH: -/

-- QUOTE:
class Semigroup₁ (α : Type) where
  toDia₁ : Dia₁ α
  /-- Diamond is associative -/
  dia_assoc : ∀ a b c : α, a ⋄ b ⋄ c = a ⋄ (b ⋄ c)
-- QUOTE.

/- TEXT:
请注意，在声明 ``dia_assoc`` 时，先前定义的字段 ``toDia₁`` 在本地上下文中，因此在 Lean 搜索 ``Dia₁ α`` 的实例以理解 ``a ⋄ b`` 时可以使用它。但是这个 ``toDia₁`` 字段不会成为类型类实例数据库的一部分。因此，执行 ``example {α : Type} [Semigroup₁ α] (a b : α) : α := a ⋄ b`` 将会失败。错误消息 ``failed to synthesize instance Dia₁ α`` 。

我们可以通过稍后添加 ``instance`` 属性来解决这个问题。
BOTH: -/

-- QUOTE:
attribute [instance] Semigroup₁.toDia₁

example {α : Type} [Semigroup₁ α] (a b : α) : α := a ⋄ b
-- QUOTE.

/- TEXT:
在构建之前，我们需要一种比显式编写诸如 `toDia₁` 这样的字段并手动添加实例属性更方便的方式来扩展结构。 ``class`` 使用如下语法通过 ``extends`` 支持这一点：
BOTH: -/

-- QUOTE:
class Semigroup₂ (α : Type) extends Dia₁ α where
  /-- Diamond is associative -/
  dia_assoc : ∀ a b c : α, a ⋄ b ⋄ c = a ⋄ (b ⋄ c)

example {α : Type} [Semigroup₂ α] (a b : α) : α := a ⋄ b
-- QUOTE.

/- TEXT:
请注意，这种语法在 ``structure`` 命令中也是可用的，尽管在这种情况下，它仅解决了编写诸如 `toDia₁` 这样的字段的麻烦，因为在那种情况下没有实例需要定义。

现在让我们尝试将一个菱形运算和一个特殊操作结合起来，并用公理说明这个元素在两边都是零元。
BOTH: -/
-- QUOTE:
class DiaOneClass₁ (α : Type) extends One₁ α, Dia₁ α where
  /-- 存在一个对于菱形运算的左零元。 -/
  one_dia : ∀ a : α, 𝟙 ⋄ a = a
  /-- 存在一个对于菱形运算的右零元。 -/
  dia_one : ∀ a : α, a ⋄ 𝟙 = a

-- QUOTE.

/- TEXT:
在下一个示例中，我们告诉 Lean ``α`` 具有 ``DiaOneClass₁`` 结构，并声明一个使用 ``Dia₁`` 实例和 ``One₁`` 实例的属性。为了查看 Lean 如何找到这些实例，我们设置了一个跟踪选项，其结果可以在 Infoview 中看到。默认情况下，该结果相当简略，但可以通过点击以黑色箭头结尾的行来展开。它包括 Lean 在拥有足够的类型信息之前尝试查找实例但未成功的尝试。成功的尝试确实涉及由 ``extends`` 语法生成的实例。
BOTH: -/

-- QUOTE:
set_option trace.Meta.synthInstance true in
example {α : Type} [DiaOneClass₁ α] (a b : α) : Prop := a ⋄ b = 𝟙
-- QUOTE.

/- TEXT:
请注意，在组合现有类时，我们不需要包含额外的字段。因此，我们可以将半群定义为：
BOTH: -/

-- QUOTE:
class Monoid₁ (α : Type) extends Semigroup₁ α, DiaOneClass₁ α
-- QUOTE.

/- TEXT:
虽然上述定义看起来很简单，但它隐藏了一个重要的微妙之处。 ``Semigroup₁ α`` 和 ``DiaOneClass₁ α`` 都扩展了 ``Dia₁ α`` ，所以有人可能会担心，拥有一个 ``Monoid₁ α`` 实例会在 ``α`` 上产生两个不相关的菱形运算，一个来自字段 ``Monoid₁.toSemigroup₁`` ，另一个来自字段 ``Monoid₁.toDiaOneClass₁`` 。

实际上，如果我们尝试通过以下方式手动构建一个单子类：
BOTH: -/

-- QUOTE:
class Monoid₂ (α : Type) where
  toSemigroup₁ : Semigroup₁ α
  toDiaOneClass₁ : DiaOneClass₁ α
-- QUOTE.

/- TEXT:
那么我们会得到两个完全不相关的菱形运算
 ``Monoid₂.toSemigroup₁.toDia₁.dia`` 和 ``Monoid₂.toDiaOneClass₁.toDia₁.dia`` 。

使用 ``extends`` 语法生成的版本不存在此缺陷。
BOTH: -/

-- QUOTE:
example {α : Type} [Monoid₁ α] :
  (Monoid₁.toSemigroup₁.toDia₁.dia : α → α → α) = Monoid₁.toDiaOneClass₁.toDia₁.dia := rfl
-- QUOTE.

/- TEXT:
所以 ``class`` 命令为我们做了些神奇的事（ ``structure`` 命令也会这样做）。查看类的构造函数是了解其字段的简便方法。比较：
BOTH: -/

-- QUOTE:
/- Monoid₂.mk {α : Type} (toSemigroup₁ : Semigroup₁ α) (toDiaOneClass₁ : DiaOneClass₁ α) : Monoid₂ α -/
#check Monoid₂.mk

/- Monoid₁.mk {α : Type} [toSemigroup₁ : Semigroup₁ α] [toOne₁ : One₁ α] (one_dia : ∀ (a : α), 𝟙 ⋄ a = a) (dia_one : ∀ (a : α), a ⋄ 𝟙 = a) : Monoid₁ α -/
#check Monoid₁.mk
-- QUOTE.

/- TEXT:
所以我们看到 ``Monoid₁`` 按预期接受 ``Semigroup₁ α`` 参数，但不会接受可能重叠的 ``DiaOneClass₁ α`` 参数，而是将其拆分并仅包含不重叠的部分。它还自动生成了一个实例 ``Monoid₁.toDiaOneClass₁`` ，这并非字段，但具有预期的签名，从最终用户的角度来看，这恢复了两个扩展类 ``Semigroup₁`` 和 ``DiaOneClass₁`` 之间的对称性。
BOTH: -/

-- QUOTE:
#check Monoid₁.toSemigroup₁
#check Monoid₁.toDiaOneClass₁
-- QUOTE.

/- TEXT:
我们现在离定义群非常接近了。我们可以在单子结构中添加一个字段，断言每个元素都存在逆元。但那样的话，我们需要努力才能访问这些逆元。实际上，将其作为数据添加会更方便。为了优化可重用性，我们定义一个新的携带数据的类，然后为其提供一些符号表示。
BOTH: -/

-- QUOTE:
class Inv₁ (α : Type) where
  /-- The inversion function -/
  inv : α → α

@[inherit_doc]
postfix:max "⁻¹" => Inv₁.inv

class Group₁ (G : Type) extends Monoid₁ G, Inv₁ G where
  inv_dia : ∀ a : G, a⁻¹ ⋄ a = 𝟙
-- QUOTE.

/- TEXT:
上述定义可能看起来太弱了，我们只要求 ``a⁻¹`` 是 ``a`` 的左逆元。但另一侧是自动的。为了证明这一点，我们需要一个预备引理。
BOTH: -/

-- QUOTE:
lemma left_inv_eq_right_inv₁ {M : Type} [Monoid₁ M] {a b c : M} (hba : b ⋄ a = 𝟙) (hac : a ⋄ c = 𝟙) : b = c := by
  rw [← DiaOneClass₁.one_dia c, ← hba, Semigroup₁.dia_assoc, hac, DiaOneClass₁.dia_one b]
-- QUOTE.

/- TEXT:
在这个引理中，给出全名相当烦人，尤其是因为这需要知道这些事实是由层次结构中的哪一部分提供的。解决这个问题的一种方法是使用 ``export`` 命令将这些事实作为引理复制到根名称空间中。
BOTH: -/

-- QUOTE:
export DiaOneClass₁ (one_dia dia_one)
export Semigroup₁ (dia_assoc)
export Group₁ (inv_dia)
-- QUOTE.

/- TEXT:
然后我们可以将上述证明重写为：
BOTH: -/

-- QUOTE:
example {M : Type} [Monoid₁ M] {a b c : M} (hba : b ⋄ a = 𝟙) (hac : a ⋄ c = 𝟙) : b = c := by
  rw [← one_dia c, ← hba, dia_assoc, hac, dia_one b]
-- QUOTE.

/- TEXT:
现在轮到你来证明我们代数结构的性质了。
BOTH: -/

-- QUOTE:
lemma inv_eq_of_dia [Group₁ G] {a b : G} (h : a ⋄ b = 𝟙) : a⁻¹ = b :=
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  left_inv_eq_right_inv₁ (inv_dia a) h
-- BOTH:

lemma dia_inv [Group₁ G] (a : G) : a ⋄ a⁻¹ = 𝟙 :=
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  by rw [← inv_dia a⁻¹, inv_eq_of_dia (inv_dia a)]
-- QUOTE.

/- TEXT:
在这个阶段，我们想继续定义环，但有一个严重的问题。一个类型的环结构包含一个加法群结构和一个乘法半群结构，以及它们相互作用的一些性质。但到目前为止，我们为所有操作硬编码了一个符号 ``⋄`` 。更根本的是，类型类系统假定每个类型对于每个类型类只有一个实例。有多种方法可以解决这个问题。令人惊讶的是，Mathlib 使用了一个朴素的想法，借助一些代码生成属性，为加法和乘法理论复制了所有内容。结构和类以加法和乘法两种记法定义，并通过属性 ``to_additive`` 相互关联。对于像半群这样的多重继承情况，自动生成的“恢复对称性”的实例也需要进行标记。这有点技术性，您无需理解细节。重要的是，引理仅以乘法记法陈述，并通过属性 ``to_additive`` 标记，以生成加法版本为 ``left_inv_eq_right_inv'`` ，其自动生成的加法版本为 ``left_neg_eq_right_neg'`` 。为了检查这个加法版本的名称，我们在 ``left_inv_eq_right_inv'`` 之上使用了 ``whatsnew in`` 命令。
BOTH: -/

-- QUOTE:



class AddSemigroup₃ (α : Type) extends Add α where
/-- Addition is associative -/
  add_assoc₃ : ∀ a b c : α, a + b + c = a + (b + c)

@[to_additive AddSemigroup₃]
class Semigroup₃ (α : Type) extends Mul α where
/-- Multiplication is associative -/
  mul_assoc₃ : ∀ a b c : α, a * b * c = a * (b * c)

class AddMonoid₃ (α : Type) extends AddSemigroup₃ α, AddZeroClass α

@[to_additive AddMonoid₃]
class Monoid₃ (α : Type) extends Semigroup₃ α, MulOneClass α

attribute [to_additive existing] Monoid₃.toMulOneClass

export Semigroup₃ (mul_assoc₃)
export AddSemigroup₃ (add_assoc₃)

whatsnew in
@[to_additive]
lemma left_inv_eq_right_inv' {M : Type} [Monoid₃ M] {a b c : M} (hba : b * a = 1) (hac : a * c = 1) : b = c := by
  rw [← one_mul c, ← hba, mul_assoc₃, hac, mul_one b]

#check left_neg_eq_right_neg'
-- QUOTE.

/- TEXT:
借助这项技术，我们可以轻松定义交换半群、幺半群和群，然后定义环。
BOTH: -/
-- QUOTE:
class AddCommSemigroup₃ (α : Type) extends AddSemigroup₃ α where
  add_comm : ∀ a b : α, a + b = b + a

@[to_additive AddCommSemigroup₃]
class CommSemigroup₃ (α : Type) extends Semigroup₃ α where
  mul_comm : ∀ a b : α, a * b = b * a

class AddCommMonoid₃ (α : Type) extends AddMonoid₃ α, AddCommSemigroup₃ α

@[to_additive AddCommMonoid₃]
class CommMonoid₃ (α : Type) extends Monoid₃ α, CommSemigroup₃ α

class AddGroup₃ (G : Type) extends AddMonoid₃ G, Neg G where
  neg_add : ∀ a : G, -a + a = 0

@[to_additive AddGroup₃]
class Group₃ (G : Type) extends Monoid₃ G, Inv G where
  inv_mul : ∀ a : G, a⁻¹ * a = 1
-- QUOTE.

/- TEXT:
我们应当在适当的时候用 ``simp`` 标记引理。
BOTH: -/

-- QUOTE:
attribute [simp] Group₃.inv_mul AddGroup₃.neg_add

-- QUOTE.

/- TEXT:
然后我们需要重复一些工作，因为我们切换到标准记法，但至少 ``to_additive`` 完成了从乘法记法到加法记法的转换工作。
BOTH: -/

-- QUOTE:
@[to_additive]
lemma inv_eq_of_mul [Group₃ G] {a b : G} (h : a * b = 1) : a⁻¹ = b :=
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  left_inv_eq_right_inv' (Group₃.inv_mul a) h
-- BOTH:
-- QUOTE.

/- TEXT:
请注意，可以要求 ``to_additive`` 为一个引理添加 ``simp`` 标签，并将该属性传播到加法版本，如下所示。
BOTH: -/

-- QUOTE:
@[to_additive (attr := simp)]
lemma Group₃.mul_inv {G : Type} [Group₃ G] {a : G} : a * a⁻¹ = 1 := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  rw [← inv_mul a⁻¹, inv_eq_of_mul (inv_mul a)]
-- BOTH:

@[to_additive]
lemma mul_left_cancel₃ {G : Type} [Group₃ G] {a b c : G} (h : a * b = a * c) : b = c := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  simpa [← mul_assoc₃] using congr_arg (a⁻¹ * ·) h
-- BOTH:

@[to_additive]
lemma mul_right_cancel₃ {G : Type} [Group₃ G] {a b c : G} (h : b*a = c*a) : b = c := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  simpa [mul_assoc₃] using congr_arg (· * a⁻¹) h
-- BOTH:

class AddCommGroup₃ (G : Type) extends AddGroup₃ G, AddCommMonoid₃ G

@[to_additive AddCommGroup₃]
class CommGroup₃ (G : Type) extends Group₃ G, CommMonoid₃ G

-- QUOTE.

/- TEXT:
现在我们准备讨论环。为了演示目的，我们不会假设加法是交换的，然后立即提供一个 ``AddCommGroup₃`` 的实例。Mathlib 不会玩这种把戏，首先是因为在实践中这不会使任何环实例变得更容易，其次是因为 Mathlib 的代数层次结构通过半环进行，半环类似于环但没有相反数，因此下面的证明对它们不起作用。在这里，我们不仅收获了一个不错的实践机会（尤其是对于初次接触者而言），更能通过这一过程掌握一个实例构建的范例，其中运用了能够同时指定父结构及额外字段的语法技巧。
BOTH: -/

-- QUOTE:
class Ring₃ (R : Type) extends AddGroup₃ R, Monoid₃ R, MulZeroClass R where
  /-- Multiplication is left distributive over addition -/
  left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c
  /-- Multiplication is right distributive over addition -/
  right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c

instance {R : Type} [Ring₃ R] : AddCommGroup₃ R :=
{ Ring₃.toAddGroup₃ with
  add_comm := by
/- EXAMPLES:
    sorry }
SOLUTIONS: -/
    intro a b
    have : a + (a + b + b) = a + (b + a + b) := calc
      a + (a + b + b) = (a + a) + (b + b) := by simp [add_assoc₃, add_assoc₃]
      _ = (1 * a + 1 * a) + (1 * b + 1 * b) := by simp
      _ = (1 + 1) * a + (1 + 1) * b := by simp [Ring₃.right_distrib]
      _ = (1 + 1) * (a + b) := by simp [Ring₃.left_distrib]
      _ = 1 * (a + b) + 1 * (a + b) := by simp [Ring₃.right_distrib]
      _ = (a + b) + (a + b) := by simp
      _ = a + (b + a + b) := by simp [add_assoc₃]
    exact add_right_cancel₃ (add_left_cancel₃ this) }
-- QUOTE.
/- TEXT:
当然，我们也可以构建具体的实例，比如在整数上构建环结构（当然下面的实例利用了 Mathlib 中已经完成的所有工作）。
BOTH: -/

-- QUOTE:
instance : Ring₃ ℤ where
  add := (· + ·)
  add_assoc₃ := add_assoc
  zero := 0
  zero_add := by simp
  add_zero := by simp
  neg := (- ·)
  neg_add := by simp
  mul := (· * ·)
  mul_assoc₃ := mul_assoc
  one := 1
  one_mul := by simp
  mul_one := by simp
  zero_mul := by simp
  mul_zero := by simp
  left_distrib := Int.mul_add
  right_distrib := Int.add_mul
-- QUOTE.
/- TEXT:
作为练习，您现在可以为序关系设置一个简单的层次结构，包括一个有序交换幺半群的类，它同时具有偏序关系和交换幺半群结构，满足 ``∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b`` 。当然，您需要为以下类添加字段，可能还需要添加 ``extends`` 子句。
BOTH: -/
-- QUOTE:

class LE₁ (α : Type) where
  /-- The Less-or-Equal relation. -/
  le : α → α → Prop

@[inherit_doc] infix:50 " ≤₁ " => LE₁.le

class Preorder₁ (α : Type)
-- SOLUTIONS:
  extends LE₁ α where
  le_refl : ∀ a : α, a ≤₁ a
  le_trans : ∀ a b c : α, a ≤₁ b → b ≤₁ c → a ≤₁ c
-- BOTH:

class PartialOrder₁ (α : Type)
-- SOLUTIONS:
  extends Preorder₁ α where
  le_antisymm : ∀ a b : α, a ≤₁ b → b ≤₁ a → a = b
-- BOTH:

class OrderedCommMonoid₁ (α : Type)
-- SOLUTIONS:
  extends PartialOrder₁ α, CommMonoid₃ α where
  mul_of_le : ∀ a b : α, a ≤₁ b → ∀ c : α, c * a ≤₁ c * b
-- BOTH:

instance : OrderedCommMonoid₁ ℕ where
-- SOLUTIONS:
  le := (· ≤ ·)
  le_refl := fun _ ↦ le_rfl
  le_trans := fun _ _ _ ↦ le_trans
  le_antisymm := fun _ _ ↦ le_antisymm
  mul := (· * ·)
  mul_assoc₃ := mul_assoc
  one := 1
  one_mul := one_mul
  mul_one := mul_one
  mul_comm := mul_comm
  mul_of_le := fun _ _ h c ↦ Nat.mul_le_mul_left c h
-- QUOTE.
/- TEXT:
我们现在要讨论涉及多个类型的代数结构。最典型的例子是环上的模。如果您不知道什么是模，您可以假装它指的是向量空间，并认为我们所有的环都是域。这些结构是配备了某个环的元素的标量乘法的交换加法群。

我们首先定义由某种类型 ``α`` 在某种类型 ``β`` 上进行标量乘法的数据承载类型类，并为其赋予右结合的表示法。
BOTH: -/

-- QUOTE:
class SMul₃ (α : Type) (β : Type) where
  /-- Scalar multiplication -/
  smul : α → β → β

infixr:73 " • " => SMul₃.smul
-- QUOTE.

/- TEXT:
然后我们可以定义模（如果您不知道什么是模，可以先想想向量空间）。
BOTH: -/

-- QUOTE:
class Module₁ (R : Type) [Ring₃ R] (M : Type) [AddCommGroup₃ M] extends SMul₃ R M where
  zero_smul : ∀ m : M, (0 : R) • m = 0
  one_smul : ∀ m : M, (1 : R) • m = m
  mul_smul : ∀ (a b : R) (m : M), (a * b) • m = a • b • m
  add_smul : ∀ (a b : R) (m : M), (a + b) • m = a • m + b • m
  smul_add : ∀ (a : R) (m n : M), a • (m + n) = a • m + a • n
-- QUOTE.

/- TEXT:
这里有一些有趣的事情。虽然 ``R`` 上的环结构作为此定义的参数并不令人意外，但您可能期望 ``AddCommGroup₃ M`` 像 ``SMul₃ R M`` 一样成为 ``extends`` 子句的一部分。尝试这样做会导致一个听起来很神秘的错误消息：
``cannot find synthesization order for instance Module₁.toAddCommGroup₃ with type (R : Type) → [inst : Ring₃ R] → {M : Type} → [self : Module₁ R M] → AddCommGroup₃ M
all remaining arguments have metavariables: Ring₃ ?R @Module₁ ?R ?inst✝ M``。
要理解此消息，您需要记住，这样的 ``extends`` 子句会导致一个标记为实例的字段 ``Module₃.toAddCommGroup₃`` 。此实例具有错误消息中出现的签名：
 ``(R : Type) → [inst : Ring₃ R] → {M : Type} → [self : Module₁ R M] → AddCommGroup₃ M`` 。在类型类数据库中有这样一个实例，每次 Lean 要为某个 ``M`` 查找一个 ``AddCommGroup₃ M`` 实例时，它都需要先去寻找一个完全未指定的类型 ``R`` 以及一个 ``Ring₃ R`` 实例，然后才能开始寻找主要目标，即一个 ``Module₁ R M`` 实例。这两个支线任务在错误消息中由元变量表示，并在那里用 ``？R`` 和 ``？inst✝`` 标注。这样的一个 ``Module₃.toAddCommGroup₃`` 实例对于实例解析过程来说会是一个巨大的陷阱，因此 ``class`` 命令拒绝设置它。

那么 ``extends SMul₃ R M`` 又如何呢？它创建了一个字段
 ``Module₁.toSMul₃ : {R : Type} →  [inst : Ring₃ R] → {M : Type} → [inst_1 : AddCommGroup₃ M] → [self : Module₁ R M] → SMul₃ R M``
其最终结果 ``SMul₃ R M`` 同时提到了 ``R`` 和 ``M`` ，所以这个字段可以安全地用作实例。规则很容易记住：在 ``extends`` 子句中出现的每个类都应提及参数中出现的每个类型。

让我们创建我们的第一个模块实例：一个环自身就是一个模块，其乘法作为标量乘法。
BOTH: -/
-- QUOTE:
instance selfModule (R : Type) [Ring₃ R] : Module₁ R R where
  smul := fun r s ↦ r*s
  zero_smul := zero_mul
  one_smul := one_mul
  mul_smul := mul_assoc₃
  add_smul := Ring₃.right_distrib
  smul_add := Ring₃.left_distrib
-- QUOTE.
/- TEXT:
作为第二个例子，每个阿贝尔群都是整数环上的模块（这是推广向量空间理论以允许非可逆标量的原因之一）。首先，对于任何配备零和加法的类型，都可以定义自然数的标量乘法： ``n • a`` 定义为 ``a + ⋯ + a`` ，其中 ``a`` 出现 ``n`` 次。然后通过确保 ``(-1) • a = -a`` 将其扩展到整数的标量乘法。
BOTH: -/
-- QUOTE:

def nsmul₁ [Zero M] [Add M] : ℕ → M → M
  | 0, _ => 0
  | n + 1, a => a + nsmul₁ n a

def zsmul₁ {M : Type*} [Zero M] [Add M] [Neg M] : ℤ → M → M
  | Int.ofNat n, a => nsmul₁ n a
  | Int.negSucc n, a => -nsmul₁ n.succ a
-- QUOTE.
/- TEXT:
证明这会产生一个模块结构有点繁琐，且对当前讨论来说不那么有趣，所以我们很抱歉地略过所有公理。您**无需**用证明来替换这些抱歉。如果您坚持这样做，那么您可能需要陈述并证明关于 ``nsmul₁`` 和 ``zsmul₁`` 的几个中间引理。
BOTH: -/
-- QUOTE:

instance abGrpModule (A : Type) [AddCommGroup₃ A] : Module₁ ℤ A where
  smul := zsmul₁
  zero_smul := sorry
  one_smul := sorry
  mul_smul := sorry
  add_smul := sorry
  smul_add := sorry
-- QUOTE.
/- TEXT:
一个更为重要的问题是，我们目前对于整数环 ``ℤ`` 本身存在两种模块结构：首先，由于 ``ℤ`` 是阿贝尔群，因此可以定义其为 ``abGrpModule ℤ`` ；其次，鉴于 ``ℤ`` 作为环的性质，我们也可以将其视作 ``selfModule ℤ`` 。这两种模块结构虽然对应相同的阿贝尔群结构，但它们在标量乘法上的一致性并不显而易见。实际上，这两者确实是相同的，但这一点并非由定义直接决定，而需要通过证明来确认。这一情况对类型类实例解析过程而言无疑是个不利消息，并且可能会让使用此层次结构的用户感到颇为沮丧。当我们直接请求找到某个实例时，Lean 会自动选择一个，我们可以通过以下命令查看所选的是哪一个：
BOTH: -/
-- QUOTE:

#synth Module₁ ℤ ℤ -- abGrpModule ℤ

-- QUOTE.
/- TEXT:
但在更间接的上下文中，Lean 可能会先推断出一个实例，然后感到困惑。这种情况被称为坏菱形。这与我们上面使用的菱形运算无关，而是指从 ``ℤ`` 到其 ``Module₁ ℤ`` 的路径，可以通过 ``AddCommGroup₃ ℤ`` 或 ``Ring₃ ℤ`` 中的任意一个到达。

重要的是要明白，并非所有的菱形结构都是不好的。实际上，在 Mathlib 中以及本章中到处都有菱形结构。在最开始的时候我们就看到，可以从 ``Monoid₁ α`` 通过 ``Semigroup₁ α`` 或者 ``DiaOneClass₁ α`` 到达 ``Dia₁ α`` ，并且由于 ``class`` 命令所做的工作，这两个 ``Dia₁ α`` 实例在定义上是相等的。特别是，底部为 ``Prop`` 值类的菱形结构不可能是不好的，因为对同一陈述的任何两个证明在定义上都是相等的。

但是我们用模块创建的菱形肯定是有问题的。问题出在 ``smul`` 字段上，它是数据而非证明，并且我们有两个构造在定义上并不相等。解决这个问题的稳健方法是确保从丰富结构到贫乏结构的转换总是通过遗忘数据来实现，而不是通过定义数据。这种众所周知的模式被称为“遗忘继承”，在 https://inria.hal.science/hal-02463336 中有大量讨论。

在我们的具体案例中，我们可以修改 ``AddMonoid₃`` 的定义，以包含一个 ``nsmul`` 数据字段以及一些值为 ``Prop`` 类型的字段，以确保此操作确实是我们在上面构造的那个。在下面的定义中，这些字段在其类型后面使用 ``:=`` 给出了默认值。由于这些默认值的存在，大多数实例的构造方式与我们之前的定义完全相同。但在 ``ℤ`` 的特殊情况下，我们将能够提供特定的值。
BOTH: -/
-- QUOTE:

class AddMonoid₄ (M : Type) extends AddSemigroup₃ M, AddZeroClass M where
  /-- Multiplication by a natural number. -/
  nsmul : ℕ → M → M := nsmul₁
  /-- Multiplication by `(0 : ℕ)` gives `0`. -/
  nsmul_zero : ∀ x, nsmul 0 x = 0 := by intros; rfl
  /-- Multiplication by `(n + 1 : ℕ)` behaves as expected. -/
  nsmul_succ : ∀ (n : ℕ) (x), nsmul (n + 1) x = x + nsmul n x := by intros; rfl

instance mySMul {M : Type} [AddMonoid₄ M] : SMul ℕ M := ⟨AddMonoid₄.nsmul⟩
-- QUOTE.
/- TEXT:
让我们检查一下，即使不提供与 ``nsmul`` 相关的字段，我们是否仍能构造一个乘积单群实例。
BOTH: -/
-- QUOTE:

instance (M N : Type) [AddMonoid₄ M] [AddMonoid₄ N] : AddMonoid₄ (M × N) where
  add := fun p q ↦ (p.1 + q.1, p.2 + q.2)
  add_assoc₃ := fun a b c ↦ by ext <;> apply add_assoc₃
  zero := (0, 0)
  zero_add := fun a ↦ by ext <;> apply zero_add
  add_zero := fun a ↦ by ext <;> apply add_zero
-- QUOTE.
/- TEXT:
现在让我们处理 ``ℤ`` 的特殊情况，在这种情况下，我们希望使用从 ``ℕ`` 到 ``ℤ`` 的强制转换以及 ``ℤ`` 上的乘法来构建 ``nsmul`` 。请注意，特别是证明字段包含的工作比上面的默认值要多。
BOTH: -/
-- QUOTE:

instance : AddMonoid₄ ℤ where
  add := (· + ·)
  add_assoc₃ := Int.add_assoc
  zero := 0
  zero_add := Int.zero_add
  add_zero := Int.add_zero
  nsmul := fun n m ↦ (n : ℤ) * m
  nsmul_zero := Int.zero_mul
  nsmul_succ := fun n m ↦ show (n + 1 : ℤ) * m = m + n * m
    by rw [Int.add_mul, Int.add_comm, Int.one_mul]
-- QUOTE.
/- TEXT:
让我们检查一下我们是否解决了问题。因为 Lean 已经有一个自然数和整数的标量乘法定义，而我们希望确保使用我们的实例，所以我们不会使用 ``•`` 符号，而是调用 ``SMul.mul`` 并明确提供上面定义的实例。
BOTH: -/
-- QUOTE:

example (n : ℕ) (m : ℤ) : SMul.smul (self := mySMul) n m = n * m := rfl
-- QUOTE.
/- TEXT:
接下来的故事中，会在群的定义中加入一个 ``zsmul`` 字段，并采用类似的技巧。现在您已经准备好阅读 Mathlib 中关于幺半群、群、环和模的定义了。它们比我们在这里看到的要复杂，因为它们属于一个庞大的层级结构，但上面已经解释了所有原则。

作为练习，您可以回到上面构建的序关系层次结构，并尝试引入一个携带“小于”符号 `<₁` 的类型类 `LT₁`，并确保每个预序都带有一个 `<₁`，其默认值由 `≤₁` 构建，并且有一个 `Prop` 值字段，断言这两个比较运算符之间的自然关系。
-/

-- SOLUTIONS:

class LT₁ (α : Type) where
  /-- The Less-Than relation -/
  lt : α → α → Prop

@[inherit_doc] infix:50 " <₁ " => LT₁.lt

class PreOrder₂ (α : Type) extends LE₁ α, LT₁ α where
  le_refl : ∀ a : α, a ≤₁ a
  le_trans : ∀ a b c : α, a ≤₁ b → b ≤₁ c → a ≤₁ c
  lt := fun a b ↦ a ≤₁ b ∧ ¬b ≤₁ a
  lt_iff_le_not_le : ∀ a b : α, a <₁ b ↔ a ≤₁ b ∧ ¬b ≤₁ a := by intros; rfl
