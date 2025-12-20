-- BOTH:
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Prime.Basic
import MIL.Common

/- TEXT:
.. _sets:

集合
----

.. index:: set operations

设 ``α`` 是任意类型，则类型 ``Set α`` 是 ``α`` 中的元素组成的集合。这一类型支持常规的集合论运算和关系。例如， ``s ⊆ t`` 表示 ``s`` 是 ``t`` 的子集（ ``⊆`` 符号是 ``\ss`` 或 ``\sub``），``s ∩ t`` 指交集（ ``\i`` 或 ``\cap`` ）， ``s ∪ t`` 指并集（ ``\un`` 或 ``\cup`` ）。库中也定义了集合 ``univ``, 它包含类型 ``α`` 的全部元素，以及空集 ``∅`` （ ``\empty`` ）。给定 ``x : α`` 和 ``s : Set α``, ``x ∈ s`` 表示 ``x`` 属于 ``s`` （ ``\in`` 或 ``\mem`` ，涉及集合成员关系的定理的名字经常含有 ``mem``）。 ``x ∉ s`` （ ``\notin`` ）是 ``¬ x ∈ s`` 的缩写。

.. index:: simp, tactics ; simp

证明关于集合的命题的一种方法是使用 ``rw`` 或 ``simp`` 来展开定义。在下面的第二个例子中，我们使用 ``simp only`` 告诉化简器只使用我们提供的列表中的等式，而不是整个数据库中的等式。不同于 ``rw``, ``simp`` 可以在全称或存在量词内实施化简。
TEXT. -/
-- BOTH:
section
-- QUOTE:
variable {α : Type*}
variable (s t u : Set α)
open Set

-- EXAMPLES:
example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rw [subset_def, inter_def, inter_def]
  rw [subset_def] at h
  simp only [mem_setOf]
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  simp only [subset_def, mem_inter_iff] at *
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩
-- QUOTE.

/- TEXT:
本例中，我们打开了 ``Set`` 命名空间以用更短的定理名访问定理。事实上，我们完全可以不用 ``rw`` 和 ``simp`` ：
TEXT. -/
-- QUOTE:
example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  intro x xsu
  exact ⟨h xsu.1, xsu.2⟩
-- QUOTE.

/- TEXT:
这叫做 **定义规约（definitional reduction）** ：为了理解 ``intro`` 命令和匿名构造子，Lean 不得不展开定义。下面的例子也说明了这一现象：
TEXT. -/
-- QUOTE:
example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
  fun x ⟨xs, xu⟩ ↦ ⟨h xs, xu⟩
-- QUOTE.

/- TEXT:
为了处理并集，我们可以使用 ``Set.union_def`` 和 ``Set.mem_union`` 。由于 ``x ∈ s ∪ t`` 展开为 ``x ∈ s ∨ x ∈ t``, 我们也可以使用 ``cases`` 策略强制要求定义规约。
TEXT. -/
-- QUOTE:
example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  intro x hx
  have xs : x ∈ s := hx.1
  have xtu : x ∈ t ∪ u := hx.2
  rcases xtu with xt | xu
  · left
    show x ∈ s ∩ t
    exact ⟨xs, xt⟩
  · right
    show x ∈ s ∩ u
    exact ⟨xs, xu⟩
-- QUOTE.

/- TEXT:
交集比并集优先级更高，表达式 ``(s ∩ t) ∪ (s ∩ u)`` 中不必需使用括号，但使用括号会更易读。下面是更简短的证明。使用 ``rintro`` 时，有时我们需要使用括号包围析取模式 ``h1 | h2`` 使得 Lean 能正确解析它。
TEXT. -/
-- QUOTE:
example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  rintro x ⟨xs, xt | xu⟩
  · left; exact ⟨xs, xt⟩
  · right; exact ⟨xs, xu⟩
-- QUOTE.

/- TEXT:
作为练习，试着证明反向的包含关系：
BOTH: -/
-- QUOTE:
example : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  rintro x (⟨xs, xt⟩ | ⟨xs, xu⟩)
  · use xs; left; exact xt
  · use xs; right; exact xu
-- QUOTE.

-- BOTH:
/- TEXT:
库里也定义了差集 ``s \ t`` （反斜线以 ``\\`` 输入）。表达式 ``x ∈ s \ t`` 展开为 ``x ∈ s ∧ x ∉ t`` 。可以使用 ``Set.diff_eq`` 和 ``dsimp`` 或 ``Set.mem_diff`` 手动重写它，而下面的两个证明展示了这一点和更简洁的方案。
TEXT. -/
-- QUOTE:
example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  intro x xstu
  have xs : x ∈ s := xstu.1.1
  have xnt : x ∉ t := xstu.1.2
  have xnu : x ∉ u := xstu.2
  constructor
  · exact xs
  intro xtu
  -- x ∈ t ∨ x ∈ u
  rcases xtu with xt | xu
  · show False; exact xnt xt
  · show False; exact xnu xu

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  rintro x ⟨⟨xs, xnt⟩, xnu⟩
  use xs
  rintro (xt | xu) <;> contradiction
-- QUOTE.

/- TEXT:
作为练习，证明反向的包含关系：
BOTH: -/
-- QUOTE:
example : s \ (t ∪ u) ⊆ (s \ t) \ u := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  rintro x ⟨xs, xntu⟩
  constructor
  use xs
  · intro xt
    exact xntu (Or.inl xt)
  intro xu
  apply xntu (Or.inr xu)
-- QUOTE.

-- BOTH:
/- TEXT:
要证明两个集合相等，只需证明任一集合中的每个元素都是另一个集合中的元素。这个原理称为“外延性”， ``ext`` 策略可以用于处理它。
TEXT. -/
-- QUOTE:
example : s ∩ t = t ∩ s := by
  ext x
  simp only [mem_inter_iff]
  constructor
  · rintro ⟨xs, xt⟩; exact ⟨xt, xs⟩
  · rintro ⟨xt, xs⟩; exact ⟨xs, xt⟩
-- QUOTE.

/- TEXT:
删除 ``simp only [mem_inter_iff]`` 一行并不会影响证明。下面的单行证明更简洁但难读：
TEXT. -/
-- QUOTE:
example : s ∩ t = t ∩ s :=
  Set.ext fun x ↦ ⟨fun ⟨xs, xt⟩ ↦ ⟨xt, xs⟩, fun ⟨xt, xs⟩ ↦ ⟨xs, xt⟩⟩
-- QUOTE.

/- TEXT:
甚至还能更短：
TEXT. -/
-- QUOTE:
example : s ∩ t = t ∩ s := by ext x; simp [and_comm]
-- QUOTE.

/- TEXT:
除了使用 ``ext`` 之外，我们还可以使用 ``Subset.antisymm`` 这个定理，它可以通过证明 ``s ⊆ t`` 和 ``t ⊆ s`` 来证明集合间的等式 ``s = t`` 。
TEXT. -/
-- QUOTE:
example : s ∩ t = t ∩ s := by
  apply Subset.antisymm
  · rintro x ⟨xs, xt⟩; exact ⟨xt, xs⟩
  · rintro x ⟨xt, xs⟩; exact ⟨xs, xt⟩
-- QUOTE.

/- TEXT:
练习：
BOTH: -/
-- QUOTE:
example : s ∩ t = t ∩ s :=
/- EXAMPLES:
    Subset.antisymm sorry sorry
SOLUTIONS: -/
    Subset.antisymm
    (fun x ⟨xs, xt⟩ ↦ ⟨xt, xs⟩) fun x ⟨xt, xs⟩ ↦ ⟨xs, xt⟩
-- QUOTE.

-- BOTH:
/- TEXT:
技巧：你可以用下划线代替 ``sorry`` ，并将鼠标悬停在它上面，Lean 会向你显示它在这一位置的预期。

下面是一些你可能会喜欢的集合论性质：
TEXT. -/
-- QUOTE:
example : s ∩ (s ∪ t) = s := by
  sorry

example : s ∪ s ∩ t = s := by
  sorry

example : s \ t ∪ t = s ∪ t := by
  sorry

example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example : s ∩ (s ∪ t) = s := by
  ext x; constructor
  · rintro ⟨xs, _⟩
    exact xs
  · intro xs
    use xs; left; exact xs

example : s ∪ s ∩ t = s := by
  ext x; constructor
  · rintro (xs | ⟨xs, xt⟩) <;> exact xs
  · intro xs; left; exact xs

example : s \ t ∪ t = s ∪ t := by
  ext x; constructor
  · rintro (⟨xs, nxt⟩ | xt)
    · left
      exact xs
    · right
      exact xt
  by_cases h : x ∈ t
  · intro
    right
    exact h
  rintro (xs | xt)
  · left
    use xs
  right; exact xt

example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  ext x; constructor
  · rintro (⟨xs, xnt⟩ | ⟨xt, xns⟩)
    · constructor
      left
      exact xs
      rintro ⟨_, xt⟩
      contradiction
    · constructor
      right
      exact xt
      rintro ⟨xs, _⟩
      contradiction
  rintro ⟨xs | xt, nxst⟩
  · left
    use xs
    intro xt
    apply nxst
    constructor <;> assumption
  · right; use xt; intro xs
    apply nxst
    constructor <;> assumption

/- TEXT:
说到集合的表示，下面就为大家揭秘背后的机制。在类型论中，类型 ``α`` 上的 **性质** 或 **谓词** 只是一个函数 ``P : α → Prop`` 。这是有意义的：给定 ``a : α``, ``P a`` 就是 ``P`` 对 ``a`` 成立这一命题。在库中， ``Set α`` 定义为 ``α → Prop`` 而 ``x ∈ s`` 定义为 ``s x`` 。换句话说，集合实际上就是性质，只是被当成对象。

库中也定义了集合构造器的符号。表达式 ``{ y | P y }`` 展开就是 ``(fun y ↦ P y)`` 。因此 ``x ∈ { y | P y }`` 规约为 ``P x`` 。因此我们可以把偶数性质转化为偶数集合：
TEXT. -/
-- QUOTE:
def evens : Set ℕ :=
  { n | Even n }

def odds : Set ℕ :=
  { n | ¬Even n }

example : evens ∪ odds = univ := by
  rw [evens, odds]
  ext n
  simp [-Nat.not_even_iff_odd]
  apply Classical.em
-- QUOTE.

/- TEXT:
你最好能一句一句看看这个证明，并确保你理解你了解发生了什么。
注意到我们告诉化简器 **不要** 使用引理 ``Nat.not_even_iff``
因为我们希望将 ``¬ Even n`` 保留在我们的目标中
尝试删除 ``rw [evens, odds]`` 这一行，证明仍然成立。

事实上，集合构造器符号定义

- ``s ∩ t`` 为 ``{x | x ∈ s ∧ x ∈ t}``
- ``s ∪ t`` 为 ``{x | x ∈ s ∨ x ∈ t}``
- ``∅`` 为 ``{x | False}``
- ``univ`` 为 ``{x | True}``

我们经常需要精确指定 ``∅`` 和 ``univ`` 的类型，因为 Lean 很难猜出我们指的是哪种类型。下面的例子演示了当需要的时候 Lean 如何展开最后两个定义。在第二个例子中，``trivial`` 是库中对 ``True`` 的标准证明。
TEXT. -/
-- QUOTE:
example (x : ℕ) (h : x ∈ (∅ : Set ℕ)) : False :=
  h

example (x : ℕ) : x ∈ (univ : Set ℕ) :=
  trivial
-- QUOTE.

/- TEXT:
作为练习，证明下列包含关系。使用 ``intro n`` 以展开子集定义，使用 ``simp`` 把集合论构造约化为逻辑。我们也推荐使用定理 ``Nat.Prime.eq_two_or_odd`` 和 ``Nat.even_iff`` 。
TEXT. -/
-- QUOTE:
example : { n | Nat.Prime n } ∩ { n | n > 2 } ⊆ { n | ¬Even n } := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example : { n | Nat.Prime n } ∩ { n | n > 2 } ⊆ { n | ¬Even n } := by
  intro n
  simp
  intro nprime n_gt
  rcases Nat.Prime.eq_two_or_odd nprime with h | h
  · rw [h]
    linarith
  · rw [Nat.odd_iff, h]

/- TEXT:
有点令人困惑的是，库中有多个版本的谓词 ``Prime`` 。最通用的谓词对任何有零元素的交换幺半群都有意义。谓词 ``Nat.Prime`` 是针对自然数的。幸运的是，有一个定理指出，在特定情况下这两个概念是一致的，所以你总是可以把一个谓词改写成另一个谓词。
TEXT. -/
-- QUOTE:
#print Prime

#print Nat.Prime

example (n : ℕ) : Prime n ↔ Nat.Prime n :=
  Nat.prime_iff.symm

example (n : ℕ) (h : Prime n) : Nat.Prime n := by
  rw [Nat.prime_iff]
  exact h
-- QUOTE.

/- TEXT:
.. index:: rwa, tactics ; rwa

``rwa`` 策略是在 ``rw`` 后跟着一个 ``assumption`` 策略。
TEXT. -/
-- QUOTE:
example (n : ℕ) (h : Prime n) : Nat.Prime n := by
  rwa [Nat.prime_iff]
-- QUOTE.

-- BOTH:
end

/- TEXT:
.. index:: bounded quantifiers

Lean 引入了记号 ``∀ x ∈ s, ...``, 等价于 ``∀ x, x ∈ s → ...`` ，类似地也引入了 ``∃ x ∈ s, ...,`` 。有时它们被称为 **约束量词（bounded quantifier）** ，因为这种构造将 ``x`` 的意义约束在集合 ``s`` 内。因此，库中使用这些量词的定理通常在名称中包含 ``ball`` 或 ``bex`` 。定理 ``bex_def`` 断言 ``∃ x ∈ s, ...`` 等价于 ``∃ x, x ∈ s ∧ ...,`` ，但当它们和 ``rintro``, ``use`` 以及匿名构造子一起使用时，这两种量词表达式的行为大致相同。因此，我们通常不需要使用 ``bex_def`` 来精确转换它们。用例：
TEXT. -/
-- BOTH:
section

-- QUOTE:
variable (s t : Set ℕ)

-- EXAMPLES:
example (h₀ : ∀ x ∈ s, ¬Even x) (h₁ : ∀ x ∈ s, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  intro x xs
  constructor
  · apply h₀ x xs
  apply h₁ x xs

example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ s, Prime x := by
  rcases h with ⟨x, xs, _, prime_x⟩
  use x, xs
-- QUOTE.

/- TEXT:
尝试下这些略有不同的命题：
TEXT. -/
-- QUOTE:
section
variable (ssubt : s ⊆ t)

example (h₀ : ∀ x ∈ t, ¬Even x) (h₁ : ∀ x ∈ t, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  sorry

example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ t, Prime x := by
  sorry

end
-- QUOTE.

-- SOLUTIONS:
section
variable (ssubt : s ⊆ t)

example (h₀ : ∀ x ∈ t, ¬Even x) (h₁ : ∀ x ∈ t, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  intro x xs
  constructor
  · apply h₀ x (ssubt xs)
  apply h₁ x (ssubt xs)

example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ t, Prime x := by
  rcases h with ⟨x, xs, _, px⟩
  use x, ssubt xs

end

-- BOTH:
end

/- TEXT:
带下标的并集和交集是另一种重要的集合论构造。我们可以把 ``α`` 中的元素组成的集合的序列 :math:`A_0, A_1, A_2, \ldots` 建模为函数 ``A : ℕ → Set α`` ，此时 ``⋃ i, A i`` 表示它们的并集，而 ``⋂ i, A i`` 表示它们的交集。这里自然数没有什么特别之处，因此 ``ℕ`` 可以替换为任意作为指标集的类型 ``I``。下面说明它们的用法。
TEXT. -/
-- BOTH:
section
-- QUOTE:
variable {α I : Type*}
variable (A B : I → Set α)
variable (s : Set α)

open Set

-- EXAMPLES:
example : (s ∩ ⋃ i, A i) = ⋃ i, A i ∩ s := by
  ext x
  simp only [mem_inter_iff, mem_iUnion]
  constructor
  · rintro ⟨xs, ⟨i, xAi⟩⟩
    exact ⟨i, xAi, xs⟩
  rintro ⟨i, xAi, xs⟩
  exact ⟨xs, ⟨i, xAi⟩⟩

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i := by
  ext x
  simp only [mem_inter_iff, mem_iInter]
  constructor
  · intro h
    constructor
    · intro i
      exact (h i).1
    intro i
    exact (h i).2
  rintro ⟨h1, h2⟩ i
  constructor
  · exact h1 i
  exact h2 i
-- QUOTE.

/- TEXT:
带下标的并集或交集通常需要使用括号，因为与量词一样，绑定变量的范围会尽可能地扩展。

尝试证明下列恒等式。其中一个方向需要经典逻辑！我们建议在证明的适当位置使用 ``by_cases xs : x ∈ s`` 。
TEXT. -/
-- QUOTE:

example : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by
  ext x
  simp only [mem_union, mem_iInter]
  constructor
  · rintro (xs | xI)
    · intro i
      right
      exact xs
    intro i
    left
    exact xI i
  intro h
  by_cases xs : x ∈ s
  · left
    exact xs
  right
  intro i
  cases h i
  · assumption
  contradiction

/- TEXT:
Mathlib 也支持在自定义的下标集中做并集和交集，类似于约束量词。你可以使用 ``mem_iUnion₂`` 和 ``mem_iInter₂`` 解包它们的含义。正如下面的示例所示，Lean 的化简器也可以执行这些替换。
TEXT. -/
-- QUOTE:
-- BOTH:
def primes : Set ℕ :=
  { x | Nat.Prime x }

-- EXAMPLES:
example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } :=by
  ext
  rw [mem_iUnion₂]
  simp

example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } := by
  ext
  simp

example : (⋂ p ∈ primes, { x | ¬p ∣ x }) ⊆ { x | x = 1 } := by
  intro x
  contrapose!
  simp
  apply Nat.exists_prime_and_dvd
-- QUOTE.

/- TEXT:
试着解决下面这个类似的例子。如果你开始输入 ``eq_univ`` ，标签补全器会告诉你 ``apply eq_univ_of_forall`` 是开始证明的好方法。另外推荐使用 ``Nat.exists_infinite_primes`` 定理。
TEXT. -/
-- QUOTE:
example : (⋃ p ∈ primes, { x | x ≤ p }) = univ := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example : (⋃ p ∈ primes, { x | x ≤ p }) = univ := by
  apply eq_univ_of_forall
  intro x
  simp
  rcases Nat.exists_infinite_primes x with ⟨p, pge, primep⟩
  use p, primep

-- BOTH:
end

/- TEXT:
给定一组集合 ``s : Set (Set α)`` ，它们的并集 ``⋃₀ s`` 具有类型 ``Set α`` ，定义为 ``{x | ∃ t ∈ s, x ∈ t}`` 。类似地，它们的交集 ``⋂₀ s`` 定义为 ``{x | ∀ t ∈ s, x ∈ t}`` 。这些运算分别称为 ``sUnion`` 和 ``sInter`` 。下面的例子展示了它们与下标集合上并集和交集的关系，在库中它们称为 ``sUnion_eq_biUnion`` 和 ``sInter_eq_biInter`` 。
TEXT. -/
section

open Set

-- QUOTE:
variable {α : Type*} (s : Set (Set α))

example : ⋃₀ s = ⋃ t ∈ s, t := by
  ext x
  rw [mem_iUnion₂]
  simp

example : ⋂₀ s = ⋂ t ∈ s, t := by
  ext x
  rw [mem_iInter₂]
  rfl
-- QUOTE.

end
