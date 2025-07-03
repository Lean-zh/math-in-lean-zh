import Mathlib.Data.Fintype.BigOperators
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Tactic

/- TEXT:
.. _counting_arguments:

计数论证
------------------

计数的艺术是组合学的核心部分。
Mathlib 包含了几个用于计数有限集合元素的基本恒等式：
BOTH: -/
-- QUOTE:
open Finset

-- EXAMPLES:
variable {α β : Type*} [DecidableEq α] [DecidableEq β] (s t : Finset α) (f : α → β)

example : #(s ×ˢ t) = #s * #t := by rw [card_product]
example : #(s ×ˢ t) = #s * #t := by simp

example : #(s ∪ t) = #s + #t - #(s ∩ t) := by rw [card_union]

example (h : Disjoint s t) : #(s ∪ t) = #s + #t := by rw [card_union_of_disjoint h]
example (h : Disjoint s t) : #(s ∪ t) = #s + #t := by simp [h]

example (h : Function.Injective f) : #(s.image f) = #s := by rw [card_image_of_injective _ h]

example (h : Set.InjOn f s) : #(s.image f) = #s := by rw [card_image_of_injOn h]
-- QUOTE.

/- TEXT:
打开 ``Finset`` 命名空间允许我们使用记法 ``#s`` 表示 ``s.card``，
以及使用简化的名称如 `card_union` 等。

Mathlib 也可以计数有限类型的元素：
EXAMPLES: -/
section
-- QUOTE:
open Fintype

variable {α β : Type*} [Fintype α] [Fintype β]

example : card (α × β) = card α * card β := by simp

example : card (α ⊕ β) = card α + card β := by simp

example (n : ℕ) : card (Fin n → α) = (card α)^n := by simp

variable {n : ℕ} {γ : Fin n → Type*} [∀ i, Fintype (γ i)]

example : card ((i : Fin n) → γ i) = ∏ i, card (γ i) := by simp

example : card (Σ i, γ i) = ∑ i, card (γ i) := by simp
-- QUOTE.

end

/- TEXT:
当 ``Fintype`` 命名空间未打开时，我们必须使用 ``Fintype.card`` 而不是 `card`。

以下是计算有限集合基数的例子，即 `range n` 与 `range n` 的一个副本（已向右偏移超过 `n`）的并集。
这个计算需要证明并集中的两个集合是不相交的；
证明的第一行产生了副条件 ``Disjoint (range n) (image (fun i ↦ m + i) (range n))``，
这在证明的末尾得到了建立。
``Disjoint`` 谓词过于一般，无法直接对我们有用，但定理 ``disjoint_iff_ne``
将它转换为我们可以使用的形式。
EXAMPLES: -/
-- QUOTE:
#check Disjoint

example (m n : ℕ) (h : m ≥ n) :
    card (range n ∪ (range n).image (fun i ↦ m + i)) = 2 * n := by
  rw [card_union_of_disjoint, card_range, card_image_of_injective, card_range]; omega
  . apply add_right_injective
  . simp [disjoint_iff_ne]; omega
-- QUOTE.

/- TEXT:
在这一节中，``omega`` 将是我们处理算术计算和不等式的主力工具。

这里有一个更有趣的例子。考虑 :math:`\{0, \ldots, n\} \times \{0, \ldots, n\}` 的子集，
它由满足 :math:`i < j` 的对 :math:`(i, j)` 组成。如果你将这些看作坐标平面中的格点，
它们构成了顶点为 :math:`(0, 0)` 和 :math:`(n, n)` 的正方形的上三角形，
不包括对角线。完整正方形的基数是 :math:`(n + 1)^2`，去掉对角线的大小并将结果减半，
显示三角形的基数是 :math:`n (n + 1) / 2`。

或者，我们注意到三角形的行的大小是 :math:`0, 1, \ldots, n`，
所以基数是前 :math:`n` 个自然数的和。下面证明的第一个 ``have``
将三角形描述为行的并集，其中第 :math:`j` 行由与 :math:`j` 配对的数字 :math:`0, 1, ..., j - 1` 组成。
在下面的证明中，记法 ``(., j)`` 缩写了函数 ``fun i ↦ (i, j)``。
证明的其余部分只是有限集合基数的计算。
BOTH: -/
-- QUOTE:
def triangle (n : ℕ) : Finset (ℕ × ℕ) := {p ∈ range (n+1) ×ˢ range (n+1) | p.1 < p.2}

-- EXAMPLES:
example (n : ℕ) : #(triangle n) = (n + 1) * n / 2 := by
  have : triangle n = (range (n+1)).biUnion (fun j ↦ (range j).image (., j)) := by
    ext p
    simp only [triangle, mem_filter, mem_product, mem_range, mem_biUnion, mem_image]
    constructor
    . rintro ⟨⟨hp1, hp2⟩, hp3⟩
      use p.2, hp2, p.1, hp3
    . rintro ⟨p1, hp1, p2, hp2, rfl⟩
      omega
  rw [this, card_biUnion]; swap
  · -- take care of disjointness first
    intro x _ y _ xney
    simp [disjoint_iff_ne, xney]
  -- continue the calculation
  transitivity (∑ i ∈ range (n + 1), i)
  · congr; ext i
    rw [card_image_of_injective, card_range]
    intros i1 i2; simp
  rw [sum_range_id]; rfl
-- QUOTE.

/- TEXT:
下面的证明变体使用有限类型而不是有限集合进行计算。
类型 ``α ≃ β`` 是 ``α`` 和 ``β`` 之间的等价类型，
由正向映射、反向映射以及证明这两个映射互为逆映射的证明组成。
证明中的第一个 ``have`` 显示 ``triangle n`` 等价于 ``Fin i`` 的不相交并集，
其中 ``i`` 在 ``Fin (n + 1)`` 上变化。有趣的是，正向函数和反向函数是用策略构造的，
而不是显式写出的。由于它们只是移动数据和信息，``rfl`` 建立了它们是互逆的。

之后，``rw [←Fintype.card_coe]`` 将 ``#(triangle n)`` 重写为子类型
``{ x // x ∈ triangle n }`` 的基数，证明的其余部分是计算。
EXAMPLES: -/
-- QUOTE:
example (n : ℕ) : #(triangle n) = (n + 1) * n / 2 := by
  have : triangle n ≃ Σ i : Fin (n + 1), Fin i.val :=
    { toFun := by
        rintro ⟨⟨i, j⟩, hp⟩
        simp [triangle] at hp
        exact ⟨⟨j, hp.1.2⟩, ⟨i, hp.2⟩⟩
      invFun := by
        rintro ⟨i, j⟩
        use ⟨j, i⟩
        simp [triangle]
        exact j.isLt.trans i.isLt
      left_inv := by intro i; rfl
      right_inv := by intro i; rfl }
  rw [←Fintype.card_coe]
  trans; apply (Fintype.card_congr this)
  rw [Fintype.card_sigma, sum_fin_eq_sum_range]
  convert Finset.sum_range_id (n + 1)
  simp_all
-- QUOTE.

/- TEXT:
这里是另一种方法。下面证明的第一行将问题简化为证明 ``2 * #(triangle n) = (n + 1) * n``。
我们可以通过证明三角形的两个副本恰好填充矩形 ``range n ×ˢ range (n + 1)`` 来做到这一点。
作为练习，看看你能否填写计算的步骤。
在解答中，我们在倒数第二步中广泛依赖 ``omega``，
但不幸的是，我们必须手动完成相当多的工作。
BOTH: -/
-- QUOTE:
example (n : ℕ) : #(triangle n) = (n + 1) * n / 2 := by
  apply Nat.eq_div_of_mul_eq_right (by norm_num)
  let turn (p : ℕ × ℕ) : ℕ × ℕ := (n - 1 - p.1, n - p.2)
  calc 2 * #(triangle n)
      = #(triangle n) + #(triangle n) := by
-- EXAMPLES:
          sorry
/- SOLUTIONS:
          ring
BOTH: -/
    _ = #(triangle n) + #(triangle n |>.image turn) := by
-- EXAMPLES:
          sorry
/- SOLUTIONS:
          rw [Finset.card_image_of_injOn]
          rintro ⟨p1, p2⟩ hp ⟨q1, q2⟩ hq; simp [turn]
          simp_all [triangle]; omega
BOTH: -/
    _ = #(range n ×ˢ range (n + 1)) := by
-- EXAMPLES:
          sorry
/- SOLUTIONS:
          rw [←Finset.card_union_of_disjoint]; swap
          . rw [Finset.disjoint_iff_ne]
            rintro ⟨p1, p2⟩ hp ⟨q1, q2⟩ hq; simp [turn] at *
            simp_all [triangle]; omega
          congr; ext p; rcases p with ⟨p1, p2⟩
          simp [triangle, turn]
          constructor
          . rintro (h | h) <;> omega
          rcases Nat.lt_or_ge p1 p2 with h | h
          . omega
          . intro h'
            right
            use n - 1 - p1, n - p2
            omega
BOTH: -/
    _ = (n + 1) * n := by
-- EXAMPLES:
          sorry
/- SOLUTIONS:
          simp [mul_comm]
BOTH: -/
-- QUOTE.

/- TEXT:
你可以说服自己，如果我们将 ``triangle`` 定义中的 ``n`` 替换为 ``n + 1``，
将 ``<`` 替换为 ``≤``，我们会得到同样的三角形，只是向下平移了。
下面的练习要求你使用这个事实来证明两个三角形有相同的大小。
BOTH: -/
-- QUOTE:
def triangle' (n : ℕ) : Finset (ℕ × ℕ) := {p ∈ range n ×ˢ range n | p.1 ≤ p.2}

-- EXAMPLES:
example (n : ℕ) : #(triangle' n) = #(triangle n) := by sorry
/- SOLUTIONS:
example (n : ℕ) : #(triangle' n) = #(triangle n) := by
  let f (p : ℕ × ℕ) : ℕ × ℕ := (p.1, p.2 + 1)
  have : triangle n = (triangle' n |>.image f) := by
    ext p; rcases p with ⟨p1, p2⟩
    simp [triangle, triangle', f]
    constructor
    . intro h
      use p1, p2 - 1
      omega
    . simp; omega
  rw [this, card_image_of_injOn]
  rintro ⟨p1, p2⟩ hp ⟨q1, q2⟩ hq; simp [f] at *
BOTH: -/
-- QUOTE.

/- TEXT:
让我们用一个来自 Bhavik Mehta 在 2023 年 *Lean for the Curious Mathematician* 上
`关于组合学的教程 <https://www.youtube.com/watch?v=_cJctOIXWE4&list=PLlF-CfQhukNn7xEbfL38eLgkveyk9_myQ&index=8&t=2737s&ab_channel=leanprovercommunity>`_ 中的一个例子和一个练习来结束这一节。
假设我们有一个二部图，顶点集为 ``s`` 和 ``t``，使得对于 ``s`` 中的每个 ``a``，
至少有三条边离开 ``a``，对于 ``t`` 中的每个 ``b``，最多有一条边进入 ``b``。
那么图中的边的总数至少是 ``s`` 的基数的三倍，最多是 ``t`` 的基数，
由此可得 ``s`` 的基数的三倍最多是 ``t`` 的基数。
下面的定理实现了这个论证，其中我们使用关系 ``r`` 来表示图的边。
证明是一个优雅的计算。
EXAMPLES: -/
section
-- QUOTE:
open Classical
variable (s t : Finset Nat) (a b : Nat)

theorem doubleCounting {α β : Type*} (s : Finset α) (t : Finset β)
    (r : α → β → Prop)
    (h_left : ∀ a ∈ s, 3 ≤ #{b ∈ t | r a b})
    (h_right : ∀ b ∈ t, #{a ∈ s | r a b} ≤ 1) :
    3 * #(s) ≤ #(t) := by
  calc 3 * #(s)
      = ∑ a ∈ s, 3                               := by simp [sum_const_nat, mul_comm]
    _ ≤ ∑ a ∈ s, #({b ∈ t | r a b})              := sum_le_sum h_left
    _ = ∑ a ∈ s, ∑ b ∈ t, if r a b then 1 else 0 := by simp
    _ = ∑ b ∈ t, ∑ a ∈ s, if r a b then 1 else 0 := sum_comm
    _ = ∑ b ∈ t, #({a ∈ s | r a b})              := by simp
    _ ≤ ∑ b ∈ t, 1                               := sum_le_sum h_right
    _ ≤ #(t)                                     := by simp
-- QUOTE.

/- TEXT:
下面的练习也取自 Mehta 的教程。假设 ``A`` 是 ``range (2 * n)`` 的一个有 ``n + 1`` 个元素的子集。
很容易看出 ``A`` 必须包含两个连续的整数，因此包含两个互质的元素。
如果你观看教程，你会看到花费了相当大的努力来建立以下事实，
现在 ``omega`` 可以自动证明。
EXAMPLES: -/
-- QUOTE:
example (m k : ℕ) (h : m ≠ k) (h' : m / 2 = k / 2) : m = k + 1 ∨ k = m + 1 := by omega
-- QUOTE.

/- TEXT:
Mehta 练习的解答使用了鸽笼原理，以 ``exists_lt_card_fiber_of_mul_lt_card_of_maps_to`` 的形式，
来证明 ``A`` 中存在两个不同的元素 ``m`` 和 ``k`` 使得 ``m / 2 = k / 2``。
看看你能否完成这个事实的证明，然后用它来完成证明。
BOTH: -/
-- QUOTE:
example {n : ℕ} (A : Finset ℕ)
    (hA : #(A) = n + 1)
    (hA' : A ⊆ range (2 * n)) :
    ∃ m ∈ A, ∃ k ∈ A, Nat.Coprime m k := by
  have : ∃ t ∈ range n, 1 < #({u ∈ A | u / 2 = t}) := by
    apply exists_lt_card_fiber_of_mul_lt_card_of_maps_to
-- EXAMPLES:
    · sorry
/- SOLUTIONS:
    · intro u hu
      specialize hA' hu
      simp only [mem_range] at *
      exact Nat.div_lt_of_lt_mul hA'
EXAMPLES: -/
    · sorry
/- SOLUTIONS:
    · simp [hA]
BOTH: -/
  rcases this with ⟨t, ht, ht'⟩
  simp only [one_lt_card, mem_filter] at ht'
-- EXAMPLES:
  sorry
/- SOLUTIONS:
  rcases ht' with ⟨m, ⟨hm, hm'⟩, k, ⟨hk, hk'⟩, hmk⟩
  have : m = k + 1 ∨ k = m + 1 := by omega
  rcases this with rfl | rfl
  . use k, hk, k+1, hm; simp
  . use m, hm, m+1, hk; simp
BOTH: -/
-- QUOTE.
