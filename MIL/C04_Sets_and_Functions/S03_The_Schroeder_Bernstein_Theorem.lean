import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import MIL.Common

open Set
open Function

/- TEXT:
.. _the_schroeder_bernstein_theorem:

施罗德-伯恩斯坦定理
------------------------------

我们用一个初等而非平凡的定理结束本章。令 :math:`\alpha` 和 :math:`\beta` 是集合。（在本节的形式化中, 它们实际上会是类型。）假定 :math:`f : \alpha → \beta` 和 :math:`g : \beta → \alpha` 都是单射。直观上，这意味着 :math:`\alpha` 不大于 :math:`\beta` ，反之亦然。如果 :math:`\alpha` 和 :math:`\beta` 是有限的，这意味着它们具有相同的基数，而这相当于说它们之间存在双射。在十九世纪，康托尔（Cantor）指出，即使当 :math:`\alpha` 和 :math:`\beta` 无穷时，同样的结果也成立。这个结果最终由戴德金（Dedekind）、施罗德（Schröder）和伯恩斯坦（Bernstein）各自独立证明。

本节引入的新方法会接下来的章节中更详细地解释，所以不必担心本节讲得太快。本节目标是向你展示你已经可以为真正的数学结果的形式化做出贡献。

证明的主要目标是构造 :math:`\alpha` 和 :math:`\beta` 之间的双射。现在展示直观上的证明步骤。考虑映射 :math:`g` 在 :math:`\alpha` 中的像。在这个像中，可以定义 :math:`g` 的逆，且是到 :math:`\beta` 的双射。

.. image:: /figures/schroeder_bernstein1.*
   :height: 150 px
   :alt: the Schröder Bernstein theorem
   :align: center

问题是双射不包括图中的阴影区域，如果 :math:`g` 不是满射，则阴影是非空的。或者，我们可以使用 :math:`f` 把整个 :math:`\alpha` 映射到 :math:`\beta` ，但在那种情况下问题是若 :math:`f` 不是满射，则它会同样错过 :math:`\beta` 内的一些元素。

.. image:: /figures/schroeder_bernstein2.*
   :height: 150 px
   :alt: the Schröder Bernstein theorem
   :align: center

但现在考虑从 :math:`\alpha` 到自身的复合映射 :math:`g \circ f` 。由于这个复合映射是单射，可以证明它也是 :math:`\alpha` 到它的像的双射，直观上就是在 :math:`\alpha` 内部产生了一个缩小的副本。

.. image:: /figures/schroeder_bernstein3.*
   :height: 150 px
   :alt: the Schröder Bernstein theorem
   :align: center

这个复合将内部阴影环映射到另一个这样的集合，我们可以将其视为更小的同心阴影环，依此类推。这会产生一个阴影环的同心序列，每个都与下一个有双射对应。这实际上得到了 :math:`\alpha` 和 :math:`g` 的像之间的双射： :math:`\alpha` 的白色部分不动，每个阴影圆环映射到下一个。和 :math:`g^{-1}` 复合一下就产生了所需的 :math:`\alpha` 和 :math:`\beta` 的双射。

形式化地，令 :math:`A` 为这列阴影区域的并，如下定义 :math:`h : \alpha \to \beta`:

.. math::

  h(x) = \begin{cases}
    f(x) & \text{if $x \in A$} \\
    g^{-1}(x) & \text{otherwise.}
  \end{cases}

换句话说，我们在阴影部分使用 :math:`f` ，而在其余部分使用 :math:`g` 的逆。生成的映射 :math:`h` 是单射，因为每个分支都是单射并且两个分支的像是不相交的。为了看出它是满射，假设给定了 :math:`\beta` 中的元素 :math:`y` ，考虑 :math:`g(y)` 。若 :math:`g(y)` 位于阴影区域之一，它不能在第一个环中，因此我们有 :math:`g(y) = g(f(x))` ，其中 :math:`x` 在上一个环中。由 :math:`g` 的单射性，我们有 :math:`h(x) = f(x) = y` 。若 :math:`g(y)` 不在阴影区域中，那么由 :math:`h` 的定义，我们有 :math:`h(g(y))= y` 。不论哪种情况， :math:`y` 都在 :math:`h` 的像中。

这个论证听起来应该有道理，但细节却很微妙。形式化证明不仅可以提高我们对结果的信心，还可以帮助我们更好地理解它。因为证明使用经典逻辑，所以我们告诉 Lean，我们的定义通常是不可计算的。
BOTH: -/
-- QUOTE:
noncomputable section
open Classical
variable {α β : Type*} [Nonempty β]
-- QUOTE.

/- TEXT:
记号 ``[Nonempty β]`` 规定 ``β`` 非空。我们使用它是因为我们将用于构造 :math:`g^{-1}` 的 Mathlib 原语要求它。定理在 :math:`\beta` 为空的情形是平凡的，虽然把形式化推广到覆盖这种情况并不难，但当下就算了。特别地，我们需要假设 ``[Nonempty β]`` 以使用 Mathlib 中定义的运算 ``invFun`` 。对于给定的 ``x : α``,  如果有的话，``invFun g x`` 选择 ``x`` 在 ``β`` 中的一个原像，否则就返回 ``β`` 中的任意元素。若 ``g`` 是单射，则 ``invFun g`` 一定是左逆，若 ``g`` 是满射，则它是右逆。

-- LITERALINCLUDE: invFun g

我们定义对应于阴影区域的并的集合如下。
BOTH: -/
section
-- QUOTE:
variable (f : α → β) (g : β → α)

def sbAux : ℕ → Set α
  | 0 => univ \ g '' univ
  | n + 1 => g '' (f '' sbAux n)

def sbSet :=
  ⋃ n, sbAux f g n
-- QUOTE.

/- TEXT:
定义 ``sbAux`` 是 **递归定义** 的一个例子，我们将在下一章解释。它定义了一列集合

.. math::

  S_0 &= \alpha ∖ g(\beta) \\
  S_{n+1} &= g(f(S_n)).

定义 ``sbSet`` 对应于我们的证明概要中的集合 :math:`A = \bigcup_{n \in \mathbb{N}} S_n` 。上面描述的函数 :math:`h` 现在定义如下：
BOTH: -/
-- QUOTE:
def sbFun (x : α) : β :=
  if x ∈ sbSet f g then f x else invFun g x
-- QUOTE.

/- TEXT:
我们将需要这样的事实：我们定义的 :math:`g^{-1}` 是 :math:`A` 的补集上的右逆，也就是 :math:`\alpha` 中白色区域上的右逆。这是因为最外层的环 :math:`S_0` 等于 :math:`\alpha \setminus g(\beta)` ，因此 :math:`A` 的补集包含于 :math:`g(\beta)` 中。所以，对 :math:`A` 的补集中的每个 :math:`x` ，存在 :math:`y` 使得 :math:`g(y) = x` 。（由 :math:`g` 的单射性，这个 :math:`y` 是唯一的，但下一个定理只说了 ``invFun g x`` 返回 ``y`` 使得 ``g y = x``.）

逐步完成下面的证明，确保你理解发生了什么，并填写剩余部分。你需要在最后使用 ``invFun_eq`` 。请注意，此处用 ``sbAux`` 重写替换了 ``sbAux f g 0`` 与相应定义方程的右侧。
BOTH: -/
-- QUOTE:
theorem sb_right_inv {x : α} (hx : x ∉ sbSet f g) : g (invFun g x) = x := by
  have : x ∈ g '' univ := by
    contrapose! hx
    rw [sbSet, mem_iUnion]
    use 0
    rw [sbAux, mem_diff]
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    exact ⟨mem_univ _, hx⟩
-- BOTH:
  have : ∃ y, g y = x := by
/- EXAMPLES:
    sorry
  sorry
SOLUTIONS: -/
    simp at this
    assumption
  exact invFun_eq this
-- BOTH:
-- QUOTE.

/- TEXT:
我们现在转向证明 :math:`h` 是单射。非正式地证明过程如下。首先，假设 :math:`h(x_1) = h(x_2)` 。若 :math:`x_1` 在 :math:`A` 中，则 :math:`h(x_1) = f(x_1)` ，且我们可以证明 :math:`x_2` 在 :math:`A` 中如下。若非如此，则我们有 :math:`h(x_2) = g^{-1}(x_2)` 。由 :math:`f(x_1) = h(x_1) = h(x_2)` 我们有 :math:`g(f(x_1)) = x_2` 。由 :math:`A` 的定义，既然 :math:`x_1` 在 :math:`A` 中， :math:`x_2` 同样在 :math:`A` 中，矛盾。因此，若 :math:`x_1` 在 :math:`A` 中，则 :math:`x_2` 也在，这种情况下我们有 :math:`f(x_1) = h(x_1) = h(x_2) = f(x_2)` 。 :math:`f` 的单射性推出 :math:`x_1 = x_2` 。对称论证表明若 :math:`x_2` 在 :math:`A` 中，则 :math:`x_1` 也在，这又一次蕴含着 :math:`x_1 = x_2` 。

剩下的唯一可能性是 :math:`x_1` 和 :math:`x_2` 都不在 :math:`A` 中。这种情况下，我们有 :math:`g^{-1}(x_1) = h(x_1) = h(x_2) = g^{-1}(x_2)` 。两边使用 :math:`g` 就得到 :math:`x_1 = x_2` 。

我们再次鼓励你逐步完成以下证明，观察这个论证在 Lean 中是如何展开的。看看你是否可以使用 ``sb_right_inv`` 结束证明。
BOTH: -/
-- QUOTE:
theorem sb_injective (hf : Injective f) : Injective (sbFun f g) := by
  set A := sbSet f g with A_def
  set h := sbFun f g with h_def
  intro x₁ x₂
  intro (hxeq : h x₁ = h x₂)
  show x₁ = x₂
  simp only [h_def, sbFun, ← A_def] at hxeq
  by_cases xA : x₁ ∈ A ∨ x₂ ∈ A
  · wlog x₁A : x₁ ∈ A generalizing x₁ x₂ hxeq xA
    · symm
      apply this hxeq.symm xA.symm (xA.resolve_left x₁A)
    have x₂A : x₂ ∈ A := by
      apply _root_.not_imp_self.mp
      intro (x₂nA : x₂ ∉ A)
      rw [if_pos x₁A, if_neg x₂nA] at hxeq
      rw [A_def, sbSet, mem_iUnion] at x₁A
      have x₂eq : x₂ = g (f x₁) := by
/- EXAMPLES:
        sorry
SOLUTIONS: -/
        rw [hxeq, sb_right_inv f g x₂nA]
-- BOTH:
      rcases x₁A with ⟨n, hn⟩
      rw [A_def, sbSet, mem_iUnion]
      use n + 1
      simp [sbAux]
      exact ⟨x₁, hn, x₂eq.symm⟩
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    rw [if_pos x₁A, if_pos x₂A] at hxeq
    exact hf hxeq
-- BOTH:
  push_neg  at xA
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  rw [if_neg xA.1, if_neg xA.2] at hxeq
  rw [← sb_right_inv f g xA.1, hxeq, sb_right_inv f g xA.2]
-- BOTH:
-- QUOTE.

/- TEXT:
这个证明引入了一些新策略。首先， ``set`` 策略引入了缩写 ``A`` 和 ``h`` 分别代表 ``sbSet f g`` 和 ``sb_fun f g`` 。我们把对应的定义式命名为 ``A_def`` 和 ``h_def`` 。这些缩写是定义性的，也就是说，当需要时，Lean有时会自动展开它们。但并不总是如此；例如，当使用 ``rw`` 时，我们通常需要精确地使用 ``A_def`` 和 ``h_def`` 。所以这些定义带来了一个权衡：它们可以使表达式更短并且更具可读性，但它们有时需要我们做更多的工作。

一个更有趣的策略是 ``wlog`` 策略，它封装了上面非正式证明中的对称性论证。我们现在不会详细讨论它，但请注意它恰好做了我们想要的工作。如果将鼠标悬停在该策略上，你可以查看其文档。

满射性的论证甚至更容易。给定 :math:`\beta` 中的 :math:`y` ，我们考虑两种情况，取决于 :math:`g(y)` 是否在 :math:`A` 中。若是，则它不会在最外层的环 :math:`S_0` 中，因为根据定义，这个环和 :math:`g` 的像不相交。因此存在 :math:`n` 使得 `g(y)` 是 :math:`S_{n+1}` 的元素。这意味着它形如 :math:`g(f(x))` ，其中 :math:`x` 在 :math:`S_n` 中。由 :math:`g` 的单射性，我们有 :math:`f(x) = y` 。在 :math:`g(y)` 属于 :math:`A` 的补集的情况，我们立刻得到 :math:`h(g(y))= y`, 证毕。

我们再次鼓励您逐步完成证明并填写缺失的部分。策略 ``cases n with n`` 分解为情况 ``g y ∈ sbAux f g 0`` 和 ``g y ∈ sbAux f g n.succ`` 。在两种情况下，通过 ``simp [sbAux]`` 调用化简器都会应用 ``sbAux`` 的相应定义式。
BOTH: -/
-- QUOTE:
theorem sb_surjective (hg : Injective g) : Surjective (sbFun f g) := by
  set A := sbSet f g with A_def
  set h := sbFun f g with h_def
  intro y
  by_cases gyA : g y ∈ A
  · rw [A_def, sbSet, mem_iUnion] at gyA
    rcases gyA with ⟨n, hn⟩
    rcases n with _ | n
    · simp [sbAux] at hn
    simp [sbAux] at hn
    rcases hn with ⟨x, xmem, hx⟩
    use x
    have : x ∈ A := by
      rw [A_def, sbSet, mem_iUnion]
      exact ⟨n, xmem⟩
    simp only [h_def, sbFun, if_pos this]
    exact hg hx
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  use g y
  simp only [h_def, sbFun, if_neg gyA]
  apply leftInverse_invFun hg
-- BOTH:
-- QUOTE.

end

/- TEXT:
我们现在可以把它们放在一起。最后的论证简短而优雅，证明使用了 ``Bijective h`` 展开为 ``Injective h ∧ Surjective h`` 这一事实。
EXAMPLES: -/
-- QUOTE:
theorem schroeder_bernstein {f : α → β} {g : β → α} (hf : Injective f) (hg : Injective g) :
    ∃ h : α → β, Bijective h :=
  ⟨sbFun f g, sb_injective f g hf, sb_surjective f g hg⟩
-- QUOTE.

-- Auxiliary information
section
variable (g : β → α) (x : α)

-- TAG: invFun g
#check (invFun g : α → β)
#check (leftInverse_invFun : Injective g → LeftInverse (invFun g) g)
#check (leftInverse_invFun : Injective g → ∀ y, invFun g (g y) = y)
#check (invFun_eq : (∃ y, g y = x) → g (invFun g x) = x)
-- TAG: end

end
