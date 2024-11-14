-- BOTH:
import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S06

/- TEXT:
.. _sequences_and_convergence:

序列和收敛
-------------------------

来做一些真正的数学！在 Lean 中，我们可以把实数序列 :math:`s_0, s_1, s_2, \ldots` 写成函数 ``s : ℕ → ℝ`` 。我们称这个序列 *收敛* 到数 :math:`a` ，如果对任意 :math:`\varepsilon > 0` ，存在一个位置，在该位置之后，序列留在距离 :math:`a` 不超过 :math:`\varepsilon` 的范围内，也就是说，存在数 :math:`N`, 使得对于任意 :math:`n \ge N` ， :math:`| s_n - a | < \varepsilon` 。

在 Lean 中，我们可以将其表述如下：
BOTH: -/
-- QUOTE:
def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε
-- QUOTE.

/- TEXT:
符号 ``∀ ε > 0, ...`` 是 ``∀ ε, ε > 0 → ...`` 的方便缩写，类似地， ``∀ n ≥ N, ...`` 是 ``∀ n, n ≥ N →  ...`` 的缩写。记住 ``ε > 0`` 的定义是 ``0 < ε`` ，而 ``n ≥ N`` 的定义是 ``N ≤ n`` 。

.. index:: extensionality, ext, tactics ; ext

本节将证明收敛的一些性质。但首先我们将介绍三个用于处理等式的策略。第一个是 ``ext`` 策略，它给我们提供了一种证明两个函数相等的途径。令 :math:`f(x) = x + 1` 和 :math:`g(x) = 1 + x` 是从实数到实数的函数。当然有 :math:`f = g` ，因为对任意 :math:`x`, 它们返回相同的值。``ext`` 策略允许我们通过证明函数在所有参数下的值都相同来证明函数等式。
TEXT. -/
-- QUOTE:
example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext
  ring
-- QUOTE.

/- TEXT:
.. index:: congr, tactics ; congr

稍后将看到，可以指定 ``ext`` 中出现的变量名。例如，你可以尝试在上面的证明中把 ``ext`` 替换为 ``ext u v`` 。第二个策略是 ``congr`` 策略，它允许我们通过调和有差异的部分来证明两个表达式之间的等式：
TEXT. -/
-- QUOTE:
example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring
-- QUOTE.

/- TEXT:
在这里 ``congr`` 策略剥离两边的 ``abs`` ，只留下 ``a = a - b + b`` 。

.. index:: convert, tactics ; convert

最后， ``convert`` 策略用于在定理和结论不完全一致时将定理应用于目标。例如，假定我们想从 ``1 < a`` 证明 ``a < a * a`` 。库定理 ``mul_lt_mul_right`` 让我们证明 ``1 * a < a * a`` 。一种可能的方法是逆向工作，重写目标使其具有这种形式。相反， ``convert`` 策略原封不动地应用定理，留下证明匹配目标所需等式的任务。
TEXT. -/
-- QUOTE:
example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert (mul_lt_mul_right _).2 h
  · rw [one_mul]
  exact lt_trans zero_lt_one h
-- QUOTE.

/- TEXT:
这个示例还说明了另一个有用的技巧：Lean 无法自动填写带下划线的表达式时，它就会把下划线作为另一个目标留给我们。

下面证明任意常数序列 :math:`a, a, a, \ldots` 收敛。
BOTH: -/
-- QUOTE:
theorem convergesTo_const (a : ℝ) : ConvergesTo (fun x : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n nge
  rw [sub_self, abs_zero]
  apply εpos
-- QUOTE.

/- TEXT:
.. TODO: reference to the simplifier

策略 ``simp`` 经常可以为你省下手写 ``rw [sub_self, abs_zero]`` 这种步骤的麻烦。稍后详细介绍。

让我们证明一个更有趣的定理，如果 ``s`` 收敛到 ``a`` ， ``t`` 收敛到 ``b`` ，那么 ``fun n ↦ s n + t n`` 收敛到 ``a + b`` 。在开始写形式证明之前，先建立清晰的纸笔证明是很有帮助的。给定 ``ε`` 大于 ``0`` ，思路是利用假设得到 ``Ns`` ，使得超出这一位置时， ``s`` 在 ``a`` 附近 ``ε / 2`` 内，以及 ``Nt`` ，使得超出这一位置时， ``s`` 在 ``b`` 附近 ``ε / 2`` 内。而后，当 ``n`` 大于或等于 ``Ns`` 和 ``Nt`` 的最大值时，序列 ``fun n ↦ s n + t n`` 应在 ``a + b`` 附近 ``ε`` 内。完成下面的证明。

（提示，你可以使用 ``le_of_max_le_left`` 和 ``le_of_max_le_right`` ； ``norm_num`` 可以证明 ``ε / 2 + ε / 2 = ε`` 。还有，使用 ``congr`` 策略有助于证明 ``|s n + t n - (a + b)|`` 等于 ``|(s n - a) + (t n - b)|`` ，因为在那之后你就可以使用三角不等式。把全部变量 ``s``, ``t``, ``a``, ``b`` 标记为隐变量，因为它们可以从假设中推断出来。）
TEXT. -/
-- QUOTE:
theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  sorry
-- QUOTE.

-- SOLUTIONS:
theorem convergesTo_addαα {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro n hn
  have ngeNs : n ≥ Ns := le_of_max_le_left hn
  have ngeNt : n ≥ Nt := le_of_max_le_right hn
  calc
    |s n + t n - (a + b)| = |s n - a + (t n - b)| := by
      congr
      ring
    _ ≤ |s n - a| + |t n - b| := (abs_add _ _)
    _ < ε / 2 + ε / 2 := (add_lt_add (hs n ngeNs) (ht n ngeNt))
    _ = ε := by norm_num

/- TEXT:
证明把加法换成乘法的同样定理需要技巧。我们会先证明一些辅助性的结论。看看你能否同样完成下列证明，它表明若 ``s`` 收敛于 ``a`` ，则 ``fun n ↦ c * s n`` 收敛于 ``c * a`` 。根据 ``c`` 是否等于零来区分不同情况有助于证明。我们已经处理了零的情况，现在让你在另一种假设，即 ``c`` 非零时证明结论。
TEXT. -/
-- QUOTE:
theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h
  sorry
-- QUOTE.

-- SOLUTIONS:
theorem convergesTo_mul_constαα {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h
  intro ε εpos
  dsimp
  have εcpos : 0 < ε / |c| := by apply div_pos εpos acpos
  rcases cs (ε / |c|) εcpos with ⟨Ns, hs⟩
  use Ns
  intro n ngt
  calc
    |c * s n - c * a| = |c| * |s n - a| := by rw [← abs_mul, mul_sub]
    _ < |c| * (ε / |c|) := (mul_lt_mul_of_pos_left (hs n ngt) acpos)
    _ = ε := mul_div_cancel₀ _ (ne_of_lt acpos).symm

/- TEXT:
下一个定理也很有趣：收敛序列在绝对值意义下最终是有界的。完成它。
TEXT. -/
-- QUOTE:
theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  sorry
-- QUOTE.

-- SOLUTIONS:
theorem exists_abs_le_of_convergesToαα {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  intro n ngt
  calc
    |s n| = |s n - a + a| := by
      congr
      abel
    _ ≤ |s n - a| + |a| := (abs_add _ _)
    _ < |a| + 1 := by linarith [h n ngt]

/- TEXT:
事实上，该定理还可以加强，断言存在一个对所有 ``n`` 值都成立的界 ``b`` 。但这个版本对我们的目的来说已经足够强了，我们将在本节结尾看到它在更一般的条件下成立。

接下来的引理是辅助性的：我们证明若 ``s`` 收敛到 ``a`` 且 ``t`` 收敛到 ``0`` ，则 ``fun n ↦ s n * t n`` 收敛到 ``0`` 。为了证明它，我们使用上一个定理来找到 ``B`` ，作为 ``s`` 在超出 ``N₀`` 时的界。看看你能否理解我们简述的思路并完成证明。
TEXT. -/
-- QUOTE:
theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  sorry
-- QUOTE.

-- SOLUTIONS:
theorem auxαα {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  use max N₀ N₁
  intro n ngt
  have ngeN₀ : n ≥ N₀ := le_of_max_le_left ngt
  have ngeN₁ : n ≥ N₁ := le_of_max_le_right ngt
  calc
    |s n * t n - 0| = |s n| * |t n - 0| := by rw [sub_zero, abs_mul, sub_zero]
    _ < B * (ε / B) := (mul_lt_mul'' (h₀ n ngeN₀) (h₁ n ngeN₁) (abs_nonneg _) (abs_nonneg _))
    _ = ε := mul_div_cancel₀ _ (ne_of_lt Bpos).symm

/- TEXT:
如果你已经走到这一步，那么恭喜你！我们现在已经离定理不远了。下面的证明将为我们画上圆满的句号。
TEXT. -/
-- QUOTE:
-- BOTH:
theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs
    convert convergesTo_add ct (convergesTo_const (-b))
    ring
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert convergesTo_add h₁ (convergesTo_mul_const b cs) using 1
  · ext; ring
  ring
-- QUOTE.

/- TEXT:
另一个具有挑战性的练习，请试着填写下面的极限唯一性的证明概要。(如果你觉得自信，可以删除证明概要，然后尝试从头开始证明）。

TEXT. -/
-- QUOTE:
theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : |a - b| > 0 := by sorry
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := by sorry
  have absb : |s N - b| < ε := by sorry
  have : |a - b| < |a - b| := by sorry
  exact lt_irrefl _ this
-- QUOTE.

-- SOLUTIONS:
theorem convergesTo_uniqueαα {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : |a - b| > 0 := by
    apply lt_of_le_of_ne
    · apply abs_nonneg
    intro h''
    apply abne
    apply eq_of_abs_sub_eq_zero h''.symm
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := by
    apply hNa
    apply le_max_left
  have absb : |s N - b| < ε := by
    apply hNb
    apply le_max_right
  have : |a - b| < |a - b|
  calc
    |a - b| = |(-(s N - a)) + (s N - b)| := by
      congr
      ring
    _ ≤ |(-(s N - a))| + |s N - b| := (abs_add _ _)
    _ = |s N - a| + |s N - b| := by rw [abs_neg]
    _ < ε + ε := (add_lt_add absa absb)
    _ = |a - b| := by norm_num [ε]

  exact lt_irrefl _ this

/- TEXT:
在本节的最后，我们要指出，我们的证明是可以推广的。例如，我们使用的唯一一条自然数性质是它们的结构带有含 ``min`` 和 ``max`` 的偏序。如果把 ``ℕ`` 换成任意线性序 ``α``, 你可以验证一切仍然正确：
TEXT. -/
section
-- QUOTE:
variable {α : Type*} [LinearOrder α]

def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε
-- QUOTE.

end

/- TEXT:
在 :numref:`filters` 中，我们将看到 Mathlib 有更一般的机制来处理收敛，它不仅抽象化了定义域和值域的特定特征，还在抽象意义下统一了不同类型的收敛。
TEXT. -/
