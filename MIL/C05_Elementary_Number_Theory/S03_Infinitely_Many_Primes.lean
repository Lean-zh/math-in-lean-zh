import Mathlib.Data.Nat.Prime.Basic
import MIL.Common

open BigOperators

namespace C05S03

/- TEXT:
.. _section_infinitely_many_primes:

无穷多个素数
------------

让我们继续探讨归纳法和递归法，这次以另一个数学标准为例：证明存在无穷多个素数。一种表述方式是：对于每一个自然数 :math:`n` ，都存在一个大于 :math:`n` 的素数。要证明这一点，设 :math:`p` 是 :math:`n！ + 1` 的任意一个素因数。如果 :math:`p` 小于或等于 :math:`n` ，那么它能整除 :math:`n！` 。由于它也能整除 :math:`n！ + 1` ，所以它能整除 1 ，这与事实相悖。因此 :math:`p` 大于 :math:`n` 。

要使该证明形式化，我们需要证明任何大于或等于 2 的数都有一个质因数。
要做到这一点，我们需要证明任何不等于 0 或 1 的自然数都大于或等于 2。
这让我们看到了形式化的一个奇特之处：
往往正是像这样的简单陈述最难形式化。
这里我们考虑几种实现方式。

首先，我们可以使用 ``cases`` 策略以及后继函数在自然数上保持顺序这一事实。
BOTH: -/
-- QUOTE:
theorem two_le {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  cases m; contradiction
  case succ m =>
    cases m; contradiction
    repeat apply Nat.succ_le_succ
    apply zero_le
-- QUOTE.

/- TEXT:
另一种策略是使用 ``interval_cases`` 这一策略，它会在所讨论的变量处于自然数或整数的某个区间内时，自动将目标分解为多个情况。请记住，您可以将鼠标悬停在它上面以查看其文档说明。
EXAMPLES: -/
-- QUOTE:
example {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  by_contra h
  push_neg at h
  interval_cases m <;> contradiction
-- QUOTE.

/- TEXT:
.. index:: decide, tactics ; decide

回想一下， ``interval_cases m`` 后面的分号表示接下来的策略将应用于它生成的每个情况。另一个选择是使用 ``decide`` 策略，它尝试找到一个决策过程来解决问题。Lean 知道，对于以有界量词 ``∀ x, x < n → ...`` 或 ``∃ x, x < n ∧ ...`` 开头的陈述，可以通过决定有限多个实例来确定其真值。
EXAMPLES: -/
-- QUOTE:
example {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  by_contra h
  push_neg at h
  revert h0 h1
  revert h m
  decide
-- QUOTE.

/- TEXT:
有了 ``two_le`` 这个定理，让我们先证明每个大于 2 的自然数都有一个素数因子。
Mathlib 包含一个函数 ``Nat.minFac`` ，它会返回最小的素数因子，但为了学习库的新部分，我们将避免使用它，直接证明这个定理。

在这里，普通的归纳法不够用。
我们想用 **强归纳法** ，它允许我们通过证明对于每个自然数 :math:`n` ，如果 :math:`P` 对所有小于 :math:`n` 的值都成立，那么 :math:`P` 在 :math:`n` 处也成立，从而证明每个自然数 :math:`n` 都具有性质 :math:`P` 。
在 Lean 中，这个原理被称为 ``Nat.strong_induction_on`` ，我们可以使用 ``using`` 关键字告诉归纳法策略使用它。
请注意，当我们这样做时，就没有了基本情况；它被包含在一般的归纳步骤中。

论证过程很简单。假设 :math:`n ≥ 2` ，如果 :math:`n` 是质数，那么证明就完成了。如果不是，那么根据质数的定义之一，它有一个非平凡因子 :math:`m` ，此时我们可以对这个因子应用归纳假设。步进证明，看看具体是如何进行的。
BOTH: -/
-- QUOTE:
theorem exists_prime_factor {n : Nat} (h : 2 ≤ n) : ∃ p : Nat, p.Prime ∧ p ∣ n := by
  by_cases np : n.Prime
  · use n, np
  induction' n using Nat.strong_induction_on with n ih
  rw [Nat.prime_def_lt] at np
  push_neg at np
  rcases np h with ⟨m, mltn, mdvdn, mne1⟩
  have : m ≠ 0 := by
    intro mz
    rw [mz, zero_dvd_iff] at mdvdn
    linarith
  have mgt2 : 2 ≤ m := two_le this mne1
  by_cases mp : m.Prime
  · use m, mp
  · rcases ih m mltn mgt2 mp with ⟨p, pp, pdvd⟩
    use p, pp
    apply pdvd.trans mdvdn
-- QUOTE.

/- TEXT:
现在我们可以证明我们定理的以下表述形式。
看看你能否完善这个概要。
你可以使用 ``Nat.factorial_pos`` 、 ``Nat.dvd_factorial`` 和 ``Nat.dvd_sub'`` 。
BOTH: -/
-- QUOTE:
theorem primes_infinite : ∀ n, ∃ p > n, Nat.Prime p := by
  intro n
  have : 2 ≤ Nat.factorial (n + 1) + 1 := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    apply Nat.succ_le_succ
    exact Nat.succ_le_of_lt (Nat.factorial_pos _)
-- BOTH:
  rcases exists_prime_factor this with ⟨p, pp, pdvd⟩
  refine ⟨p, ?_, pp⟩
  show p > n
  by_contra ple
  push_neg  at ple
  have : p ∣ Nat.factorial (n + 1) := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    apply Nat.dvd_factorial
    apply pp.pos
    linarith
-- BOTH:
  have : p ∣ 1 := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    convert Nat.dvd_sub' pdvd this
    simp
-- BOTH:
  show False
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  have := Nat.le_of_dvd zero_lt_one this
  linarith [pp.two_le]

-- BOTH:
-- QUOTE.
/- TEXT:
让我们考虑上述证明的一个变体，其中不使用阶乘函数，而是假设我们得到一个有限集合 :math:`\{ p_1， \ldots， p_n \}` ，并考虑 :math:`\prod_{i = 1}^n p_i + 1` 的一个质因数。该质因数必须与每个 :math:`p_i` 都不同，这表明不存在包含所有质数的有限集合。

要将此论证形式化，我们需要对有限集合进行推理。在 Lean 中，对于任何类型 ``α`` ，类型 ``Finset α`` 表示类型为 ``α`` 的元素的有限集合。从计算角度对有限集合进行推理需要有一个在 ``α`` 上测试相等性的过程，这就是下面代码片段包含假设 ``[DecidableEq α]`` 的原因。对于像 ``ℕ`` 、 ``ℤ`` 和 ``ℚ`` 这样的具体数据类型，该假设会自动满足。在对实数进行推理时，可以使用经典逻辑并放弃计算解释来满足该假设。

我们使用命令 ``open Finset`` 来使用相关定理的更短名称。与集合的情况不同，涉及有限集的大多数等价关系并非定义上的成立，因此需要手动使用诸如 ``Finset.subset_iff`` 、 ``Finset.mem_union`` 、 ``Finset.mem_inter`` 和 ``Finset.mem_sdiff`` 这样的等价关系来展开。不过， ``ext`` 策略仍然可以用于通过证明一个有限集的每个元素都是另一个有限集的元素来证明两个有限集相等。
BOTH: -/
-- QUOTE:
open Finset

-- EXAMPLES:
section
variable {α : Type*} [DecidableEq α] (r s t : Finset α)

example : r ∩ (s ∪ t) ⊆ r ∩ s ∪ r ∩ t := by
  rw [subset_iff]
  intro x
  rw [mem_inter, mem_union, mem_union, mem_inter, mem_inter]
  tauto

example : r ∩ (s ∪ t) ⊆ r ∩ s ∪ r ∩ t := by
  simp [subset_iff]
  intro x
  tauto

example : r ∩ s ∪ r ∩ t ⊆ r ∩ (s ∪ t) := by
  simp [subset_iff]
  intro x
  tauto

example : r ∩ s ∪ r ∩ t = r ∩ (s ∪ t) := by
  ext x
  simp
  tauto

end
-- QUOTE.

/- TEXT:
我们使用了一个新技巧： ``tauto`` 策略（还有一个更强的 ``tauto！`` ，这个使用经典逻辑）可以用来省去命题逻辑中的重言式。
看看你能否用这些方法证明下面的两个例子。
BOTH: -/
section
variable {α : Type*} [DecidableEq α] (r s t : Finset α)

-- QUOTE:
example : (r ∪ s) ∩ (r ∪ t) = r ∪ s ∩ t := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  ext x
  rw [mem_inter, mem_union, mem_union, mem_union, mem_inter]
  tauto

example : (r ∪ s) ∩ (r ∪ t) = r ∪ s ∩ t := by
  ext x
  simp
  tauto

-- BOTH:
example : (r \ s) \ t = r \ (s ∪ t) := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  ext x
  rw [mem_sdiff, mem_sdiff, mem_sdiff, mem_union]
  tauto

example : (r \ s) \ t = r \ (s ∪ t) := by
  ext x
  simp
  tauto
-- QUOTE.
-- BOTH:

end

/- TEXT:
定理 ``Finset.dvd_prod_of_mem`` 告诉我们，如果一个数 ``n`` 是有限集合 ``s`` 的一个元素，那么 ``n`` 能整除 ``∏ i in s, i`` 。
EXAMPLES: -/
-- QUOTE:
example (s : Finset ℕ) (n : ℕ) (h : n ∈ s) : n ∣ ∏ i in s, i :=
  Finset.dvd_prod_of_mem _ h
-- QUOTE.

/- TEXT:
我们还需要知道，在 ``n`` 为素数且 ``s`` 为素数集合的情况下，其逆命题也成立。要证明这一点，我们需要以下引理，您应该能够使用定理 ``Nat.Prime.eq_one_or_self_of_dvd`` 来证明它。
BOTH: -/
-- QUOTE:
theorem _root_.Nat.Prime.eq_of_dvd_of_prime {p q : ℕ}
      (prime_p : Nat.Prime p) (prime_q : Nat.Prime q) (h : p ∣ q) :
    p = q := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  cases prime_q.eq_one_or_self_of_dvd _ h
  · linarith [prime_p.two_le]
  assumption
-- QUOTE.
-- BOTH:

/- TEXT:
我们可以利用这个引理来证明，如果一个素数 ``p`` 整除有限个素数的乘积，那么它就等于其中的一个素数。
``Mathlib`` 提供了一个关于有限集合的有用归纳原理：要证明某个性质对任意有限集合 ``s`` 成立，只需证明其对空集成立，并证明当向集合 ``s`` 中添加一个新元素 ``a ∉ s`` 时该性质仍成立。
这个原理被称为 ``Finset.induction_on`` 。当我们告诉归纳策略使用它时，还可以指定名称 ``a`` 和 ``s`` ，以及归纳步骤中假设 ``a ∉ s`` 的名称和归纳假设的名称。
表达式 ``Finset.insert a s`` 表示集合 ``s`` 与单元素集合 ``a`` 的并集。
恒等式 ``Finset.prod_empty`` 和 ``Finset.prod_insert`` 则提供了乘积相关的重写规则。
在下面的证明中，第一个 ``simp`` 应用了 ``Finset.prod_empty`` 。
逐步查看证明的开头部分，以了解归纳过程的展开，然后完成证明。
BOTH: -/
-- QUOTE:
theorem mem_of_dvd_prod_primes {s : Finset ℕ} {p : ℕ} (prime_p : p.Prime) :
    (∀ n ∈ s, Nat.Prime n) → (p ∣ ∏ n in s, n) → p ∈ s := by
  intro h₀ h₁
  induction' s using Finset.induction_on with a s ans ih
  · simp at h₁
    linarith [prime_p.two_le]
  simp [Finset.prod_insert ans, prime_p.dvd_mul] at h₀ h₁
  rw [mem_insert]
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  rcases h₁ with h₁ | h₁
  · left
    exact prime_p.eq_of_dvd_of_prime h₀.1 h₁
  right
  exact ih h₀.2 h₁

-- BOTH:
-- QUOTE.
/- TEXT:
我们需要有限集合的一个最后性质。
给定一个元素 ``s : Set α`` 和一个关于 ``α`` 的谓词 ``P`` ，在 :numref:`第 %s 章 <sets_and_functions>` 中，我们用 ``{ x ∈ s | P x }`` 表示集合 ``s`` 中满足 ``P`` 的元素。
对于 ``s ： Finset α`` ，类似的概念写作 ``s.filter P`` 。
EXAMPLES: -/
-- QUOTE:
example (s : Finset ℕ) (x : ℕ) : x ∈ s.filter Nat.Prime ↔ x ∈ s ∧ x.Prime :=
  mem_filter
-- QUOTE.

/- TEXT:
我们现在证明关于存在无穷多个素数的另一种表述，即对于任意的 ``s : Finset ℕ`` ，都存在一个素数 ``p`` 不属于 ``s`` 。
为了得出矛盾，我们假设所有的素数都在 ``s`` 中，然后缩小到一个只包含素数的集合 ``s'`` 。
将该集合的元素相乘，加一，然后找到结果的一个素因数，这将得出我们所期望的矛盾。
看看你能否完成下面的概要。
在第一个 ``have`` 的证明中，你可以使用 ``Finset.prod_pos`` 。
BOTH: -/
-- QUOTE:
theorem primes_infinite' : ∀ s : Finset Nat, ∃ p, Nat.Prime p ∧ p ∉ s := by
  intro s
  by_contra h
  push_neg at h
  set s' := s.filter Nat.Prime with s'_def
  have mem_s' : ∀ {n : ℕ}, n ∈ s' ↔ n.Prime := by
    intro n
    simp [s'_def]
    apply h
  have : 2 ≤ (∏ i in s', i) + 1 := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    apply Nat.succ_le_succ
    apply Nat.succ_le_of_lt
    apply Finset.prod_pos
    intro n ns'
    apply (mem_s'.mp ns').pos
-- BOTH:
  rcases exists_prime_factor this with ⟨p, pp, pdvd⟩
  have : p ∣ ∏ i in s', i := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    apply dvd_prod_of_mem
    rw [mem_s']
    apply pp
-- BOTH:
  have : p ∣ 1 := by
    convert Nat.dvd_sub' pdvd this
    simp
  show False
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  have := Nat.le_of_dvd zero_lt_one this
  linarith [pp.two_le]

-- BOTH:
-- QUOTE.
/- TEXT:
因此，我们看到了两种表述素数有无穷多个的方式：一种是说它们不受任何 ``n`` 的限制，另一种是说它们不在任何有限集合 ``s`` 中。下面的两个证明表明这两种表述是等价的。在第二个证明中，为了形成 ``s.filter Q`` ，我们必须假设存在一个判定 ``Q`` 是否成立的程序。Lean 知道存在一个判定 ``Nat.Prime`` 的程序。一般来说，如果我们通过写 ``open Classical`` 来使用经典逻辑，就可以省去这个假设。
在 Mathlib 中， ``Finset.sup s f`` 表示当 ``x`` 遍历 ``s`` 时 ``f x`` 的上确界，如果 ``s`` 为空且 ``f`` 的值域为 ``ℕ`` ，则返回 ``0`` 。在第一个证明中，我们使用 ``s.sup id``来表示 ``s`` 中的最大值，其中 ``id`` 是恒等函数。
BOTH: -/
-- QUOTE:
theorem bounded_of_ex_finset (Q : ℕ → Prop) :
    (∃ s : Finset ℕ, ∀ k, Q k → k ∈ s) → ∃ n, ∀ k, Q k → k < n := by
  rintro ⟨s, hs⟩
  use s.sup id + 1
  intro k Qk
  apply Nat.lt_succ_of_le
  show id k ≤ s.sup id
  apply le_sup (hs k Qk)

theorem ex_finset_of_bounded (Q : ℕ → Prop) [DecidablePred Q] :
    (∃ n, ∀ k, Q k → k ≤ n) → ∃ s : Finset ℕ, ∀ k, Q k ↔ k ∈ s := by
  rintro ⟨n, hn⟩
  use (range (n + 1)).filter Q
  intro k
  simp [Nat.lt_succ_iff]
  exact hn k
-- QUOTE.

/- TEXT:
对证明存在无穷多个素数的第二种方法稍作修改，即可证明存在无穷多个模 4 余 3 的素数。论证过程如下。
首先，注意到如果两个数 :math:`m` 和 :math:`n` 的乘积模 4 余 3，那么这两个数中必有一个模 4 余 3。毕竟，这两个数都必须是奇数，如果它们都模 4 余 1，那么它们的乘积也模 4 余 1。
利用这一观察结果，我们可以证明，如果某个大于 2 的数模 4 余 3，那么这个数有一个模 4 余 3 的素因数。
现在假设只有有限个形如 4n + 3 的素数，设为 :math:`p_1, \ldots, p_k` 。不失一般性，我们可以假设 :math:`p_1 = 3` 。考虑乘积 :math:`4 \prod_{i = 2}^k p_i + 3` 。显然，这个数除以 4 的余数为 3，所以它有一个形如 4n + 3 的素因数 :math:`p` 。:math:`p` 不可能等于 3；因为 :math:`p` 整除 :math:`4 \prod_{i = 2}^k p_i + 3` ，如果 :math:`p` 等于 3，那么它也会整除 :math:`\prod_{i = 2}^k p_i` ，这意味着 :math:`p` 等于 :math:`p_i` 中的一个（i = 2， ...， k），但我们已将 3 排除在该列表之外。所以 :math:`p` 必须是其他 :math:`p_i` 中的一个。但在这种情况下，:math:`p` 会整除 :math:`4 \prod_{i = 2}^k p_i` 以及 3，这与 :math:`p` 不是 3 这一事实相矛盾。
在 Lean 中，记号 ``n % m`` ，读作 ``n`` 模 ``m`` ，表示 ``n`` 除以 ``m`` 的余数。
EXAMPLES: -/
-- QUOTE:
example : 27 % 4 = 3 := by norm_num
-- QUOTE.

/- TEXT:
然后我们可以将“ ``n`` 除以 4 余 3”这一表述写成 ``n % 4 = 3`` 。下面的示例和定理总结了我们接下来需要用到的关于此函数的事实。第一个命名定理是通过少量情况推理的又一示例。在第二个命名定理中，请记住分号表示后续的策略块应用于前面策略生成的所有目标。
EXAMPLES: -/
-- QUOTE:
example (n : ℕ) : (4 * n + 3) % 4 = 3 := by
  rw [add_comm, Nat.add_mul_mod_self_left]

-- BOTH:
theorem mod_4_eq_3_or_mod_4_eq_3 {m n : ℕ} (h : m * n % 4 = 3) : m % 4 = 3 ∨ n % 4 = 3 := by
  revert h
  rw [Nat.mul_mod]
  have : m % 4 < 4 := Nat.mod_lt m (by norm_num)
  interval_cases m % 4 <;> simp [-Nat.mul_mod_mod]
  have : n % 4 < 4 := Nat.mod_lt n (by norm_num)
  interval_cases n % 4 <;> simp

theorem two_le_of_mod_4_eq_3 {n : ℕ} (h : n % 4 = 3) : 2 ≤ n := by
  apply two_le <;>
    · intro neq
      rw [neq] at h
      norm_num at h
-- QUOTE.

/- TEXT:
我们还需要以下事实，即如果 ``m`` 是 ``n`` 的非平凡因数，那么 ``n / m`` 也是。试着用 ``Nat.div_dvd_of_dvd`` 和 ``Nat.div_lt_self`` 完成证明。
BOTH: -/
-- QUOTE:
theorem aux {m n : ℕ} (h₀ : m ∣ n) (h₁ : 2 ≤ m) (h₂ : m < n) : n / m ∣ n ∧ n / m < n := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  constructor
  · exact Nat.div_dvd_of_dvd h₀
  exact Nat.div_lt_self (lt_of_le_of_lt (zero_le _) h₂) h₁
-- QUOTE.

-- BOTH:
/- TEXT:
现在把所有部分整合起来，证明任何模 4 余 3 的数都有一个具有相同性质的素因数。
BOTH: -/
-- QUOTE:
theorem exists_prime_factor_mod_4_eq_3 {n : Nat} (h : n % 4 = 3) :
    ∃ p : Nat, p.Prime ∧ p ∣ n ∧ p % 4 = 3 := by
  by_cases np : n.Prime
  · use n
  induction' n using Nat.strong_induction_on with n ih
  rw [Nat.prime_def_lt] at np
  push_neg at np
  rcases np (two_le_of_mod_4_eq_3 h) with ⟨m, mltn, mdvdn, mne1⟩
  have mge2 : 2 ≤ m := by
    apply two_le _ mne1
    intro mz
    rw [mz, zero_dvd_iff] at mdvdn
    linarith
  have neq : m * (n / m) = n := Nat.mul_div_cancel' mdvdn
  have : m % 4 = 3 ∨ n / m % 4 = 3 := by
    apply mod_4_eq_3_or_mod_4_eq_3
    rw [neq, h]
  rcases this with h1 | h1
/- EXAMPLES:
  . sorry
  . sorry
SOLUTIONS: -/
  · by_cases mp : m.Prime
    · use m
    rcases ih m mltn h1 mp with ⟨p, pp, pdvd, p4eq⟩
    use p
    exact ⟨pp, pdvd.trans mdvdn, p4eq⟩
  obtain ⟨nmdvdn, nmltn⟩ := aux mdvdn mge2 mltn
  by_cases nmp : (n / m).Prime
  · use n / m
  rcases ih (n / m) nmltn h1 nmp with ⟨p, pp, pdvd, p4eq⟩
  use p
  exact ⟨pp, pdvd.trans nmdvdn, p4eq⟩

-- BOTH:
-- QUOTE.
/- TEXT:
我们已接近尾声。给定一个素数集合 ``s`` ，我们需要讨论从该集合中移除 3（如果存在的话）的结果。函数 ``Finset.erase`` 可以处理这种情况。
EXAMPLES: -/
-- QUOTE:
example (m n : ℕ) (s : Finset ℕ) (h : m ∈ erase s n) : m ≠ n ∧ m ∈ s := by
  rwa [mem_erase] at h

example (m n : ℕ) (s : Finset ℕ) (h : m ∈ erase s n) : m ≠ n ∧ m ∈ s := by
  simp at h
  assumption
-- QUOTE.

/- TEXT:
我们现在准备证明存在无穷多个模 4 余 3 的素数。
请补全下面缺失的部分。
我们的解法会用到 ``Nat.dvd_add_iff_left`` 和 ``Nat.dvd_sub'`` 。
BOTH: -/
-- QUOTE:
theorem primes_mod_4_eq_3_infinite : ∀ n, ∃ p > n, Nat.Prime p ∧ p % 4 = 3 := by
  by_contra h
  push_neg at h
  rcases h with ⟨n, hn⟩
  have : ∃ s : Finset Nat, ∀ p : ℕ, p.Prime ∧ p % 4 = 3 ↔ p ∈ s := by
    apply ex_finset_of_bounded
    use n
    contrapose! hn
    rcases hn with ⟨p, ⟨pp, p4⟩, pltn⟩
    exact ⟨p, pltn, pp, p4⟩
  rcases this with ⟨s, hs⟩
  have h₁ : ((4 * ∏ i in erase s 3, i) + 3) % 4 = 3 := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    rw [add_comm, Nat.add_mul_mod_self_left]
-- BOTH:
  rcases exists_prime_factor_mod_4_eq_3 h₁ with ⟨p, pp, pdvd, p4eq⟩
  have ps : p ∈ s := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    rw [← hs p]
    exact ⟨pp, p4eq⟩
-- BOTH:
  have pne3 : p ≠ 3 := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    intro peq
    rw [peq, ← Nat.dvd_add_iff_left (dvd_refl 3)] at pdvd
    rw [Nat.prime_three.dvd_mul] at pdvd
    norm_num at pdvd
    have : 3 ∈ s.erase 3 := by
      apply mem_of_dvd_prod_primes Nat.prime_three _ pdvd
      intro n
      simp [← hs n]
      tauto
    simp at this
-- BOTH:
  have : p ∣ 4 * ∏ i in erase s 3, i := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    apply dvd_trans _ (dvd_mul_left _ _)
    apply dvd_prod_of_mem
    simp
    constructor <;> assumption
-- BOTH:
  have : p ∣ 3 := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    convert Nat.dvd_sub' pdvd this
    simp
-- BOTH:
  have : p = 3 := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    apply pp.eq_of_dvd_of_prime Nat.prime_three this
-- BOTH:
  contradiction
-- QUOTE.

/- TEXT:
如果您成功完成了证明，恭喜您！这是一项了不起的形式化成就。
TEXT. -/
-- OMIT:
/-
稍后：
o 斐波那契数列
o 二项式系数

（前者是一个存在多个基本情况的典型示例。）

待办事项：在适当的位置提及 ``local attribute`` 。-/
