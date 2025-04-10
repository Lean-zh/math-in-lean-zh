import MIL.Common
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
/- OMIT:
-- 解决这个问题。
-- import Mathlib.Data.Real.Irrational
BOTH: -/

/- TEXT:
.. _section_irrational_roots:

无理数根
--------

让我们从古希腊人已知的一个事实开始，即根号 2 是无理数。如果我们假设并非如此，那么我们可以将根号 2 写成最简分数形式 :math:`\sqrt{2} = a / b` 。两边平方得到 :math:`a^2 = 2 b^2` ，这表明 a 是偶数。如果设 a = 2c ，则有 :math:`4c^2 = 2 b^2` ，从而得出 :math:`b^2 = 2 c^2` 。这表明 b 也是偶数，与我们假设 a / b 已化为最简形式相矛盾。

说 :math:`a / b` 是最简分数意味着 :math:`a` 和 :math:`b` 没有公因数，也就是说，它们是 **互质** 的。
Mathlib 定义谓词 ``Nat.Coprime m n`` 为  ``Nat.gcd m n = 1`` 。
使用 Lean 的匿名投影符号，如果 ``s`` 和 ``t`` 是类型为 ``Nat`` 的表达式，我们可以写 ``s.Coprime t`` 而不是  ``Nat.Coprime s t`` ，对于 ``Nat.gcd`` 也是如此。
和往常一样，Lean 通常会在必要时自动展开 ``Nat.Coprime`` 的定义，但我们也可以通过重写或简化使用标识符 ``Nat.Coprime`` 来手动进行。
 ``norm_num``  策略足够聪明，可以计算出具体的值。
EXAMPLES: -/
-- QUOTE:
#print Nat.Coprime

example (m n : Nat) (h : m.Coprime n) : m.gcd n = 1 :=
  h

example (m n : Nat) (h : m.Coprime n) : m.gcd n = 1 := by
  rw [Nat.Coprime] at h
  exact h

example : Nat.Coprime 12 7 := by norm_num

example : Nat.gcd 12 8 = 4 := by norm_num
-- QUOTE.

/- TEXT:
我们在 :numref:`more_on_order_and_divisibility` 中已经遇到过 `gcd` 函数。对于整数也有一个 `gcd` 版本；我们将在下面讨论不同数系之间的关系。甚至还有适用于一般代数结构类别的通用 `gcd` 函数以及通用的 ``Prime`` 和 ``Coprime`` 概念。在下一章中，我们将了解 Lean 是如何处理这种通用性的。与此同时，在本节中，我们将把注意力限制在自然数上。

我们还需要素数的概念，即 ``Nat.Prime`` 。
定理 ``Nat.prime_def_lt`` 提供了一个常见的特征描述，
而 ``Nat.Prime.eq_one_or_self_of_dvd`` 则提供了另一种。
EXAMPLES: -/
-- QUOTE:
#check Nat.prime_def_lt

example (p : ℕ) (prime_p : Nat.Prime p) : 2 ≤ p ∧ ∀ m : ℕ, m < p → m ∣ p → m = 1 := by
  rwa [Nat.prime_def_lt] at prime_p

#check Nat.Prime.eq_one_or_self_of_dvd

example (p : ℕ) (prime_p : Nat.Prime p) : ∀ m : ℕ, m ∣ p → m = 1 ∨ m = p :=
  prime_p.eq_one_or_self_of_dvd

example : Nat.Prime 17 := by norm_num

-- commonly used
example : Nat.Prime 2 :=
  Nat.prime_two

example : Nat.Prime 3 :=
  Nat.prime_three
-- QUOTE.

/- TEXT:
在自然数中，素数具有不能写成非平凡因数乘积的性质。
在更广泛的数学背景下，具有这种性质的环中的元素被称为 **不可约元** 。
如果一个环中的元素在它整除某个乘积时，就整除其中一个因数，那么这个元素被称为 **素元** 。
自然数的一个重要性质是，在这种情况下这两个概念是重合的，从而产生了定理 ``Nat.Prime.dvd_mul`` 。
我们可以利用这一事实来确立上述论证中的一个关键性质：
如果一个数的平方是偶数，那么这个数本身也是偶数。
Mathlib 在 ``Algebra.Group.Even`` 中定义了谓词 ``Even`` ，但出于下文将要阐明的原因，
我们将简单地使用 ``2 ∣ m`` 来表示 ``m`` 是偶数。
EXAMPLES: -/
-- QUOTE:
#check Nat.Prime.dvd_mul
#check Nat.Prime.dvd_mul Nat.prime_two
#check Nat.prime_two.dvd_mul

-- BOTH:
theorem even_of_even_sqr {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m := by
  rw [pow_two, Nat.prime_two.dvd_mul] at h
  cases h <;> assumption

-- EXAMPLES:
example {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m :=
  Nat.Prime.dvd_of_dvd_pow Nat.prime_two h
-- QUOTE.

/- TEXT:
在接下来的学习过程中，您需要熟练掌握查找所需事实的方法。
请记住，如果您能猜出名称的前缀并且已导入相关库，您可以使用制表符补全（有时需要按 ``Ctrl + Tab`` ）来找到您要查找的内容。
您可以在任何标识符上按 ``Ctrl + 点击`` 跳转到其定义所在的文件，这使您能够浏览附近的定义和定理。
您还可以使用 `Lean 社区网页 <https://leanprover-community.github.io/>`_ 上的搜索引擎，如果其他方法都行不通，不要犹豫，在 `Zulip <https://leanprover.zulipchat.com/>`_ 上提问。
EXAMPLES: -/
-- QUOTE:
example (a b c : Nat) (h : a * b = a * c) (h' : a ≠ 0) : b = c :=
  -- apply? suggests the following:
  (mul_right_inj' h').mp h
-- QUOTE.

/- TEXT:
我们证明根号二为无理数的核心在于以下定理。
试着用 ``even_of_even_sqr`` 和定理 ``Nat.dvd_gcd`` 来完善证明概要。
BOTH: -/
-- QUOTE:
example {m n : ℕ} (coprime_mn : m.Coprime n) : m ^ 2 ≠ 2 * n ^ 2 := by
  intro sqr_eq
  have : 2 ∣ m := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    apply even_of_even_sqr
    rw [sqr_eq]
    apply dvd_mul_right
-- BOTH:
  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp this
  have : 2 * (2 * k ^ 2) = 2 * n ^ 2 := by
    rw [← sqr_eq, meq]
    ring
  have : 2 * k ^ 2 = n ^ 2 :=
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    (mul_right_inj' (by norm_num)).mp this
-- BOTH:
  have : 2 ∣ n := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    apply even_of_even_sqr
    rw [← this]
    apply dvd_mul_right
-- BOTH:
  have : 2 ∣ m.gcd n := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    apply Nat.dvd_gcd <;>
    assumption
-- BOTH:
  have : 2 ∣ 1 := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    convert this
    symm
    exact coprime_mn
-- BOTH:
  norm_num at this
-- QUOTE.

/- TEXT:
实际上，只需稍作改动，我们就可以用任意素数替换 ``2`` 。在下一个示例中试一试。
在证明的最后，您需要从 ``p ∣ 1`` 推导出矛盾。
您可以使用 ``Nat.Prime.two_le`` ，它表明任何素数都大于或等于 2，以及 ``Nat.le_of_dvd`` 。
BOTH: -/
-- QUOTE:
example {m n p : ℕ} (coprime_mn : m.Coprime n) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  intro sqr_eq
  have : p ∣ m := by
    apply prime_p.dvd_of_dvd_pow
    rw [sqr_eq]
    apply dvd_mul_right
  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp this
  have : p * (p * k ^ 2) = p * n ^ 2 := by
    rw [← sqr_eq, meq]
    ring
  have : p * k ^ 2 = n ^ 2 := by
    apply (mul_right_inj' _).mp this
    exact prime_p.ne_zero
  have : p ∣ n := by
    apply prime_p.dvd_of_dvd_pow
    rw [← this]
    apply dvd_mul_right
  have : p ∣ Nat.gcd m n := by apply Nat.dvd_gcd <;> assumption
  have : p ∣ 1 := by
    convert this
    symm
    exact coprime_mn
  have : 2 ≤ 1 := by
    apply prime_p.two_le.trans
    exact Nat.le_of_dvd zero_lt_one this
  norm_num at this
-- QUOTE.

-- BOTH:
/- TEXT:
让我们考虑另一种方法。
这里有一个快速证明：如果 :math:`p` 是质数，那么 :math:`m^2 \ne p n^2` ：假设 :math:`m^2 = p n^2` 并考虑 :math:`m` 和 :math:`n` 分解成质数的情况，那么方程左边 :math:`p` 出现的次数为偶数，而右边为奇数，这与假设相矛盾。
请注意，此论证要求 :math:`n` 以及因此 :math:`m` 不为零。
下面的形式化证明确认了这一假设是足够的。
唯一分解定理指出，除了零以外的任何自然数都可以唯一地表示为素数的乘积。Mathlib 包含此定理的形式化版本，用函数 ``Nat.primeFactorsList`` 来表示，该函数返回一个数的素因数列表，且这些素因数按非递减顺序排列。该库证明了 ``Nat.primeFactorsList n`` 中的所有元素都是素数，任何大于零的 ``n`` 都等于其素因数的乘积，并且如果 ``n`` 等于另一组素数的乘积，那么这组素数就是 ``Nat.primeFactorsList n`` 的一个排列。
EXAMPLES: -/
-- QUOTE:
#check Nat.primeFactorsList
#check Nat.prime_of_mem_primeFactorsList
#check Nat.prod_primeFactorsList
#check Nat.primeFactorsList_unique
-- QUOTE.

/- TEXT:
您可以浏览这些定理以及附近的其他定理，尽管我们尚未讨论列表成员、乘积或排列。
对于当前的任务，我们不需要这些内容。
相反，我们将使用这样一个事实：Mathlib 有一个函数  ``Nat.factorization`` ，它表示与函数相同的数据。
具体来说， ``Nat.factorization n p`` ，我们也可以写成  ``n.factorization p`` ，返回 ``p`` 在 ``n`` 的质因数分解中的重数。我们将使用以下三个事实。
BOTH: -/
-- QUOTE:
theorem factorization_mul' {m n : ℕ} (mnez : m ≠ 0) (nnez : n ≠ 0) (p : ℕ) :
    (m * n).factorization p = m.factorization p + n.factorization p := by
  rw [Nat.factorization_mul mnez nnez]
  rfl

theorem factorization_pow' (n k p : ℕ) :
    (n ^ k).factorization p = k * n.factorization p := by
  rw [Nat.factorization_pow]
  rfl

theorem Nat.Prime.factorization' {p : ℕ} (prime_p : p.Prime) :
    p.factorization p = 1 := by
  rw [prime_p.factorization]
  simp
-- QUOTE.

/- TEXT:
实际上，在 Lean 中， ``n.factorization``  被定义为一个有限支撑的函数，这解释了在您逐步查看上述证明时会看到的奇怪符号。现在不必担心这个问题。就我们此处的目的而言，可以将上述三个定理当作黑箱来使用。
下一个示例表明，化简器足够智能，能够将 ``n^2 ≠ 0`` 替换为 ``n ≠ 0`` 。策略 ``simpa`` 仅调用 ``simp`` 后再调用 ``assumption`` 。
看看你能否利用上面的恒等式来补全证明中缺失的部分。
BOTH: -/
-- QUOTE:
example {m n p : ℕ} (nnz : n ≠ 0) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := by
  intro sqr_eq
  have nsqr_nez : n ^ 2 ≠ 0 := by simpa
  have eq1 : Nat.factorization (m ^ 2) p = 2 * m.factorization p := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    rw [factorization_pow']
-- BOTH:
  have eq2 : (p * n ^ 2).factorization p = 2 * n.factorization p + 1 := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    rw [factorization_mul' prime_p.ne_zero nsqr_nez, prime_p.factorization', factorization_pow',
      add_comm]
-- BOTH:
  have : 2 * m.factorization p % 2 = (2 * n.factorization p + 1) % 2 := by
    rw [← eq1, sqr_eq, eq2]
  rw [add_comm, Nat.add_mul_mod_self_left, Nat.mul_mod_right] at this
  norm_num at this
-- QUOTE.

/- TEXT:
这个证明的一个妙处在于它还能推广。这里的 ``2`` 没有什么特殊之处；稍作改动，该证明就能表明，无论何时我们写出 ``m^k = r * n^k`` ，那么在 ``r`` 中任何素数 ``p`` 的幂次都必须是 ``k`` 的倍数。
要使用 ``Nat.count_factors_mul_of_pos`` 来处理  ``r * n^k`` ，我们需要知道 ``r`` 是正数。但当 ``r`` 为零时，下面的定理是显然成立的，并且很容易通过简化器证明。所以证明是分情况来进行的。 ``rcases r with _ | r``  这一行将目标替换为两个版本：一个版本中 ``r`` 被替换为  ``0`` ，另一个版本中 ``r`` 被替换为  ``r + 1`` 。在第二种情况下，我们可以使用定理  ``r.succ_ne_zero`` ，它表明  ``r + 1 ≠ 0`` （ ``succ``  表示后继）。
还要注意，以 ``have : npow_nz`` 开头的那行提供了 ``n^k ≠ 0`` 的简短证明项证明。
要理解其工作原理，可以尝试用策略证明替换它，然后思考这些策略是如何描述证明项的。
试着补全下面证明中缺失的部分。
在最后，你可以使用 ``Nat.dvd_sub'`` 和 ``Nat.dvd_mul_right`` 来完成证明。
请注意，此示例并未假定 ``p`` 为素数，但当 ``p`` 不是素数时结论是显而易见的，因为根据定义此时 ``r.factorization p`` 为零，而且无论如何该证明在所有情况下都成立。
BOTH: -/
-- QUOTE:
example {m n k r : ℕ} (nnz : n ≠ 0) (pow_eq : m ^ k = r * n ^ k) {p : ℕ} :
    k ∣ r.factorization p := by
  rcases r with _ | r
  · simp
  have npow_nz : n ^ k ≠ 0 := fun npowz ↦ nnz (pow_eq_zero npowz)
  have eq1 : (m ^ k).factorization p = k * m.factorization p := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    rw [factorization_pow']
-- BOTH:
  have eq2 : ((r + 1) * n ^ k).factorization p =
      k * n.factorization p + (r + 1).factorization p := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    rw [factorization_mul' r.succ_ne_zero npow_nz, factorization_pow', add_comm]
-- BOTH:
  have : r.succ.factorization p = k * m.factorization p - k * n.factorization p := by
    rw [← eq1, pow_eq, eq2, add_comm, Nat.add_sub_cancel]
  rw [this]
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  apply Nat.dvd_sub' <;>
  apply Nat.dvd_mul_right
-- BOTH:
-- QUOTE.

/- TEXT:
我们或许想要通过多种方式改进这些结果。首先，关于根号二为无理数的证明应当提及根号二，这可以理解为实数或复数中的一个元素。并且，声称其为无理数应当说明有理数的情况，即不存在任何有理数与之相等。此外，我们应当将本节中的定理推广到整数。尽管从数学角度显而易见，如果能将根号二写成两个整数的商，那么也能写成两个自然数的商，但正式证明这一点仍需付出一定努力。
在 Mathlib 中，自然数、整数、有理数、实数和复数分别由不同的数据类型表示。将注意力限制在不同的域上通常是有帮助的：我们会看到对自然数进行归纳很容易，而且在不考虑实数的情况下，关于整数的可除性进行推理是最简单的。但在不同域之间进行转换是一件令人头疼的事，这是我们必须应对的问题。我们将在本章后面再次讨论这个问题。
我们还应当能够将最后一个定理的结论加强，即表明数字 ``r`` 是 ``k`` 的幂，因为其 ``k`` 次方根恰好是每个整除 ``r`` 的素数的 ``r`` 中该素数的幂次除以 ``k`` 后的乘积。要做到这一点，我们需要更好的方法来处理有限集合上的乘积和求和问题，这也是我们之后会再次探讨的一个主题。
事实上，本节中的所有结果在 Mathlib 的 ``Data.Real.Irrational`` 中都有更广泛的证明。对于任意交换幺半群，都定义了 ``重数（multiplicity）`` 这一概念，其取值范围为扩展自然数 ``enat`` ，即在自然数的基础上增加了无穷大这一值。在下一章中，我们将开始探讨 Lean 如何支持这种泛化的方法。
EXAMPLES: -/
#check multiplicity

-- OMIT: TODO: add when available
-- #check irrational_nrt_of_n_not_dvd_multiplicity

-- #check irrational_sqrt_two

-- OMIT:
-- TODO: use this in the later section and then delete here.
#check Rat.num
#check Rat.den

section
variable (r : ℚ)

#check r.num
#check r.den
#check r.pos
#check r.reduced

end

-- example (r : ℚ) : r ^ 2 ≠ 2 := by
--   rw [← r.num_div_denom, div_pow]
--   have : (r.denom : ℚ) ^ 2 > 0 := by
--     norm_cast
--     apply pow_pos r.pos
--   have := Ne.symm (ne_of_lt this)
--   intro h
--   field_simp [this]  at h
--   norm_cast  at h
--   sorry
