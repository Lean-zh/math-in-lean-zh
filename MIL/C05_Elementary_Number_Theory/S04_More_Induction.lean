import MIL.Common
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Data.Nat.GCD.Basic

namespace more_induction
/- TEXT:
.. _more_induction:

更多归纳
------------


在 :numref:`section_induction_and_recursion` 中，我们看到了如何通过递归在自然数上定义阶乘函数。

EXAMPLES: -/
-- QUOTE:
def fac : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * fac n
-- QUOTE.
/- TEXT:


我们还看到了如何使用 ``induction'`` 策略证明定理。
EXAMPLES: -/
-- QUOTE:
theorem fac_pos (n : ℕ) : 0 < fac n := by
  induction' n with n ih
  · rw [fac]
    exact zero_lt_one
  rw [fac]
  exact mul_pos n.succ_pos ih
-- QUOTE.

/- TEXT:


``induction`` 策略（没有单引号）允许更清晰的语法结构
EXAMPLES: -/
-- QUOTE:
example (n : ℕ) : 0 < fac n := by
  induction n
  case zero =>
    rw [fac]
    exact zero_lt_one
  case succ n ih =>
    rw [fac]
    exact mul_pos n.succ_pos ih

example (n : ℕ) : 0 < fac n := by
  induction n with
  | zero =>
    rw [fac]
    exact zero_lt_one
  | succ n ih =>
    rw [fac]
    exact mul_pos n.succ_pos ih
-- QUOTE.
/- TEXT:

你可以将鼠标悬停在 ``induction`` 或其它关键词上以查看相关文档说明。
case ``zero`` 和 ``succ`` 的名称源自类型ℕ的定义。
请注意，case ``succ`` 允许将归纳变量和归纳假设随意命名，此处命名为 ``n`` 和 ``ih`` 。
你甚至可以使用证明递归函数时使用过的符号来证明其它定理。


BOTH: -/
-- QUOTE:
theorem fac_pos' : ∀ n, 0 < fac n
  | 0 => by
    rw [fac]
    exact zero_lt_one
  | n + 1 => by
    rw [fac]
    exact mul_pos n.succ_pos (fac_pos' n)
-- QUOTE.
/- TEXT:

注意，这里省略了 ``:=`` ，且额外添加了冒号后的 ``∀ n`` 、每一个case 结尾的 ``by`` 以及对 ``fac_pos' n`` 的归纳调用，就好像这个定理是一个 ``n`` 的递归函数，并在归纳步骤中进行了递归调用。
（译注：这个证明与上面相同，但它没有使用 by 引导的策略模式，而是使用了函数式编程风格的模式匹配写法）


这个定义方式极其灵活。Lean的设计者们内置了复杂的递归函数定义方法，并且将这些手段扩展到了归纳证明。
举个例子，我们可以以多种基础情形来定义斐波纳契数列。

BOTH: -/

-- QUOTE:
@[simp] def fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)
-- QUOTE.

/- TEXT:


@[simp] 注解表示化简器会自动使用这些定义方程。
也可以通过 `rw [fib]` 手动应用这些方程。
推荐为 ``n + 2`` 的情况命名。

BOTH: -/

-- QUOTE:
theorem fib_add_two (n : ℕ) : fib (n + 2) = fib n + fib (n + 1) := rfl

example (n : ℕ) : fib (n + 2) = fib n + fib (n + 1) := by rw [fib]
-- QUOTE.
/- TEXT:

我们可以使用 Lean 的递归函数定义方式，对自然数进行归纳证明，且这些证明与 ``fib`` 的递归定义相对应。
以下示例通过黄金分割比例 ``φ`` 及其共轭 ``φ'`` 给出斐波那契数的通项公式。
但由于实数运算不可计算，我们需要声明这些定义属于不可计算范畴（即用 ``noncomputable section`` 声明）。

BOTH: -/
-- QUOTE:
noncomputable section

def phi  : ℝ := (1 + √5) / 2
def phi' : ℝ := (1 - √5) / 2

theorem phi_sq : phi^2 = phi + 1 := by
  field_simp [phi, add_sq]; ring

theorem phi'_sq : phi'^2 = phi' + 1 := by
  field_simp [phi', sub_sq]; ring

theorem fib_eq : ∀ n, fib n = (phi^n - phi'^n) / √5
  | 0   => by simp
  | 1   => by field_simp [phi, phi']
  | n+2 => by field_simp [fib_eq, pow_add, phi_sq, phi'_sq]; ring

end
-- QUOTE.
/- TEXT:

涉及斐波那契函数的归纳证明不必采用上面形式，如 ``Mathlib`` 中的写法。
下面我们重现了证明：相邻斐波那契数列互质。

BOTH: -/
-- QUOTE:
theorem fib_coprime_fib_succ (n : ℕ) : Nat.Coprime (fib n) (fib (n + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [fib, Nat.coprime_add_self_right]
    exact ih.symm
-- QUOTE.
/- TEXT:

通过Lean的计算语义，我们可以直接求得斐波那契数列。

BOTH: -/
-- QUOTE:
#eval fib 6
#eval List.range 20 |>.map fib
-- QUOTE.
/- TEXT:

用 ``fib`` 实现的斐波那契函数的效率低下，其时间复杂度呈指数级（你可以思考一下为什么是指数级）。
在Lean中，我们可以实现如下尾递归版本：
其运行时间与 ``n`` 成线性关系（即 ``O(n)`` 复杂度），并证明其与原始定义等价。

BOTH: -/
-- QUOTE:
def fib' (n : Nat) : Nat :=
  aux n 0 1
where aux
  | 0,   x, _ => x
  | n+1, x, y => aux n y (x + y)

theorem fib'.aux_eq (m n : ℕ) : fib'.aux n (fib m) (fib (m + 1)) = fib (n + m) := by
  induction n generalizing m with
  | zero => simp [fib'.aux]
  | succ n ih => rw [fib'.aux, ←fib_add_two, ih, add_assoc, add_comm 1]

theorem fib'_eq_fib : fib' = fib := by
  ext n
  erw [fib', fib'.aux_eq 0 n]; rfl

#eval fib' 10000
-- QUOTE.
/- TEXT:

请注意在 ``fib'.aux_eq`` 的证明中使用了 ``generalizing`` 关键字。
它的作用是在归纳假设前插入一个 ``∀ m`` ，这样在归纳步骤中，``m`` 可以取不同的值。
逐步检查这个证明，可以发现此时量词确实需要在归纳步骤中实例化为 ``m + 1`` 。

还要注意这里使用了 ``erw``（表示“扩展重写”，extended rewrite）而不是 ``rw`` 。
这是因为为了重写目标 ``fib'_eq_fib`` ，
需要将 ``fib'`` 和 ``fib`` 分别化简为 ``fib'.aux 0 1`` 和 ``fib n`` 。
该策略在展开定义以匹配参数时比 ``rw`` 更激进。但这有时效果很差；甚至会浪费大量时间，因此应谨慎使用。

下面是另一个 ``generalizing`` 关键字的例子，出现在 ``Mathlib`` 中另一个恒等式的证明里。
该恒等式的非形式化证明可以在 `这里 <https://proofwiki.org/wiki/Fibonacci_Number_in_terms_of_Smaller_Fibonacci_NumbersLean>`_ 找到。
下面我们给出两种形式化证明。

BOTH: -/
-- QUOTE:
theorem fib_add (m n : ℕ) : fib (m + n + 1) = fib m * fib n + fib (m + 1) * fib (n + 1) := by
  induction n generalizing m with
  | zero => simp
  | succ n ih =>
    specialize ih (m + 1)
    rw [add_assoc m 1 n, add_comm 1 n] at ih
    simp only [fib_add_two, Nat.succ_eq_add_one, ih]
    ring

theorem fib_add' : ∀ m n, fib (m + n + 1) = fib m * fib n + fib (m + 1) * fib (n + 1)
  | _, 0     => by simp
  | m, n + 1 => by
    have := fib_add' (m + 1) n
    rw [add_assoc m 1 n, add_comm 1 n] at this
    simp only [fib_add_two, Nat.succ_eq_add_one, this]
    ring
-- QUOTE.
/- TEXT:
使用 ``fib_add`` 证明下列等式作为练习。
BOTH: -/
-- QUOTE:
example (n : ℕ): (fib n) ^ 2 + (fib (n + 1)) ^ 2 = fib (2 * n + 1) := by sorry
example (n : ℕ): (fib n) ^ 2 + (fib (n + 1)) ^ 2 = fib (2 * n + 1) := by
  rw [two_mul, fib_add, pow_two, pow_two]
-- QUOTE.
/- TEXT:
Lean 定义递归函数的机制非常灵活，只要参数的复杂度按照某种良基度量递减，就允许任意递归调用。
在下一个例子中，我们将利用“只要 ``n`` 不为零且不是素数，那么它一定有一个更小的因子”这一事实，
来证明每个自然数 ``n ≠ 1`` 都有一个素因子（你可以在 Mathlib 的 ``Nat`` 命名空间中找到同名定理，
不过证明方法和这里不同）。
BOTH: -/
-- QUOTE:
#check (@Nat.not_prime_iff_exists_dvd_lt :
  ∀ {n : ℕ}, 2 ≤ n → (¬Nat.Prime n ↔ ∃ m, m ∣ n ∧ 2 ≤ m ∧ m < n))

theorem ne_one_iff_exists_prime_dvd : ∀ {n}, n ≠ 1 ↔ ∃ p : ℕ, p.Prime ∧ p ∣ n
  | 0 => by simpa using Exists.intro 2 Nat.prime_two
  | 1 => by simp [Nat.not_prime_one]
  | n + 2 => by
    have hn : n+2 ≠ 1 := by omega
    simp only [Ne, not_false_iff, true_iff, hn]
    by_cases h : Nat.Prime (n + 2)
    · use n+2, h
    · have : 2 ≤ n + 2 := by omega
      rw [Nat.not_prime_iff_exists_dvd_lt this] at h
      rcases h with ⟨m, mdvdn, mge2, -⟩
      have : m ≠ 1 := by omega
      rw [ne_one_iff_exists_prime_dvd] at this
      rcases this with ⟨p, primep, pdvdm⟩
      use p, primep
      exact pdvdm.trans mdvdn
-- QUOTE.
/- TEXT:

 ``rw [ne_one_iff_exists_prime_dvd] at this`` 这一行就像黑魔法一样：在证明自身时用到了正在证明的定理本身。
 这种用法之所以可行，是因为归纳调用实例化在 ``m`` 上，当前 case 是 ``n + 2`` ，且上下文中有 ``m < n + 2`` 。Lean 能自动找到假设并据此判定归纳是良基的。
 Lean 很擅长判断递减量；在本例中，定理语句中的 `n` 和小于关系很明显。在更复杂的情况下，Lean 还提供了一些机制让你显式指定递减量。详见 Lean Reference Manual关于 ``良基递归 <https://lean-lang.org/doc/reference/latest//Definitions/Recursive-Definitions/#well-founded-recursion>``_ 的章节。
有时在证明中，你需要根据一个自然数 ``n`` 是 0 还是后继数来分类，但在后继情形下并不需要归纳假设。此时可以用 ``cases`` 和 ``rcases`` 策略。
BOTH: -/
-- QUOTE:
theorem zero_lt_of_mul_eq_one (m n : ℕ) : n * m = 1 → 0 < n ∧ 0 < m := by
  cases n <;> cases m <;> simp

example (m n : ℕ) : n*m = 1 → 0 < n ∧ 0 < m := by
  rcases m with (_ | m); simp
  rcases n with (_ | n) <;> simp
-- QUOTE.
/- TEXT:
这是一个很实用的小技巧。很多时候你要证明关于自然数 ``n`` 的命题，其中 ``n=0`` 的情况很简单。如果你先对 ``n`` 分类并快速解决 ``n=0`` 的情况，剩下的目标就会自动变成 ``n + 1`` 的情况。

BOTH: -/
