import MIL.Common
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Data.Nat.GCD.Basic

namespace more_induction
/- TEXT:
.. _more_induction:

更多归纳
------------


在 :numref:`section_induction_and_recursion` 中，我们看到了如何在自然数上通过递归定义阶乘函数。

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


没有单引号的 ``induction`` 策略允许更清晰的语法结构
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
As usual, you can hover over the keyword ``induction`` to read the documentation.
The names of the cases ``zero`` , and  ``succ`` , are taken from the definition of the type ℕ.
 Notice that the case ``succ`` allows you to choose whatever names you want for the induction variable and
 the inductive hypothesis, here ``n`` and ``ih`` . You can even prove a theorem with the same notation used to
  define a recursive function. ...

与往常一样，您可以将鼠标悬停在关键词 ``induction`` 上以查看相关文档（？）。
case ``zero`` 和 ``succ`` 的名称源自类型ℕ的定义。
请注意，case ``succ`` 允许您为归纳变量和归纳假设选择任意名称，此处为 ``n`` 和 ``ih`` 。
您甚至可以使用证明递归函数时使用过的符号来证明定理。（？）


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

注意，这里省略了 ``:=`` 。且额外添加了冒号后的 ``∀ n`` 、每一个case 结尾的 ``by`` 以及对 ``fac_pos' n`` 的归纳调用，就好像这个定理是一个 ``n`` 的递归函数，并在归纳步骤中进行了递归调用。
（译注：这个证明与上面相同，但它没有使用 by 引导的策略模式，而是使用了函数式编程风格的模式匹配写法）

This style of definition is remarkably flexible.
Lean’s designers have built in elaborate means of defining recursive functions,
and these extend to doing proofs by induction.
For example, we can define the Fibonacci function with multiple base cases.

这个定义方式极其灵活。Lean的设计者们内置了复杂递归函数的定义方法（？），并且将这些手段扩展到了归纳法。
举个例子，我们可以以多种基础条件定义斐波纳契数列。

BOTH: -/

-- QUOTE:
@[simp] def fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)
-- QUOTE.

/- TEXT:
The ``@[simp]`` annotation means that the simplifier will use the defining equations.
You can also apply them by writing ``rw [fib]`` .
Below it will be helpful to give a name to the ``n + 2`` case.

BOTH: -/

-- QUOTE:
theorem fib_add_two (n : ℕ) : fib (n + 2) = fib n + fib (n + 1) := rfl

example (n : ℕ) : fib (n + 2) = fib n + fib (n + 1) := by rw [fib]
-- QUOTE.
/- TEXT:
Using Lean’s notation for recursive functions, you can carry out proofs by induction on the natural numbers that mirror the recursive definition of . The following example provides an explicit formula for the nth Fibonacci number in terms of the golden mean, , and its conjugate, . We have to tell Lean that we don’t expect our definitions to generate code because the arithmetic operations on the real numbers are not computable.``fib`` ``φ`` ``φ'``
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
Induction proofs involving the Fibonacci function do not have to be of that form. Below we reproduce the proof that consecutive Fibonacci numbers are coprime.``Mathlib``
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
Using Lean’s computational interpretation, we can evaluate the Fibonacci numbers.
BOTH: -/
-- QUOTE:
#eval fib 6
#eval List.range 20 |>.map fib
-- QUOTE.
/- TEXT:
``fib`` ``n``
The straightforward implementation of is computationally inefficient. In fact, it runs in time exponential in its argument. (You should think about why.) In Lean, we can implement the following tail-recursive version, whose running time is linear in , and prove that it computes the same function.

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
``generalizing`` ``fib'.aux_eq`` ``∀`` ``m`` ``m`` ``m + 1``
Notice the keyword in the proof of . It serves to insert a in front of the inductive hypothesis, so that in the induction step, can take a different value. You can step through the proof and check that in this case, the quantifier needs to be instantiated to in the inductive step.

erw rw fib'.aux_eq `fib 0` `fib 1` 0 1 erw rw erw
Notice also the use of (for “extended rewrite”) instead of . This is used because to rewrite the goal , and have to be reduced to and , respectively. The tactic is more aggressive than in unfolding definitions to match parameters. This isn’t always a good idea; it can waste a lot of time in some cases, so use sparingly.

generalizing Mathlib
Here is another example of the keyword in use, in the proof of another identity that is found in . An informal proof of the identity can be found here. We provide two variants of the formal proof.
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
fib_add 代码第二三句似乎多余了（？）
As an exercise, use to prove the following.
BOTH: -/
-- QUOTE:
example (n : ℕ): (fib n) ^ 2 + (fib (n + 1)) ^ 2 = fib (2 * n + 1) := by sorry
example (n : ℕ): (fib n) ^ 2 + (fib (n + 1)) ^ 2 = fib (2 * n + 1) := by
  rw [two_mul, fib_add, pow_two, pow_two]
-- QUOTE.
/- TEXT:
`n ≠ 1` n Nat
Lean’s mechanisms for defining recursive functions are flexible enough to allow arbitrary recursive calls, as long the complexity of the arguments decrease according to some well-founded measure. In the next example, we show that every natural number has a prime divisor, using the fact that if is nonzero and not prime, it has a smaller divisor. (You can check that Mathlib has a theorem of the same name in the namespace, though it has a different proof than the one we give here.)
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
rw ``[ne_one_iff_exists_prime_dvd] at this`` m ``n + 2`` m < n + 2`` n
The line is like a magic trick: we are using the very theorem we are proving in its own proof. What makes it work is that the inductive call is instantiated at , the current case is , and the context has . Lean can find the hypothesis and use it to show that the induction is well-founded. Lean is pretty good at figuring out what is decreasing; in this case, the choice of in the statement of the theorem and the less-than relation is obvious. In more complicated cases, Lean provides mechanisms to provide this information explicitly. See the section on well-founded recursion in the Lean Reference Manual.
n cases rcases
Sometimes, in a proof, you need to split on cases depending on whether a natural number is zero or a successor, without requiring an inductive hypothesis in the successor case. For that, you can use the and tactics.

BOTH: -/
-- QUOTE:
theorem zero_lt_of_mul_eq_one (m n : ℕ) : n * m = 1 → 0 < n ∧ 0 < m := by
  cases n <;> cases m <;> simp

example (m n : ℕ) : n*m = 1 → 0 < n ∧ 0 < m := by
  rcases m with (_ | m); simp
  rcases n with (_ | n) <;> simp
-- QUOTE.
/- TEXT:
n n n ``n + 1``
This is a useful trick. Often you have a theorem about a natural number for which the zero case is easy. If you case on and take care of the zero case quickly, you are left with the original goal with replaced by .
BOTH: -/
