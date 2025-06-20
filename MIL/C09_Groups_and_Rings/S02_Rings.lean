-- BOTH:
-- import Mathlib.RingTheory.Ideal.QuotientOperations
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.ZMod.Quotient
import MIL.Common

noncomputable section

/- TEXT:
.. _rings:

环
-----

.. index:: ring (algebraic structure)

环、环上的单位元、态射和子环
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

类型 ``R`` 上环结构的类型是 ``Ring R``。乘法交换的变体为 ``CommRing R``。
我们已经看到，``ring`` 策略会证明任何基于交换环公理的等式。
EXAMPLES: -/
-- QUOTE:
example {R : Type*} [CommRing R] (x y : R) : (x + y) ^ 2 = x ^ 2 + y ^ 2 + 2 * x * y := by ring
-- QUOTE.

/- TEXT:
更为奇特的变体不要求 ``R`` 上的加法形成群，而仅需是加法幺半群。对应的类型类是 ``Semiring R`` 和 ``CommSemiring R``。

自然数类型是 ``CommSemiring R`` 的一个重要实例，任何以自然数为值的函数类型也是如此。
另一个重要的例子是环中的理想的类型，这将在下面讨论。

``ring`` 策略的名称是双重误导性的，因为它假设了交换性，但也适用于半环。换句话说，它适用于任何 ``CommSemiring``。

EXAMPLES: -/
-- QUOTE:
example (x y : ℕ) : (x + y) ^ 2 = x ^ 2 + y ^ 2 + 2 * x * y := by ring
-- QUOTE.

/- TEXT:
还有一些环类和半环类的变体不假设乘法单位元的存在或乘法的结合性。我们在这里不讨论这些。

某些传统上在环论入门中教授的概念实际上是关于底层乘法幺半群的。
一个突出的例子是环的单位元的定义。每个（乘法）幺半群 ``M`` 都有一个谓词 ``IsUnit : M → Prop``，用来断言存在双边逆元，一个类型 ``Units M`` 表示单位元，并用记号 ``Mˣ`` 表示，以及到 ``M`` 的强制转换。
类型 ``Units M`` 将一个可逆元素与其逆元以及确保它们彼此互为逆元的性质一起打包。
此实现细节主要与定义可计算函数相关。在大多数情况下，可以使用 ``IsUnit.unit {x : M} : IsUnit x → Mˣ`` 构造一个单位元。
在交换情况下，还可以使用 ``Units.mkOfMulEqOne (x y : M) : x * y = 1 → Mˣ`` 构造 ``x`` 作为单位元。
EXAMPLES: -/
-- QUOTE:
example (x : ℤˣ) : x = 1 ∨ x = -1 := Int.units_eq_one_or x

example {M : Type*} [Monoid M] (x : Mˣ) : (x : M) * x⁻¹ = 1 := Units.mul_inv x

example {M : Type*} [Monoid M] : Group Mˣ := inferInstance
-- QUOTE.

/- TEXT:
两个（半）环 ``R`` 和 ``S`` 之间环态射的类型是 ``RingHom R S``，记号为 ``R →+* S``。
EXAMPLES: -/
-- QUOTE:
example {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (x y : R) :
    f (x + y) = f x + f y := f.map_add x y

example {R S : Type*} [Ring R] [Ring S] (f : R →+* S) : Rˣ →* Sˣ :=
  Units.map f
-- QUOTE.

/- TEXT:
同构的变体是 ``RingEquiv``，记号为 ``≃+*``。

与子幺半群和子群类似，环 ``R`` 的子环有一个类型 ``Subring R``，但这个类型远不如子群类型有用，因为环不能通过子环进行商构造。

EXAMPLES: -/
-- QUOTE:
example {R : Type*} [Ring R] (S : Subring R) : Ring S := inferInstance
-- QUOTE.

/- TEXT:
值得注意的是，``RingHom.range`` 产生一个子环。

理想与商
^^^^^^^^^^^^^^^^^^^^

由于历史原因，Mathlib 仅为交换环提供了理想的理论。
（环库最初的开发是为了快速推进现代代数几何的基础。）因此，在本节中我们将讨论交换（半）环。
``R`` 的理想被定义为将 ``R`` 视为 ``R``-模的子模。模将在线性代数的章节中讨论，但这一实现细节基本上可以安全忽略，因为大多数（但不是全部）相关引理都已在理想的特殊背景中重新叙述。但是匿名投影记号并不总是像预期的那样工作。例如，不能将 ``Ideal.Quotient.mk I`` 替换为 ``I.Quotient.mk``，因为下面的代码片段中有两个 ``.``，因此它会被解析为 ``(Ideal.Quotient I).mk``；但单独的 ``Ideal.Quotient`` 并不存在。

EXAMPLES: -/
-- QUOTE:
example {R : Type*} [CommRing R] (I : Ideal R) : R →+* R ⧸ I :=
  Ideal.Quotient.mk I

example {R : Type*} [CommRing R] {a : R} {I : Ideal R} :
    Ideal.Quotient.mk I a = 0 ↔ a ∈ I :=
  Ideal.Quotient.eq_zero_iff_mem
-- QUOTE.

/- TEXT:
商环的整体性质是 ``Ideal.Quotient.lift``。
EXAMPLES: -/
-- QUOTE:
example {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (f : R →+* S)
    (H : I ≤ RingHom.ker f) : R ⧸ I →+* S :=
  Ideal.Quotient.lift I f H
-- QUOTE.

/- TEXT:
特别的，其导出了环的第一同构定理。
EXAMPLES: -/
-- QUOTE:
example {R S : Type*} [CommRing R] [CommRing S](f : R →+* S) :
    R ⧸ RingHom.ker f ≃+* f.range :=
  RingHom.quotientKerEquivRange f
-- QUOTE.

/- TEXT:
理想在包含关系下形成一个完备格结构，同时也具有半环结构。这两个结构相互作用良好。
EXAMPLES: -/
section
-- QUOTE:
variable {R : Type*} [CommRing R] {I J : Ideal R}

-- EXAMPLES:
example : I + J = I ⊔ J := rfl

example {x : R} : x ∈ I + J ↔ ∃ a ∈ I, ∃ b ∈ J, a + b = x := by
  simp [Submodule.mem_sup]

example : I * J ≤ J := Ideal.mul_le_left

example : I * J ≤ I := Ideal.mul_le_right

example : I * J ≤ I ⊓ J := Ideal.mul_le_inf
-- QUOTE.

end

/- TEXT:
可以使用环态射分别通过 ``Ideal.map`` 和 ``Ideal.comap`` 将理想前推（push forward）或拉回（pull back）。
通常情况下，后者更方便使用，因为它不涉及存在量词。这也解释了为何它被用来表达构造商环之间态射的条件。
EXAMPLES: -/
-- QUOTE:
example {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (H : I ≤ Ideal.comap f J) : R ⧸ I →+* S ⧸ J :=
  Ideal.quotientMap J f H
-- QUOTE.

/- TEXT:
一个需要注意的细微点是，类型 ``R ⧸ I`` 实际上依赖于 ``I``（在定义等同的范围内），因此证明两个理想 ``I`` 和 ``J`` 相等并不足以使相应的商环相等。然而，在这种情况下，整体性质确实提供了一个同构。
EXAMPLES: -/
-- QUOTE:
example {R : Type*} [CommRing R] {I J : Ideal R} (h : I = J) : R ⧸ I ≃+* R ⧸ J :=
  Ideal.quotEquivOfEq h
-- QUOTE.

/- TEXT:
我们现在可以将中国剩余定理的同构作为一个示例呈现。请注意，索引下确界符号 ``⨅`` 与类型大乘积符号 ``Π`` 的区别。取决于你的字体，它们可能很难区分。
EXAMPLES: -/
-- QUOTE:
example {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] (f : ι → Ideal R)
    (hf : ∀ i j, i ≠ j → IsCoprime (f i) (f j)) : (R ⧸ ⨅ i, f i) ≃+* Π i, R ⧸ f i :=
  Ideal.quotientInfRingEquivPiQuotient f hf
-- QUOTE.

/- TEXT:
初等版本的中国剩余定理（关于 ``ZMod`` 的表述）可以轻松地从前述定理推导出来：
BOTH: -/
-- QUOTE:
open BigOperators PiNotation

-- EXAMPLES:
example {ι : Type*} [Fintype ι] (a : ι → ℕ) (coprime : ∀ i j, i ≠ j → (a i).Coprime (a j)) :
    ZMod (∏ i, a i) ≃+* Π i, ZMod (a i) :=
  ZMod.prodEquivPi a coprime
-- QUOTE.

/- TEXT:
作为一系列练习，我们将在一般情况下重新证明中国剩余定理。

我们首先需要定义定理中出现的映射，作为一个环态射，利用商环的整体性质。
BOTH: -/
section
-- QUOTE:
variable {ι R : Type*} [CommRing R]
open Ideal Quotient Function

#check Pi.ringHom
#check ker_Pi_Quotient_mk

/-- 从 ``R ⧸ ⨅ i, I i`` 到 ``Π i, R ⧸ I i`` 的同态映射，该映射在中国剩余定理中出现。 -/
def chineseMap (I : ι → Ideal R) : (R ⧸ ⨅ i, I i) →+* Π i, R ⧸ I i :=
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  Ideal.Quotient.lift (⨅ i, I i) (Pi.ringHom fun i : ι ↦ Ideal.Quotient.mk (I i))
    (by simp [← RingHom.mem_ker, ker_Pi_Quotient_mk])
-- QUOTE.
-- BOTH:

/- TEXT:
确保以下两个引理可以通过 ``rfl`` 证明。
BOTH: -/
-- QUOTE:
lemma chineseMap_mk (I : ι → Ideal R) (x : R) :
    chineseMap I (Quotient.mk _ x) = fun i : ι ↦ Ideal.Quotient.mk (I i) x :=
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  rfl
-- BOTH:

lemma chineseMap_mk' (I : ι → Ideal R) (x : R) (i : ι) :
    chineseMap I (mk _ x) i = mk (I i) x :=
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  rfl
-- QUOTE.
-- BOTH:

/- TEXT:
下一个引理证明了中国剩余定理的简单部分，对于理想族没有任何假设。该证明不到一行即可完成。
EXAMPLES: -/
-- QUOTE:
#check injective_lift_iff

-- BOTH:
lemma chineseMap_inj (I : ι → Ideal R) : Injective (chineseMap I) := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  rw [chineseMap, injective_lift_iff, ker_Pi_Quotient_mk]
-- QUOTE.
-- BOTH:

/- TEXT:
我们现在准备进入定理的核心部分，它将展示我们的 ``chineseMap`` 的满射性。
首先，我们需要了解几种表达互素性（也称为互为最大假设 co-maximality assumption ）的方法。以下仅需要使用前两种表达方式。
EXAMPLES: -/
-- QUOTE:
#check IsCoprime
#check isCoprime_iff_add
#check isCoprime_iff_exists
#check isCoprime_iff_sup_eq
#check isCoprime_iff_codisjoint
-- QUOTE.

/- TEXT:
我们借此机会对 ``Finset`` 使用归纳法。以下列出了关于 ``Finset`` 的相关引理。
请记住，``ring`` 策略适用于半环，并且环的理想构成一个半环。
EXAMPLES: -/
-- QUOTE:
#check Finset.mem_insert_of_mem
#check Finset.mem_insert_self

-- BOTH:
theorem isCoprime_Inf {I : Ideal R} {J : ι → Ideal R} {s : Finset ι}
    (hf : ∀ j ∈ s, IsCoprime I (J j)) : IsCoprime I (⨅ j ∈ s, J j) := by
  classical
  simp_rw [isCoprime_iff_add] at *
  induction s using Finset.induction with
  | empty =>
      simp
  | @insert i s _ hs =>
      rw [Finset.iInf_insert, inf_comm, one_eq_top, eq_top_iff, ← one_eq_top]
      set K := ⨅ j ∈ s, J j
      calc
/- EXAMPLES:
        1 = I + K                  := sorry
        _ = I + K * (I + J i)      := sorry
        _ = (1 + K) * I + K * J i  := sorry
        _ ≤ I + K ⊓ J i            := sorry
SOLUTIONS: -/
        1 = I + K                  := (hs fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)).symm
        _ = I + K * (I + J i)      := by rw [hf i (Finset.mem_insert_self i s), mul_one]
        _ = (1 + K) * I + K * J i  := by ring
        _ ≤ I + K ⊓ J i            := by gcongr ; apply mul_le_left ; apply mul_le_inf

-- QUOTE.

/- TEXT:
我们现在可以证明在中国剩余定理中出现的映射的满射性。
BOTH: -/
-- QUOTE:
lemma chineseMap_surj [Fintype ι] {I : ι → Ideal R}
    (hI : ∀ i j, i ≠ j → IsCoprime (I i) (I j)) : Surjective (chineseMap I) := by
  classical
  intro g
  choose f hf using fun i ↦ Ideal.Quotient.mk_surjective (g i)
  have key : ∀ i, ∃ e : R, mk (I i) e = 1 ∧ ∀ j, j ≠ i → mk (I j) e = 0 := by
    intro i
    have hI' : ∀ j ∈ ({i} : Finset ι)ᶜ, IsCoprime (I i) (I j) := by
/- EXAMPLES:
      sorry
SOLUTIONS: -/
      intros j hj
      exact hI _ _ (by simpa [ne_comm, isCoprime_iff_add] using hj)
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    rcases isCoprime_iff_exists.mp (isCoprime_Inf hI') with ⟨u, hu, e, he, hue⟩
    replace he : ∀ j, j ≠ i → e ∈ I j := by simpa using he
    refine ⟨e, ?_, ?_⟩
    · simp [eq_sub_of_add_eq' hue, map_sub, eq_zero_iff_mem.mpr hu]
    · exact fun j hj ↦ eq_zero_iff_mem.mpr (he j hj)
-- BOTH:
  choose e he using key
  use mk _ (∑ i, f i * e i)
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  ext i
  rw [chineseMap_mk', map_sum, Fintype.sum_eq_single i]
  · simp [(he i).1, hf]
  · intros j hj
    simp [(he j).2 i hj.symm]
-- QUOTE.
-- BOTH:

/- TEXT:
将这些部分结合起来：
BOTH: -/
-- QUOTE:
noncomputable def chineseIso [Fintype ι] (f : ι → Ideal R)
    (hf : ∀ i j, i ≠ j → IsCoprime (f i) (f j)) : (R ⧸ ⨅ i, f i) ≃+* Π i, R ⧸ f i :=
  { Equiv.ofBijective _ ⟨chineseMap_inj f, chineseMap_surj hf⟩,
    chineseMap f with }
-- QUOTE.

end

/- TEXT:
代数与多项式
^^^^^^^^^^^^^^^^^^^^^^^^

给定一个交换（半）环 ``R``，一个 ``R`` 上的 *代数* (algebra) ``R`` 是一个半环 ``A``，其配备了一个环态射，其像与 ``A`` 的每个元素可交换。这被编码为一个类型类 ``Algebra R A``。
从 ``R`` 到 ``A`` 的态射称为结构映射，并在 Lean 中记作 ``algebraMap R A : R →+* A``。
对某个 ``r : R``，将 ``a : A`` 与 ``algebraMap R A r`` 相乘被称为 ``a`` 被 ``r`` 的标量乘法，记为 ``r • a``。
请注意，这种代数的概念有时称为 *结合幺代数* (associative unital algebra)，以强调存在更一般的代数概念。

``algebraMap R A`` 是一个环态射的事实打包了许多标量乘法的性质，例如以下内容：
EXAMPLES: -/
-- QUOTE:
example {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (r r' : R) (a : A) :
    (r + r') • a = r • a + r' • a :=
  add_smul r r' a

example {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (r r' : R) (a : A) :
    (r * r') • a = r • r' • a :=
  mul_smul r r' a
-- QUOTE.

/- TEXT:
``R``-代数 ``A`` 和 ``B`` 之间的态射是环态射，它们与 ``R`` 元素的标量乘法可交换。它们是具有类型 ``AlgHom R A B`` 的打包态射，记号为 ``A →ₐ[R] B``。

非交换代数的重要示例包括自同态代数和方阵代数，这两个将在线性代数一章中讨论。
在本章中，我们将讨论最重要的交换代数之一，即多项式代数。

系数在 ``R`` 中的一元多项式代数称为 ``Polynomial R``，当打开 ``Polynomial`` 命名空间时，它可以写作 ``R[X]``。
从 ``R`` 到 ``R[X]`` 的代数结构映射记为 ``C``，它表示 “常数”，因为相应的多项式函数始终是常数。
未定元记为 ``X``。
EXAMPLES: -/
section Polynomials
-- QUOTE:
open Polynomial

example {R : Type*} [CommRing R] : R[X] := X

example {R : Type*} [CommRing R] (r : R) := X - C r
-- QUOTE.

/- TEXT:
在上面的第一个示例中，至关重要的是要为 Lean 提供预期的类型，因为它无法从定义的主体中推断出来。在第二个示例中，目标多项式代数可以通过我们对 ``C r`` 的使用推断出来，因为已知 ``r`` 的类型。

由于 ``C`` 是从 ``R`` 到 ``R[X]`` 的环态射，我们可以在 ``R[X]`` 环中计算之前，使用所有环态射引理，例如 ``map_zero``、``map_one``、``map_mul`` 和 ``map_pow``。例如：
EXAMPLES: -/
-- QUOTE:
example {R : Type*} [CommRing R] (r : R) : (X + C r) * (X - C r) = X ^ 2 - C (r ^ 2) := by
  rw [C.map_pow]
  ring
-- QUOTE.

/- TEXT:
可以用 ``Polynomial.coeff`` 获取系数
EXAMPLES: -/
-- QUOTE:
example {R : Type*} [CommRing R] (r:R) : (C r).coeff 0 = r := by simp

example {R : Type*} [CommRing R] : (X ^ 2 + 2 * X + C 3 : R[X]).coeff 1 = 2 := by simp
-- QUOTE.

/- TEXT:
定义多项式的次数总是比较棘手，因为零多项式是一个特殊情况。Mathlib 有两个变体：
``Polynomial.natDegree : R[X] → ℕ`` 将零多项式的次数指定为 ``0``，而 ``Polynomial.degree : R[X] → WithBot ℕ`` 将其指定为 ``⊥``。

在后者中，``WithBot ℕ`` 可以视为 ``ℕ ∪ {-∞}``，只不过 ``-∞`` 被表示为 ``⊥``，与完备格中的底元素同一个符号。
此特殊值用于零多项式的次数，并且在加法中是吸收元。（在乘法中它几乎是吸收元，但 ``⊥ * 0 = 0`` 除外。）

理论而言，``degree`` 版本是正确的那一个。例如，它允许我们陈述关于乘积次数的预期公式（假设基环没有零因子）。
EXAMPLES: -/
-- QUOTE:
example {R : Type*} [Semiring R] [NoZeroDivisors R] {p q : R[X]} :
    degree (p * q) = degree p + degree q :=
  Polynomial.degree_mul
-- QUOTE.

/- TEXT:
而对于 ``natDegree`` 的版本，则需要假设多项式非零。
EXAMPLES: -/
-- QUOTE:
example {R : Type*} [Semiring R] [NoZeroDivisors R] {p q : R[X]} (hp : p ≠ 0) (hq : q ≠ 0) :
    natDegree (p * q) = natDegree p + natDegree q :=
  Polynomial.natDegree_mul hp hq
-- QUOTE.

/- TEXT:
然而，``ℕ`` 的使用要比 ``WithBot ℕ`` 更友好，因此 Mathlib 提供了这两种版本并提供了在它们之间转换的引理。此外，当计算复合多项式的次数时，``natDegree`` 是更方便的定义。多项式的复合是 ``Polynomial.comp``，我们有：
EXAMPLES: -/
-- QUOTE:
example {R : Type*} [Semiring R] [NoZeroDivisors R] {p q : R[X]} :
    natDegree (comp p q) = natDegree p * natDegree q :=
  Polynomial.natDegree_comp
-- QUOTE.

/- TEXT:
多项式产生多项式函数：任何多项式都可以通过 ``Polynomial.eval`` 在 ``R`` 上进行求值。
EXAMPLES: -/
-- QUOTE:
example {R : Type*} [CommRing R] (P: R[X]) (x : R) := P.eval x

example {R : Type*} [CommRing R] (r : R) : (X - C r).eval r = 0 := by simp
-- QUOTE.

/- TEXT:
特别地，有一个谓词 ``IsRoot``，它用于表示当一个多项式在 ``R`` 中的某些元素 ``r`` 处取零时成立。
EXAMPLES: -/
-- QUOTE:
example {R : Type*} [CommRing R] (P : R[X]) (r : R) : IsRoot P r ↔ P.eval r = 0 := Iff.rfl
-- QUOTE.

/- TEXT:
我们希望能够说明，在假设 ``R`` 没有零因子的情况下，一个多项式的根（按重数计算）最多不超过其次数。然而，零多项式的情况再次变得麻烦。

因此，Mathlib 定义了 ``Polynomial.roots``，它将一个多项式 ``P`` 映射到一个多重集合（multiset），即：
- 如果 ``P`` 为零多项式，该集合被定义为空集；
- 否则，该集合为 ``P`` 的根，并记录其重数。

此定义仅适用于底层环是整域的情况，因为在其他情况下，该定义不具有良好的性质。
EXAMPLES: -/
-- QUOTE:
example {R : Type*} [CommRing R] [IsDomain R] (r : R) : (X - C r).roots = {r} :=
  roots_X_sub_C r

example {R : Type*} [CommRing R] [IsDomain R] (r : R) (n : ℕ):
    ((X - C r) ^ n).roots = n • {r} :=
  by simp
-- QUOTE.

/- TEXT:
``Polynomial.eval`` 和 ``Polynomial.roots`` 都仅考虑系数环。它们不能让我们说明 ``X ^ 2 - 2 : ℚ[X]`` 在 ``ℝ`` 中有根，或 ``X ^ 2 + 1 : ℝ[X]`` 在 ``ℂ`` 中有根。为此，我们需要 ``Polynomial.aeval``，它可以在任意 ``R``-代数中对 ``P : R[X]`` 进行求值。

更具体地说，给定一个半环 ``A`` 和 ``Algebra R A`` 的实例，``Polynomial.aeval`` 会沿着在元素 ``a`` 处的 ``R``-代数态射将多项式的每个元素发送出去。由于 ``AlgHom`` 可以强制转换为函数，因此可以将其应用于多项式。

但 ``aeval`` 并没有一个多项式作为参数，因此不能像在上面使用 ``P.eval`` 那样使用点符号表示法。
EXAMPLES: -/
-- QUOTE:
example : aeval Complex.I (X ^ 2 + 1 : ℝ[X]) = 0 := by simp

-- QUOTE.
/- TEXT:
在这种情况下，与 ``roots`` 对应的函数是 ``aroots``，它接受一个多项式和一个代数，并输出一个多重集合（关于零多项式的警告与 ``roots`` 相同）。
EXAMPLES: -/
-- QUOTE:
open Complex Polynomial

example : aroots (X ^ 2 + 1 : ℝ[X]) ℂ = {Complex.I, -I} := by
  suffices roots (X ^ 2 + 1 : ℂ[X]) = {I, -I} by simpa [aroots_def]
  have factored : (X ^ 2 + 1 : ℂ[X]) = (X - C I) * (X - C (-I)) := by
    have key : (C I * C I : ℂ[X]) = -1 := by simp [← C_mul]
    rw [C_neg]
    linear_combination key
  have p_ne_zero : (X - C I) * (X - C (-I)) ≠ 0 := by
    intro H
    apply_fun eval 0 at H
    simp [eval] at H
  simp only [factored, roots_mul p_ne_zero, roots_X_sub_C]
  rfl

-- Mathlib 知晓达朗贝尔-高斯定理：``ℂ`` 是代数闭域。
example : IsAlgClosed ℂ := inferInstance

-- QUOTE.
/- TEXT:
更一般地说，给定一个环态射 ``f : R →+* S``，可以使用 ``Polynomial.eval₂`` 在 ``S`` 中的一个点上对 ``P : R[X]`` 进行求值。
由于它不假设存在 ``Algebra R S`` 实例，因此它生成从 ``R[X]`` 到 ``S`` 的实际函数，因此点符号可以像预期那样正常工作。
EXAMPLES: -/
-- QUOTE:
#check (Complex.ofRealHom : ℝ →+* ℂ)

example : (X ^ 2 + 1 : ℝ[X]).eval₂ Complex.ofRealHom Complex.I = 0 := by simp
-- QUOTE.

/- TEXT:
我们最后简要提一下多变量多项式。给定一个交换半环 ``R``，系数在 ``R`` 且不定元通过类型 ``σ`` 索引的多项式所构成的 ``R``-代数为 ``MVPolynomial σ R``。

给定 ``i : σ``，对应的不定元记为 ``MvPolynomial.X i``。（通常可以打开 ``MVPolynomial`` 命名空间以将其缩写为 ``X i``。）

例如，如果我们需要两个不定元，可以使用 ``Fin 2`` 作为 ``σ`` 并写出定义单位圆的多项式（在 :math:`\mathbb{R}^2` 中）如下：
EXAMPLES: -/
-- QUOTE:
open MvPolynomial

def circleEquation : MvPolynomial (Fin 2) ℝ := X 0 ^ 2 + X 1 ^ 2 - 1
-- QUOTE.

/- TEXT:
函数应用具有非常高的优先级，因此上述表达式可以读取为
``(X 0) ^ 2 + (X 1) ^ 2 - 1``。

我们可以对其进行求值，以确保坐标为 :math:`(1, 0)` 的点位于圆上。
此外，``![...]`` 表示符号表示元素属于 ``Fin n → X``，其中自然数 ``n`` 是由参数的数量决定的，而某种类型 ``X`` 是由参数的类型决定的。
EXAMPLES: -/
-- QUOTE:
example : MvPolynomial.eval ![0, 1] circleEquation = 0 := by simp [circleEquation]
-- QUOTE.

end Polynomials
