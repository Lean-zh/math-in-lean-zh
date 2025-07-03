-- BOTH:
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Charpoly.Basic

import MIL.Common


/- TEXT:

自同态
--------------

线性映射中的一个重要特例是自同态（endomorphisms）：即从向量空间自身映射到自身的线性映射。
自同态特别有趣，因为它们构成了一个 `K`-代数。具体来说，我们可以在其上对系数属于 `K` 的多项式进行求值，它们也可能具有特征值和特征向量。

Mathlib 使用简称 ``Module.End K V := V →ₗ[K] V``，这在大量使用此类映射时非常方便，尤其是在打开了 `Module` 命名空间后。
EXAMPLES: -/

-- QUOTE:

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

variable {W : Type*} [AddCommGroup W] [Module K W]


open Polynomial Module LinearMap

example (φ ψ : End K V) : φ * ψ = φ ∘ₗ ψ :=
  LinearMap.mul_eq_comp φ ψ -- `rfl` 也可以

-- evaluating `P` on `φ`
example (P : K[X]) (φ : End K V) : V →ₗ[K] V :=
  aeval φ P

-- evaluating `X` on `φ` gives back `φ`
example (φ : End K V) : aeval φ (X : K[X]) = φ :=
  aeval_X φ


-- QUOTE.
/- TEXT:
作为练习，结合自同态、子空间和多项式的操作，让我们证明二元核引理：对于任意自同态 :math:`φ` 及互素多项式 :math:`P` 和 :math:`Q`，有 :math:`\ker P(φ) ⊕ \ker Q(φ) = \ker \big(PQ(φ)\big)`。

注意，`IsCoprime x y` 的定义为 ``∃ a b, a * x + b * y = 1`` 。
EXAMPLES: -/
-- QUOTE:

#check Submodule.eq_bot_iff
#check Submodule.mem_inf
#check LinearMap.mem_ker

example (P Q : K[X]) (h : IsCoprime P Q) (φ : End K V) : ker (aeval φ P) ⊓ ker (aeval φ Q) = ⊥ := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  rw [Submodule.eq_bot_iff]
  rintro x hx
  rw [Submodule.mem_inf, mem_ker, mem_ker] at hx
  rcases h with ⟨U, V, hUV⟩
  have := congr((aeval φ) $hUV.symm x)
  simpa [hx]
-- BOTH:

#check Submodule.add_mem_sup
#check map_mul
#check LinearMap.mul_apply
#check LinearMap.ker_le_ker_comp

example (P Q : K[X]) (h : IsCoprime P Q) (φ : End K V) :
    ker (aeval φ P) ⊔ ker (aeval φ Q) = ker (aeval φ (P*Q)) := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  apply le_antisymm
  · apply sup_le
    · rw [mul_comm, map_mul]
      apply ker_le_ker_comp -- 或者换成下面的
      -- intro x hx
      -- rw [mul_comm, mem_ker] at *
      -- simp [hx]
    · rw [map_mul]
      apply ker_le_ker_comp -- 或者换成上面的
  · intro x hx
    rcases h with ⟨U, V, hUV⟩
    have key : x = aeval φ (U*P) x + aeval φ (V*Q) x := by simpa using congr((aeval φ) $hUV.symm x)
    rw [key, add_comm]
    apply Submodule.add_mem_sup <;> rw [mem_ker] at *
    · rw [← mul_apply, ← map_mul, show P*(V*Q) = V*(P*Q) by ring, map_mul, mul_apply, hx,
          map_zero]
    · rw [← mul_apply, ← map_mul, show Q*(U*P) = U*(P*Q) by ring, map_mul, mul_apply, hx,
          map_zero]

-- QUOTE.
/- TEXT:
我们现在转向本征空间和特征值的讨论。对于自同态 :math:`φ` 和标量 :math:`a` ，与之对应的本征空间是 :math:`φ - aId` 的核空间。本征空间对所有 ``a`` 都有定义，但只有在本征空间非零时才有意义。然而，本征向量定义为本征空间中的非零元素。对应的谓词是 `End.HasEigenvector`。
EXAMPLES: -/
-- QUOTE:
example (φ : End K V) (a : K) : φ.eigenspace a = LinearMap.ker (φ - a • 1) :=
  End.eigenspace_def


-- QUOTE.
/- TEXT:
然后有一个谓词 ``End.HasEigenvalue`` 和对应的子类型 ``End.Eigenvalues``。
EXAMPLES: -/
-- QUOTE:

example (φ : End K V) (a : K) : φ.HasEigenvalue a ↔ φ.eigenspace a ≠ ⊥ :=
  Iff.rfl

example (φ : End K V) (a : K) : φ.HasEigenvalue a ↔ ∃ v, φ.HasEigenvector a v  :=
  ⟨End.HasEigenvalue.exists_hasEigenvector, fun ⟨_, hv⟩ ↦ φ.hasEigenvalue_of_hasEigenvector hv⟩

example (φ : End K V) : φ.Eigenvalues = {a // φ.HasEigenvalue a} :=
  rfl

-- 特征值是最小多项式的根
example (φ : End K V) (a : K) : φ.HasEigenvalue a → (minpoly K φ).IsRoot a :=
  φ.isRoot_of_hasEigenvalue

-- 有限维情况下，反之亦然（我们将在下面讨论维度）
example [FiniteDimensional K V] (φ : End K V) (a : K) :
    φ.HasEigenvalue a ↔ (minpoly K φ).IsRoot a :=
  φ.hasEigenvalue_iff_isRoot

-- Cayley-Hamilton
example [FiniteDimensional K V] (φ : End K V) : aeval φ φ.charpoly = 0 :=
  φ.aeval_self_charpoly

-- QUOTE.
