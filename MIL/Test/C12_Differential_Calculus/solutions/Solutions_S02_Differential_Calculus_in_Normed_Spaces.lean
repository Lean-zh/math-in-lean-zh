import MIL.Common
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Prod


open Set Filter

open Topology Filter

noncomputable section

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

open Metric

example {ι : Type*} [CompleteSpace E] {g : ι → E →L[𝕜] F} (h : ∀ x, ∃ C, ∀ i, ‖g i x‖ ≤ C) :
    ∃ C', ∀ i, ‖g i‖ ≤ C' := by
  -- 由范数 `‖g i x‖` 被 `n` 所限制那些的 `x : E` 组成的子集序列
  let e : ℕ → Set E := fun n ↦ ⋂ i : ι, { x : E | ‖g i x‖ ≤ n }
  -- 这些集合每个都是闭集
  have hc : ∀ n : ℕ, IsClosed (e n) := fun i ↦
    isClosed_iInter fun i ↦ isClosed_le (g i).cont.norm continuous_const
  -- 并集是整个空间；这就是我们使用 `h` 的地方
  have hU : (⋃ n : ℕ, e n) = univ := by
    refine eq_univ_of_forall fun x ↦ ?_
    rcases h x with ⟨C, hC⟩
    obtain ⟨m, hm⟩ := exists_nat_ge C
    exact ⟨e m, mem_range_self m, mem_iInter.mpr fun i ↦ le_trans (hC i) hm⟩
  /- 应用贝尔纲定理得出结论：存在某个 `m ： ℕ` ，使得 `e m` 包含某个 `x` -/
  obtain ⟨m : ℕ, x : E, hx : x ∈ interior (e m)⟩ := nonempty_interior_of_iUnion_of_closed hc hU
  obtain ⟨ε, ε_pos, hε : ball x ε ⊆ interior (e m)⟩ := isOpen_iff.mp isOpen_interior x hx
  obtain ⟨k : 𝕜, hk : 1 < ‖k‖⟩ := NormedField.exists_one_lt_norm 𝕜
  -- 证明球内所有元素在应用任何 `g i` 后范数均不超过 `m`
  have real_norm_le : ∀ z ∈ ball x ε, ∀ (i : ι), ‖g i z‖ ≤ m := by
    intro z hz i
    replace hz := mem_iInter.mp (interior_iInter_subset _ (hε hz)) i
    apply interior_subset hz
  have εk_pos : 0 < ε / ‖k‖ := div_pos ε_pos (zero_lt_one.trans hk)
  refine ⟨(m + m : ℕ) / (ε / ‖k‖), fun i ↦ ContinuousLinearMap.opNorm_le_of_shell ε_pos ?_ hk ?_⟩
  · exact div_nonneg (Nat.cast_nonneg _) εk_pos.le
  intro y le_y y_lt
  calc
    ‖g i y‖ = ‖g i (y + x) - g i x‖ := by rw [(g i).map_add, add_sub_cancel_right]
    _ ≤ ‖g i (y + x)‖ + ‖g i x‖ := (norm_sub_le _ _)
    _ ≤ m + m :=
      (add_le_add (real_norm_le (y + x) (by rwa [add_comm, add_mem_ball_iff_norm]) i)
        (real_norm_le x (mem_ball_self ε_pos) i))
    _ = (m + m : ℕ) := by norm_cast
    _ ≤ (m + m : ℕ) * (‖y‖ / (ε / ‖k‖)) :=
      (le_mul_of_one_le_right (Nat.cast_nonneg _)
        ((one_le_div <| div_pos ε_pos (zero_lt_one.trans hk)).2 le_y))
    _ = (m + m : ℕ) / (ε / ‖k‖) * ‖y‖ := (mul_comm_div _ _ _).symm


end

