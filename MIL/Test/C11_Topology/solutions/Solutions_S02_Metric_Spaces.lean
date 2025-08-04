import MIL.Common
import Mathlib.Topology.Instances.Real
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

open Set Filter
open Topology Filter

variable {X : Type*} [MetricSpace X] (a b c : X)

#check (dist a b : ℝ)
#check (dist_nonneg : 0 ≤ dist a b)
#check (dist_eq_zero : dist a b = 0 ↔ a = b)
#check (dist_comm a b : dist a b = dist b a)
#check (dist_triangle a b c : dist a c ≤ dist a b + dist b c)

-- -- Note the next three lines are not quoted, their purpose is to make sure those things don't get renamed while we're looking elsewhere.

-- 请注意接下来的三行未加引号，其目的是在我们查看其他内容时确保这些内容不会被重命名。
#check EMetricSpace
#check PseudoMetricSpace
#check PseudoEMetricSpace

example {u : ℕ → X} {a : X} :
    Tendsto u atTop (𝓝 a) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (u n) a < ε :=
  Metric.tendsto_atTop

example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} :
    Continuous f ↔
      ∀ x : X, ∀ ε > 0, ∃ δ > 0, ∀ x', dist x' x < δ → dist (f x') (f x) < ε :=
  Metric.continuous_iff

example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) := by continuity

example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) :=
  continuous_dist.comp ((hf.comp continuous_fst).prod_mk (hf.comp continuous_snd))

example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) := by
  apply Continuous.dist
  exact hf.comp continuous_fst
  exact hf.comp continuous_snd

example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) :=
  (hf.comp continuous_fst).dist (hf.comp continuous_snd)

example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
    Continuous fun p : X × X ↦ dist (f p.1) (f p.2) :=
  hf.fst'.dist hf.snd'

example {f : ℝ → X} (hf : Continuous f) : Continuous fun x : ℝ ↦ f (x ^ 2 + x) :=
  sorry

example {f : ℝ → X} (hf : Continuous f) : Continuous fun x : ℝ ↦ f (x ^ 2 + x) :=
  hf.comp <| (continuous_pow 2).add continuous_id

example {X Y : Type*} [MetricSpace X] [MetricSpace Y] (f : X → Y) (a : X) :
    ContinuousAt f a ↔ ∀ ε > 0, ∃ δ > 0, ∀ {x}, dist x a < δ → dist (f x) (f a) < ε :=
  Metric.continuousAt_iff

variable (r : ℝ)

example : Metric.ball a r = { b | dist b a < r } :=
  rfl

example : Metric.closedBall a r = { b | dist b a ≤ r } :=
  rfl

example (hr : 0 < r) : a ∈ Metric.ball a r :=
  Metric.mem_ball_self hr

example (hr : 0 ≤ r) : a ∈ Metric.closedBall a r :=
  Metric.mem_closedBall_self hr

example (s : Set X) : IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, Metric.ball x ε ⊆ s :=
  Metric.isOpen_iff

example {s : Set X} : IsClosed s ↔ IsOpen (sᶜ) :=
  isOpen_compl_iff.symm

example {s : Set X} (hs : IsClosed s) {u : ℕ → X} (hu : Tendsto u atTop (𝓝 a))
    (hus : ∀ n, u n ∈ s) : a ∈ s :=
  hs.mem_of_tendsto hu (Eventually.of_forall hus)

example {s : Set X} : a ∈ closure s ↔ ∀ ε > 0, ∃ b ∈ s, a ∈ Metric.ball b ε :=
  Metric.mem_closure_iff

example {u : ℕ → X} (hu : Tendsto u atTop (𝓝 a)) {s : Set X} (hs : ∀ n, u n ∈ s) :
    a ∈ closure s :=
  sorry

example {u : ℕ → X} (hu : Tendsto u atTop (𝓝 a)) {s : Set X} (hs : ∀ n, u n ∈ s) : a ∈ closure s := by
  rw [Metric.tendsto_atTop] at hu
  rw [Metric.mem_closure_iff]
  intro ε ε_pos
  rcases hu ε ε_pos with ⟨N, hN⟩
  refine ⟨u N, hs _, ?_⟩
  rw [dist_comm]
  exact hN N le_rfl

example {x : X} {s : Set X} : s ∈ 𝓝 x ↔ ∃ ε > 0, Metric.ball x ε ⊆ s :=
  Metric.nhds_basis_ball.mem_iff

example {x : X} {s : Set X} : s ∈ 𝓝 x ↔ ∃ ε > 0, Metric.closedBall x ε ⊆ s :=
  Metric.nhds_basis_closedBall.mem_iff

example : IsCompact (Set.Icc 0 1 : Set ℝ) :=
  isCompact_Icc

example {s : Set X} (hs : IsCompact s) {u : ℕ → X} (hu : ∀ n, u n ∈ s) :
    ∃ a ∈ s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 a) :=
  hs.tendsto_subseq hu

example {s : Set X} (hs : IsCompact s) (hs' : s.Nonempty) {f : X → ℝ}
      (hfs : ContinuousOn f s) :
    ∃ x ∈ s, ∀ y ∈ s, f x ≤ f y :=
  hs.exists_isMinOn hs' hfs

example {s : Set X} (hs : IsCompact s) (hs' : s.Nonempty) {f : X → ℝ}
      (hfs : ContinuousOn f s) :
    ∃ x ∈ s, ∀ y ∈ s, f y ≤ f x :=
  hs.exists_isMaxOn hs' hfs

example {s : Set X} (hs : IsCompact s) : IsClosed s :=
  hs.isClosed

example {X : Type*} [MetricSpace X] [CompactSpace X] : IsCompact (univ : Set X) :=
  isCompact_univ

#check IsCompact.isClosed

example {X : Type*} [MetricSpace X] {Y : Type*} [MetricSpace Y] {f : X → Y} :
    UniformContinuous f ↔
      ∀ ε > 0, ∃ δ > 0, ∀ {a b : X}, dist a b < δ → dist (f a) (f b) < ε :=
  Metric.uniformContinuous_iff

example {X : Type*} [MetricSpace X] [CompactSpace X]
      {Y : Type*} [MetricSpace Y] {f : X → Y}
    (hf : Continuous f) : UniformContinuous f :=
  sorry

example {X : Type*} [MetricSpace X] [CompactSpace X] {Y : Type*} [MetricSpace Y] {f : X → Y}
    (hf : Continuous f) : UniformContinuous f := by
  rw [Metric.uniformContinuous_iff]
  intro ε ε_pos
  let φ : X × X → ℝ := fun p ↦ dist (f p.1) (f p.2)
  have φ_cont : Continuous φ := hf.fst'.dist hf.snd'
  let K := { p : X × X | ε ≤ φ p }
  have K_closed : IsClosed K := isClosed_le continuous_const φ_cont
  have K_cpct : IsCompact K := K_closed.isCompact
  rcases eq_empty_or_nonempty K with hK | hK
  · use 1, by norm_num
    intro x y _
    have : (x, y) ∉ K := by simp [hK]
    simpa [K] using this
  · rcases K_cpct.exists_isMinOn hK continuous_dist.continuousOn with ⟨⟨x₀, x₁⟩, xx_in, H⟩
    use dist x₀ x₁
    constructor
    · change _ < _
      rw [dist_pos]
      intro h
      have : ε ≤ 0 := by simpa [K, φ, *] using xx_in
      linarith
    · intro x x'
      contrapose!
      intro (hxx' : (x, x') ∈ K)
      exact H hxx'

example (u : ℕ → X) :
    CauchySeq u ↔ ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, dist (u m) (u n) < ε :=
  Metric.cauchySeq_iff

example (u : ℕ → X) :
    CauchySeq u ↔ ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, dist (u n) (u N) < ε :=
  Metric.cauchySeq_iff'

example [CompleteSpace X] (u : ℕ → X) (hu : CauchySeq u) :
    ∃ x, Tendsto u atTop (𝓝 x) :=
  cauchySeq_tendsto_of_complete hu

open BigOperators

open Finset

theorem cauchySeq_of_le_geometric_two' {u : ℕ → X}
    (hu : ∀ n : ℕ, dist (u n) (u (n + 1)) ≤ (1 / 2) ^ n) : CauchySeq u := by
  rw [Metric.cauchySeq_iff']
  intro ε ε_pos
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 1 / 2 ^ N * 2 < ε := by sorry
  use N
  intro n hn
  obtain ⟨k, rfl : n = N + k⟩ := le_iff_exists_add.mp hn
  calc
    dist (u (N + k)) (u N) = dist (u (N + 0)) (u (N + k)) := sorry
    _ ≤ ∑ i in range k, dist (u (N + i)) (u (N + (i + 1))) := sorry
    _ ≤ ∑ i in range k, (1 / 2 : ℝ) ^ (N + i) := sorry
    _ = 1 / 2 ^ N * ∑ i in range k, (1 / 2 : ℝ) ^ i := sorry
    _ ≤ 1 / 2 ^ N * 2 := sorry
    _ < ε := sorry


example {u : ℕ → X} (hu : ∀ n : ℕ, dist (u n) (u (n + 1)) ≤ (1 / 2) ^ n) : CauchySeq u := by
  rw [Metric.cauchySeq_iff']
  intro ε ε_pos
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 1 / 2 ^ N * 2 < ε := by
    have : Tendsto (fun N : ℕ ↦ (1 / 2 ^ N * 2 : ℝ)) atTop (𝓝 0) := by
      rw [← zero_mul (2 : ℝ)]
      apply Tendsto.mul
      simp_rw [← one_div_pow (2 : ℝ)]
      apply tendsto_pow_atTop_nhds_zero_of_lt_one <;> linarith
      exact tendsto_const_nhds
    rcases(atTop_basis.tendsto_iff (nhds_basis_Ioo_pos (0 : ℝ))).mp this ε ε_pos with ⟨N, _, hN⟩
    exact ⟨N, by simpa using (hN N left_mem_Ici).2⟩
  use N
  intro n hn
  obtain ⟨k, rfl : n = N + k⟩ := le_iff_exists_add.mp hn
  calc
    dist (u (N + k)) (u N) = dist (u (N + 0)) (u (N + k)) := by rw [dist_comm, add_zero]
    _ ≤ ∑ i in range k, dist (u (N + i)) (u (N + (i + 1))) :=
      (dist_le_range_sum_dist (fun i ↦ u (N + i)) k)
    _ ≤ ∑ i in range k, (1 / 2 : ℝ) ^ (N + i) := (sum_le_sum fun i _ ↦ hu <| N + i)
    _ = 1 / 2 ^ N * ∑ i in range k, (1 / 2 : ℝ) ^ i := by simp_rw [← one_div_pow, pow_add, ← mul_sum]
    _ ≤ 1 / 2 ^ N * 2 :=
      (mul_le_mul_of_nonneg_left (sum_geometric_two_le _)
        (one_div_nonneg.mpr (pow_nonneg (zero_le_two : (0 : ℝ) ≤ 2) _)))
    _ < ε := hN


open Metric

example [CompleteSpace X] (f : ℕ → Set X) (ho : ∀ n, IsOpen (f n)) (hd : ∀ n, Dense (f n)) :
    Dense (⋂ n, f n) := by
  let B : ℕ → ℝ := fun n ↦ (1 / 2) ^ n
  have Bpos : ∀ n, 0 < B n
  sorry
  /- 将密度假设转化为两个函数 `center` 和 `radius`，对于任意的 n、x、δ、δpos，这两个函数分别关联一个中心和一个正半径，使得 `closedBall center radius` 同时包含在 `f n` 和 `closedBall x δ` 中。我们还可以要求 `radius ≤ (1/2)^(n+1)`，以确保之后能得到一个柯西序列。-/
  have :
    ∀ (n : ℕ) (x : X),
      ∀ δ > 0, ∃ y : X, ∃ r > 0, r ≤ B (n + 1) ∧ closedBall y r ⊆ closedBall x δ ∩ f n :=
    by sorry
  choose! center radius Hpos HB Hball using this
  intro x
  rw [mem_closure_iff_nhds_basis nhds_basis_closedBall]
  intro ε εpos
  /-  设 `ε` 为正数。我们需要在以 `x` 为圆心、半径为 `ε` 的球内找到一个点，该点属于所有的 `f n`。为此，我们递归地构造一个序列 `F n = (c n, r n)`，使得闭球 `closedBall (c n) (r n)` 包含在前一个球内且属于 `f n`，并且 `r n` 足够小以确保 `c n` 是一个柯西序列。那么 `c n` 收敛到一个极限，该极限属于所有的 `f n`。-/
  let F : ℕ → X × ℝ := fun n ↦
    Nat.recOn n (Prod.mk x (min ε (B 0)))
      fun n p ↦ Prod.mk (center n p.1 p.2) (radius n p.1 p.2)
  let c : ℕ → X := fun n ↦ (F n).1
  let r : ℕ → ℝ := fun n ↦ (F n).2
  have rpos : ∀ n, 0 < r n := by sorry
  have rB : ∀ n, r n ≤ B n := by sorry
  have incl : ∀ n, closedBall (c (n + 1)) (r (n + 1)) ⊆ closedBall (c n) (r n) ∩ f n := by
    sorry
  have cdist : ∀ n, dist (c n) (c (n + 1)) ≤ B n := by sorry
  have : CauchySeq c := cauchySeq_of_le_geometric_two' cdist
  -- 由于序列 `c n` 在完备空间中是柯西序列，所以它收敛于极限 `y`。
  -- 根据完备空间中柯西序列收敛的定理，存在 `y` 使得 `c n` 收敛于 `y`，记为 `ylim`。
  -- 这个点 `y` 就是我们想要的点。接下来我们要验证它属于所有的 `f n` 以及 `ball x ε`。
  use y
  have I : ∀ n, ∀ m ≥ n, closedBall (c m) (r m) ⊆ closedBall (c n) (r n) := by sorry
  have yball : ∀ n, y ∈ closedBall (c n) (r n) := by sorry
  sorry

example [CompleteSpace X] (f : ℕ → Set X) (ho : ∀ n, IsOpen (f n)) (hd : ∀ n, Dense (f n)) :
    Dense (⋂ n, f n) := by
  let B : ℕ → ℝ := fun n ↦ (1 / 2) ^ n
  have Bpos : ∀ n, 0 < B n := fun n ↦ pow_pos sorry n
  /- 将密度假设转化为两个函数 `center` 和 `radius`，对于任意的 n、x、δ、δpos，这两个函数分别关联一个中心和一个正半径，使得 `closedBall center radius` 同时包含在 `f n` 和 `closedBall x δ` 中。我们还可以要求 `radius ≤ (1/2)^(n+1)`，以确保之后能得到一个柯西序列。 -/
  have :
    ∀ (n : ℕ) (x : X),
      ∀ δ > 0, ∃ y : X, ∃ r > 0, r ≤ B (n + 1) ∧ closedBall y r ⊆ closedBall x δ ∩ f n := by
    intro n x δ δpos
    have : x ∈ closure (f n) := hd n x
    rcases Metric.mem_closure_iff.1 this (δ / 2) (half_pos δpos) with ⟨y, ys, xy⟩
    rw [dist_comm] at xy
    obtain ⟨r, rpos, hr⟩ : ∃ r > 0, closedBall y r ⊆ f n :=
      nhds_basis_closedBall.mem_iff.1 (isOpen_iff_mem_nhds.1 (ho n) y ys)
    refine ⟨y, min (min (δ / 2) r) (B (n + 1)), ?_, ?_, fun z hz ↦ ⟨?_, ?_⟩⟩
    show 0 < min (min (δ / 2) r) (B (n + 1))
    exact lt_min (lt_min (half_pos δpos) rpos) (Bpos (n + 1))
    show min (min (δ / 2) r) (B (n + 1)) ≤ B (n + 1)
    exact min_le_right _ _
    show z ∈ closedBall x δ
    exact
      calc
        dist z x ≤ dist z y + dist y x := dist_triangle _ _ _
        _ ≤ min (min (δ / 2) r) (B (n + 1)) + δ / 2 := (add_le_add hz xy.le)
        _ ≤ δ / 2 + δ / 2 := (add_le_add_right ((min_le_left _ _).trans (min_le_left _ _)) _)
        _ = δ := add_halves δ

    show z ∈ f n
    exact
      hr
        (calc
          dist z y ≤ min (min (δ / 2) r) (B (n + 1)) := hz
          _ ≤ r := (min_le_left _ _).trans (min_le_right _ _)
          )
  choose! center radius Hpos HB Hball using this
  refine fun x ↦ (mem_closure_iff_nhds_basis nhds_basis_closedBall).2 fun ε εpos ↦ ?_
  /- `ε` 是正数。我们必须找到一个位于以 `x` 为中心、半径为 `ε` 的球内且属于所有 `f n` 的点。为此，我们递归地构造一个序列 `F n = (c n, r n)`，使得闭球 `closedBall (c n) (r n)` 包含在前一个球内且属于 `f n`，并且 `r n` 足够小以确保 `c n` 是一个柯西序列。然后 `c n` 收敛到一个属于所有 `f n` 的极限。 -/
  let F : ℕ → X × ℝ := fun n ↦
    Nat.recOn n (Prod.mk x (min ε (B 0))) fun n p ↦ Prod.mk (center n p.1 p.2) (radius n p.1 p.2)
  let c : ℕ → X := fun n ↦ (F n).1
  let r : ℕ → ℝ := fun n ↦ (F n).2
  have rpos : ∀ n, 0 < r n := by
    intro n
    induction' n with n hn
    exact lt_min εpos (Bpos 0)
    exact Hpos n (c n) (r n) hn
  have rB : ∀ n, r n ≤ B n := by
    intro n
    induction' n with n hn
    exact min_le_right _ _
    exact HB n (c n) (r n) (rpos n)
  have incl : ∀ n, closedBall (c (n + 1)) (r (n + 1)) ⊆ closedBall (c n) (r n) ∩ f n := fun n ↦
    Hball n (c n) (r n) (rpos n)
  have cdist : ∀ n, dist (c n) (c (n + 1)) ≤ B n := by
    intro n
    rw [dist_comm]
    have A : c (n + 1) ∈ closedBall (c (n + 1)) (r (n + 1)) :=
      mem_closedBall_self (rpos <| n + 1).le
    have I :=
      calc
        closedBall (c (n + 1)) (r (n + 1)) ⊆ closedBall (c n) (r n) :=
          (incl n).trans Set.inter_subset_left
        _ ⊆ closedBall (c n) (B n) := closedBall_subset_closedBall (rB n)

    exact I A
  have : CauchySeq c := cauchySeq_of_le_geometric_two' cdist
  -- 由于序列 `c n` 在完备空间中是柯西序列，所以它收敛于某个极限 `y`。
  -- 根据完备空间中柯西序列收敛的定理，存在 `y` 使得 `c n` 收敛于 `y`，记为 `ylim`。
  -- 这个点 `y` 就是我们想要的点。接下来我们要验证它属于所有的 `f n` 以及 `ball x ε`。
  use y
  have I : ∀ n, ∀ m ≥ n, closedBall (c m) (r m) ⊆ closedBall (c n) (r n) := by
    intro n
    refine Nat.le_induction ?_ fun m hnm h ↦ ?_
    · exact Subset.rfl
    · exact (incl m).trans (Set.inter_subset_left.trans h)
  have yball : ∀ n, y ∈ closedBall (c n) (r n) := by
    intro n
    refine isClosed_ball.mem_of_tendsto ylim ?_
    refine (Filter.eventually_ge_atTop n).mono fun m hm ↦ ?_
    exact I n m hm (mem_closedBall_self (rpos _).le)
  constructor
  · suffices ∀ n, y ∈ f n by rwa [Set.mem_iInter]
    intro n
    have : closedBall (c (n + 1)) (r (n + 1)) ⊆ f n :=
      Subset.trans (incl n) Set.inter_subset_right
    exact this (yball (n + 1))
  calc
    dist y x ≤ r 0 := yball 0
    _ ≤ ε := min_le_left _ _
