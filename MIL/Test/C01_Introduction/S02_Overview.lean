import MIL.Common

open Nat

-- These are pieces of data.
#check 2 + 2

def f (x : ℕ) :=
  x + 3

#check f

-- These are propositions, of type `Prop`.
#check 2 + 2 = 4

def FermatLastTheorem :=
  ∀ x y z n : ℕ, n > 2 ∧ x * y * z ≠ 0 → x ^ n + y ^ n ≠ z ^ n

#check FermatLastTheorem

-- These are proofs of propositions.
theorem easy : 2 + 2 = 4 :=
  rfl

#check easy

theorem hard : FermatLastTheorem :=
  sorry

#check hard

-- Here are some proofs.
example : ∀ m n : Nat, Even n → Even (m * n) := fun m n ⟨k, (hk : n = k + k)⟩ ↦
  have hmn : m * n = m * k + m * k := by rw [hk, mul_add]
  show ∃ l, m * n = l + l from ⟨_, hmn⟩

example : ∀ m n : Nat, Even n → Even (m * n) :=
fun m n ⟨k, hk⟩ ↦ ⟨m * k, by rw [hk, mul_add]⟩

example : ∀ m n : Nat, Even n → Even (m * n) := by
  -- 设 `m` 和 `n` 是自然数，设 `n = 2 * k`
  rintro m n ⟨k, hk⟩
  -- 需证 `m * n` 是某自然数的两倍。那就设它是 `m * k` 的两倍吧
  use m * k
  -- 代入 `n`
  rw [hk]
  -- 剩下的就很显然了
  ring

example : ∀ m n : Nat, Even n → Even (m * n) := by
  rintro m n ⟨k, hk⟩; use m * k; rw [hk]; ring

example : ∀ m n : Nat, Even n → Even (m * n) := by
  intros; simp [*, parity_simps]

