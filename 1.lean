import Mathlib.Data.Real.Basic
example (a b : ℝ) : a * b = b * a := by
  rw [mul_comm a b]
