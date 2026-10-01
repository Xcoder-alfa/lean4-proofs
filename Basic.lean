import Mathlib

/-!
# Basic Lean 4 proofs (Mathlib)

Elementary results in number theory, algebra, set theory and real analysis,
proved from first principles with Lean 4 and Mathlib.
-/

namespace LeanProofs

/-- The sum of the first `n` odd numbers is `n ^ 2`. -/
theorem sum_odd (n : ℕ) : ∑ i ∈ Finset.range n, (2 * i + 1) = n ^ 2 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    ring

/-- Gauss' formula: `2 * (0 + 1 + ... + n) = n * (n + 1)`. -/
theorem gauss_sum (n : ℕ) :
    2 * ∑ i ∈ Finset.range (n + 1), i = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    ring

/-- AM-GM inequality for two real numbers (squared form). -/
theorem am_gm_two (a b : ℝ) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

/-- The square of an odd integer is odd. -/
theorem odd_sq_odd (n : ℤ) (h : Odd n) : Odd (n ^ 2) := by
  obtain ⟨k, rfl⟩ := h
  exact ⟨2 * k ^ 2 + 2 * k, by ring⟩

/-- Left cancellation in a group. -/
theorem group_left_cancel {G : Type*} [Group G] (a b c : G)
    (h : a * b = a * c) : b = c := by
  have h' := congrArg (fun x => a⁻¹ * x) h
  simpa using h'

/-- Intersection of sets is commutative. -/
theorem inter_comm' {α : Type*} (A B : Set α) : A ∩ B = B ∩ A := by
  ext x
  simp [and_comm]

/-- The triangle inequality for real numbers, proved by cases. -/
theorem tri_ineq (a b : ℝ) : |a + b| ≤ |a| + |b| := by
  rw [abs_le]
  rcases abs_cases a with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
  rcases abs_cases b with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
  constructor <;> linarith

end LeanProofs
