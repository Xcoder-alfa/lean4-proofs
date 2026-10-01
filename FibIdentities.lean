/-!
# Fibonacci identities

Properties of the Fibonacci sequence proved by induction in core Lean 4:
positivity, monotonicity, the sum identity and the addition formula.
-/

namespace LeanProofs

/-- The Fibonacci sequence. -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

theorem fib_add_two (n : Nat) : fib (n + 2) = fib n + fib (n + 1) := rfl

/-- Fibonacci numbers are positive for positive indices. -/
theorem fib_pos : ∀ n : Nat, 0 < n → 0 < fib n
  | 0, h => absurd h (Nat.lt_irrefl 0)
  | 1, _ => by decide
  | n + 2, _ => by
    have h1 : 0 < fib (n + 1) := fib_pos (n + 1) (Nat.succ_pos n)
    rw [fib_add_two]
    omega

/-- The sequence is monotone (one step). -/
theorem fib_le_fib_succ : ∀ n : Nat, fib n ≤ fib (n + 1)
  | 0 => by decide
  | n + 1 => by
    have := fib_le_fib_succ n
    rw [fib_add_two]
    omega

/-- Sum of the first `n` Fibonacci numbers `F₀ + ... + F_{n-1}`. -/
def fibSum : Nat → Nat
  | 0 => 0
  | n + 1 => fibSum n + fib n

/-- `F₀ + ... + F_{n-1} = F_{n+1} - 1`, stated without subtraction. -/
theorem fibSum_add_one (n : Nat) : fibSum n + 1 = fib (n + 1) := by
  induction n with
  | zero => decide
  | succ k ih =>
    show fibSum k + fib k + 1 = fib (k + 2)
    rw [fib_add_two]
    omega

/-- Addition formula: `F_{m+n+1} = F_{m+1} F_{n+1} + F_m F_n`. -/
theorem fib_add (m : Nat) : ∀ n : Nat,
    fib (m + n + 1) = fib (m + 1) * fib (n + 1) + fib m * fib n
  | 0 => by simp [fib]
  | 1 => by
    show fib (m + 2) = fib (m + 1) * fib 2 + fib m * fib 1
    simp [fib, fib_add_two]
    omega
  | n + 2 => by
    have h0 : fib (m + n + 1) = fib (m + 1) * fib (n + 1) + fib m * fib n :=
      fib_add m n
    have h1 : fib (m + n + 2) = fib (m + 1) * fib (n + 2) + fib m * fib (n + 1) :=
      fib_add m (n + 1)
    have a2 : fib (n + 2) = fib n + fib (n + 1) := fib_add_two n
    have a3 : fib (n + 3) = fib (n + 1) + fib (n + 2) := fib_add_two (n + 1)
    have b : fib (m + n + 3) = fib (m + n + 1) + fib (m + n + 2) :=
      fib_add_two (m + n + 1)
    show fib (m + n + 3) = fib (m + 1) * fib (n + 3) + fib m * fib (n + 2)
    rw [b, h0, h1, a3, a2]
    simp only [Nat.mul_add, Nat.add_mul]
    omega

end LeanProofs
