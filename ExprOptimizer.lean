/-!
# A verified expression optimizer

Arithmetic expressions with variables, an evaluator, and a simplifier
(constant folding and algebraic identities). The main theorem states that
simplification never changes the value of an expression.
-/

namespace LeanProofs

inductive Expr where
  | const : Nat → Expr
  | var : Nat → Expr
  | add : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  deriving Repr, DecidableEq

namespace Expr

/-- Value of an expression under a variable assignment. -/
def eval (env : Nat → Nat) : Expr → Nat
  | const n => n
  | var i => env i
  | add a b => eval env a + eval env b
  | mul a b => eval env a * eval env b

/-- Smart constructor for addition: folds constants and drops `+ 0`. -/
def mkAdd : Expr → Expr → Expr
  | const 0, e => e
  | e, const 0 => e
  | const m, const n => const (m + n)
  | a, b => add a b

/-- Smart constructor for multiplication: folds constants, drops `* 1`,
and collapses `* 0`. -/
def mkMul : Expr → Expr → Expr
  | const 0, _ => const 0
  | _, const 0 => const 0
  | const 1, e => e
  | e, const 1 => e
  | const m, const n => const (m * n)
  | a, b => mul a b

/-- Bottom-up simplifier. -/
def simp : Expr → Expr
  | const n => const n
  | var i => var i
  | add a b => mkAdd (simp a) (simp b)
  | mul a b => mkMul (simp a) (simp b)

theorem eval_mkAdd (env : Nat → Nat) (a b : Expr) :
    eval env (mkAdd a b) = eval env a + eval env b := by
  match a, b with
  | const 0, e => simp [mkAdd, eval]
  | const (k + 1), const 0 => simp [mkAdd, eval]
  | const (k + 1), const (n + 1) => simp [mkAdd, eval]
  | const (k + 1), var i => simp [mkAdd, eval]
  | const (k + 1), add x y => simp [mkAdd, eval]
  | const (k + 1), mul x y => simp [mkAdd, eval]
  | var i, const 0 => simp [mkAdd, eval]
  | var i, const (n + 1) => simp [mkAdd, eval]
  | var i, var j => simp [mkAdd, eval]
  | var i, add x y => simp [mkAdd, eval]
  | var i, mul x y => simp [mkAdd, eval]
  | add x y, const 0 => simp [mkAdd, eval]
  | add x y, const (n + 1) => simp [mkAdd, eval]
  | add x y, var j => simp [mkAdd, eval]
  | add x y, add z w => simp [mkAdd, eval]
  | add x y, mul z w => simp [mkAdd, eval]
  | mul x y, const 0 => simp [mkAdd, eval]
  | mul x y, const (n + 1) => simp [mkAdd, eval]
  | mul x y, var j => simp [mkAdd, eval]
  | mul x y, add z w => simp [mkAdd, eval]
  | mul x y, mul z w => simp [mkAdd, eval]

theorem eval_mkMul (env : Nat → Nat) (a b : Expr) :
    eval env (mkMul a b) = eval env a * eval env b := by
  match a, b with
  | const 0, e => simp [mkMul, eval]
  | const (k + 1), const 0 => simp [mkMul, eval]
  | const 1, e =>
    cases e with
    | const n => cases n <;> simp [mkMul, eval]
    | var i => simp [mkMul, eval]
    | add x y => simp [mkMul, eval]
    | mul x y => simp [mkMul, eval]
  | const (k + 2), const 1 => simp [mkMul, eval]
  | const (k + 2), const (n + 2) => simp [mkMul, eval]
  | const (k + 2), var i => simp [mkMul, eval]
  | const (k + 2), add x y => simp [mkMul, eval]
  | const (k + 2), mul x y => simp [mkMul, eval]
  | var i, const 0 => simp [mkMul, eval]
  | var i, const 1 => simp [mkMul, eval]
  | var i, const (n + 2) => simp [mkMul, eval]
  | var i, var j => simp [mkMul, eval]
  | var i, add x y => simp [mkMul, eval]
  | var i, mul x y => simp [mkMul, eval]
  | add x y, const 0 => simp [mkMul, eval]
  | add x y, const 1 => simp [mkMul, eval]
  | add x y, const (n + 2) => simp [mkMul, eval]
  | add x y, var j => simp [mkMul, eval]
  | add x y, add z w => simp [mkMul, eval]
  | add x y, mul z w => simp [mkMul, eval]
  | mul x y, const 0 => simp [mkMul, eval]
  | mul x y, const 1 => simp [mkMul, eval]
  | mul x y, const (n + 2) => simp [mkMul, eval]
  | mul x y, var j => simp [mkMul, eval]
  | mul x y, add z w => simp [mkMul, eval]
  | mul x y, mul z w => simp [mkMul, eval]

/-- Main theorem: simplification preserves the meaning of an expression. -/
theorem eval_simp (env : Nat → Nat) : ∀ e : Expr, eval env (simp e) = eval env e
  | const n => rfl
  | var i => rfl
  | add a b => by
    rw [simp, eval_mkAdd, eval_simp env a, eval_simp env b]; rfl
  | mul a b => by
    rw [simp, eval_mkMul, eval_simp env a, eval_simp env b]; rfl

/-- Number of nodes in an expression. -/
def size : Expr → Nat
  | const _ => 1
  | var _ => 1
  | add a b => size a + size b + 1
  | mul a b => size a + size b + 1

theorem size_mkAdd_le (a b : Expr) : size (mkAdd a b) ≤ size a + size b + 1 := by
  match a, b with
  | const 0, e => simp [mkAdd, size]; omega
  | const (k + 1), const 0 => simp [mkAdd, size]
  | const (k + 1), const (n + 1) => simp [mkAdd, size]
  | const (k + 1), var i => simp [mkAdd, size]
  | const (k + 1), add x y => simp [mkAdd, size]
  | const (k + 1), mul x y => simp [mkAdd, size]
  | var i, const 0 => simp [mkAdd, size]
  | var i, const (n + 1) => simp [mkAdd, size]
  | var i, var j => simp [mkAdd, size]
  | var i, add x y => simp [mkAdd, size]
  | var i, mul x y => simp [mkAdd, size]
  | add x y, const 0 => simp [mkAdd, size]
  | add x y, const (n + 1) => simp [mkAdd, size]
  | add x y, var j => simp [mkAdd, size]
  | add x y, add z w => simp [mkAdd, size]
  | add x y, mul z w => simp [mkAdd, size]
  | mul x y, const 0 => simp [mkAdd, size]
  | mul x y, const (n + 1) => simp [mkAdd, size]
  | mul x y, var j => simp [mkAdd, size]
  | mul x y, add z w => simp [mkAdd, size]
  | mul x y, mul z w => simp [mkAdd, size]

end Expr

example : Expr.simp (Expr.add (Expr.mul (Expr.const 1) (Expr.var 0)) (Expr.const 0))
    = Expr.var 0 := by decide

end LeanProofs
