# lean4-proofs

Formal proofs in Lean 4, written by Anmol Shakya
(M.Sc. Mathematics and Computing, BHU; CSIR-NET-JRF, Mathematical Sciences).

All files are self-contained and compile with core Lean 4 (checked with Lean 4.20.0), no extra dependencies.

## Contents

| File | Topic | Level |
| --- | --- | --- |
| `FibIdentities.lean` | Fibonacci: positivity, monotonicity, sum identity, addition formula `F(m+n+1) = F(m+1)F(n+1) + F(m)F(n)` | Medium |
| `ListReverse.lean` | Custom lists: append associativity, `reverse (reverse xs) = xs`, tail-recursive reverse correctness, map laws | Medium |
| `InsertionSort.lean` | Insertion sort returns a sorted permutation of its input | Hard |
| `ExprOptimizer.lean` | Verified constant-folding / algebraic simplifier for arithmetic expressions | Hard |
| `StackCompiler.lean` | Compiler correctness: expression to stack-machine code preserves meaning | Hard |

## Check

```bash
lean FibIdentities.lean
```

An empty output means the file type-checks, so every theorem is fully proved (no `sorry`).
