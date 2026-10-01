/-!
# Compiler correctness for a stack machine

A tiny expression language, a stack-machine instruction set, a compiler,
and a proof that running the compiled program computes the value of the
expression (the classic "verified compiler" exercise).
-/

namespace LeanProofs

inductive Exp where
  | num : Nat → Exp
  | plus : Exp → Exp → Exp
  | times : Exp → Exp → Exp
  | minus : Exp → Exp → Exp   -- truncated subtraction

inductive Instr where
  | push : Nat → Instr
  | add : Instr
  | mul : Instr
  | sub : Instr

/-- Direct (denotational) semantics. -/
def Exp.eval : Exp → Nat
  | .num n => n
  | .plus a b => a.eval + b.eval
  | .times a b => a.eval * b.eval
  | .minus a b => a.eval - b.eval

/-- One step of the machine; `none` on stack underflow. -/
def step : Instr → List Nat → Option (List Nat)
  | .push n, st => some (n :: st)
  | .add, y :: x :: st => some ((x + y) :: st)
  | .mul, y :: x :: st => some ((x * y) :: st)
  | .sub, y :: x :: st => some ((x - y) :: st)
  | _, _ => none

/-- Run a program on a stack. -/
def run : List Instr → List Nat → Option (List Nat)
  | [], st => some st
  | i :: is, st =>
    match step i st with
    | none => none
    | some st' => run is st'

/-- Post-order compilation: operands first, then the operator. -/
def compile : Exp → List Instr
  | .num n => [.push n]
  | .plus a b => compile a ++ compile b ++ [.add]
  | .times a b => compile a ++ compile b ++ [.mul]
  | .minus a b => compile a ++ compile b ++ [.sub]

/-- Running a concatenation is running the parts in sequence. -/
theorem run_append (p q : List Instr) (st : List Nat) :
    run (p ++ q) st = (run p st).bind (fun st' => run q st') := by
  induction p generalizing st with
  | nil => simp [run]
  | cons i is ih =>
    simp only [List.cons_append, run]
    cases h : step i st with
    | none => simp
    | some st' => simp [ih]

/-- Main lemma: compiled code leaves the value on top of the existing stack. -/
theorem run_compile (e : Exp) (st : List Nat) :
    run (compile e) st = some (e.eval :: st) := by
  induction e generalizing st with
  | num n => simp [compile, run, step, Exp.eval]
  | plus a b iha ihb =>
    simp [compile, run_append, iha, ihb, run, step, Exp.eval]
  | times a b iha ihb =>
    simp [compile, run_append, iha, ihb, run, step, Exp.eval]
  | minus a b iha ihb =>
    simp [compile, run_append, iha, ihb, run, step, Exp.eval]

/-- Correctness from the empty stack. -/
theorem compile_correct (e : Exp) : run (compile e) [] = some [e.eval] :=
  run_compile e []

example : run (compile (.plus (.num 2) (.times (.num 3) (.num 4)))) [] = some [14] := by
  decide

end LeanProofs
