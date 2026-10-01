/-!
# Insertion sort is correct

We define insertion sort on `List Nat` and prove the two properties that
specify a sorting algorithm: the output is sorted, and it is a permutation
of the input.
-/

namespace LeanProofs

/-- `Sorted xs` : the list is in non-decreasing order. -/
inductive Sorted : List Nat → Prop where
  | nil : Sorted []
  | single (a : Nat) : Sorted [a]
  | cons_cons (a b : Nat) (rest : List Nat) :
      a ≤ b → Sorted (b :: rest) → Sorted (a :: b :: rest)

/-- Insert `a` into a list at its place. -/
def insert (a : Nat) : List Nat → List Nat
  | [] => [a]
  | b :: bs => if a ≤ b then a :: b :: bs else b :: insert a bs

def isort : List Nat → List Nat
  | [] => []
  | a :: as => insert a (isort as)

/-- Inserting into a list leaves the head either `a` or the old head. -/
theorem insert_cons_cases (a b : Nat) (bs : List Nat) :
    ∃ c cs, insert a (b :: bs) = c :: cs ∧ (c = a ∨ c = b) := by
  by_cases h : a ≤ b
  · exact ⟨a, b :: bs, by simp [insert, h], Or.inl rfl⟩
  · exact ⟨b, insert a bs, by simp [insert, h], Or.inr rfl⟩

/-- Insertion preserves sortedness. -/
theorem insert_sorted (a : Nat) : ∀ xs : List Nat, Sorted xs → Sorted (insert a xs)
  | [], _ => Sorted.single a
  | b :: bs, h => by
    by_cases hab : a ≤ b
    · simp only [insert, hab, if_true]
      exact Sorted.cons_cons a b bs hab h
    · simp only [insert, hab, if_false]
      have hba : b ≤ a := by omega
      cases bs with
      | nil =>
        exact Sorted.cons_cons b a [] hba (Sorted.single a)
      | cons c cs =>
        have hsorted : Sorted (c :: cs) := by
          cases h with
          | cons_cons _ _ _ _ h2 => exact h2
        have hbc : b ≤ c := by
          cases h with
          | cons_cons _ _ _ h1 _ => exact h1
        have ih := insert_sorted a (c :: cs) hsorted
        obtain ⟨d, ds, hd, hdc⟩ := insert_cons_cases a c cs
        rw [hd] at ih ⊢
        have hbd : b ≤ d := by
          rcases hdc with rfl | rfl
          · exact hba
          · exact hbc
        exact Sorted.cons_cons b d ds hbd ih

/-- Insertion sort returns a sorted list. -/
theorem isort_sorted : ∀ xs : List Nat, Sorted (isort xs)
  | [] => Sorted.nil
  | a :: as => insert_sorted a (isort as) (isort_sorted as)

/-- Insertion is a permutation: `insert a xs` is `a :: xs` up to reordering. -/
theorem insert_perm (a : Nat) : ∀ xs : List Nat, (insert a xs).Perm (a :: xs)
  | [] => List.Perm.refl _
  | b :: bs => by
    by_cases h : a ≤ b
    · simp only [insert, h, if_true]
      exact List.Perm.refl _
    · simp only [insert, h, if_false]
      exact ((insert_perm a bs).cons b).trans (List.Perm.swap a b bs)

/-- Insertion sort returns a permutation of its input. -/
theorem isort_perm : ∀ xs : List Nat, (isort xs).Perm xs
  | [] => List.Perm.refl _
  | a :: as => (insert_perm a (isort as)).trans ((isort_perm as).cons a)

/-- Full specification of a sorting function. -/
theorem isort_correct (xs : List Nat) : Sorted (isort xs) ∧ (isort xs).Perm xs :=
  ⟨isort_sorted xs, isort_perm xs⟩

example : isort [3, 1, 2] = [1, 2, 3] := by decide

end LeanProofs
