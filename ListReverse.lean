/-!
# Lists: append, reverse and fast reverse

Custom list functions with proofs of their algebraic laws, including
correctness of the tail-recursive (accumulator) reverse.
-/

namespace LeanProofs

inductive MyList (α : Type) where
  | nil : MyList α
  | cons : α → MyList α → MyList α

namespace MyList

variable {α β : Type}

def append : MyList α → MyList α → MyList α
  | nil, ys => ys
  | cons x xs, ys => cons x (append xs ys)

def length : MyList α → Nat
  | nil => 0
  | cons _ xs => length xs + 1

def reverse : MyList α → MyList α
  | nil => nil
  | cons x xs => append (reverse xs) (cons x nil)

/-- Tail-recursive reverse with an accumulator. -/
def revAux : MyList α → MyList α → MyList α
  | nil, acc => acc
  | cons x xs, acc => revAux xs (cons x acc)

def fastReverse (xs : MyList α) : MyList α := revAux xs nil

def map (f : α → β) : MyList α → MyList β
  | nil => nil
  | cons x xs => cons (f x) (map f xs)

theorem append_nil (xs : MyList α) : append xs nil = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [append, ih]

theorem append_assoc (xs ys zs : MyList α) :
    append (append xs ys) zs = append xs (append ys zs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [append, ih]

theorem length_append (xs ys : MyList α) :
    length (append xs ys) = length xs + length ys := by
  induction xs with
  | nil => simp [append, length]
  | cons x xs ih => simp [append, length, ih]; omega

theorem length_reverse (xs : MyList α) : length (reverse xs) = length xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [reverse, length_append, length, ih]

theorem reverse_append (xs ys : MyList α) :
    reverse (append xs ys) = append (reverse ys) (reverse xs) := by
  induction xs with
  | nil => simp [append, reverse, append_nil]
  | cons x xs ih => simp [append, reverse, ih, append_assoc]

/-- Reverse is an involution. -/
theorem reverse_reverse (xs : MyList α) : reverse (reverse xs) = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [reverse, reverse_append, ih, append]

/-- Key lemma for the accumulator version. -/
theorem revAux_eq (xs acc : MyList α) :
    revAux xs acc = append (reverse xs) acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    simp [revAux, reverse, ih, append_assoc, append]

/-- The fast tail-recursive reverse agrees with the naive one. -/
theorem fastReverse_eq (xs : MyList α) : fastReverse xs = reverse xs := by
  simp [fastReverse, revAux_eq, append_nil]

/-- `map` fusion. -/
theorem map_map (f : α → β) {γ : Type} (g : β → γ) (xs : MyList α) :
    map g (map f xs) = map (fun x => g (f x)) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [map, ih]

/-- `map` commutes with `reverse`. -/
theorem map_append (f : α → β) (xs ys : MyList α) :
    map f (append xs ys) = append (map f xs) (map f ys) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [map, append, ih]

theorem map_reverse (f : α → β) (xs : MyList α) :
    map f (reverse xs) = reverse (map f xs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [map, reverse, map_append, ih, append]

end MyList
end LeanProofs
