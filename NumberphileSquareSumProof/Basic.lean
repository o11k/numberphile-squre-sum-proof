import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.List.Basic

def IsSquare (n : ℕ) : Prop := ∃ k, k * k = n

def RegularList : List ℕ → Prop
  | []             => True
  | [_]            => True
  | a :: b :: rest => IsSquare (a + b) ∧ RegularList (b :: rest)

def RegularNumber (n : ℕ) : Prop :=
  ∃ l : List ℕ, l.Perm (List.range' 1 n) ∧ RegularList l

theorem regular_number_of_gt_25 : ∀ n : ℕ, n > 25 → RegularNumber n := sorry
