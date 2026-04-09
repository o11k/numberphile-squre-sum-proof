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

theorem regular_number_of_gt_25 : ∀ n : ℕ, n > 25 → RegularNumber n := by
  intro n hn
  by_cases h1 : n ≤ 98
  · exact regular_25_to_98 n hn h1
  by_cases h2 : n ≤ 4900
  · exact regular_99_to_4900 n (by omega) h2
  · exact regular_4901_and_up n (by omega)
where
  regular_25_to_98 : ∀ n, n > 25 → n ≤ 98 → RegularNumber n := sorry
  regular_99_to_4900 : ∀ n, n > 98 → n ≤ 4900 → RegularNumber n := sorry
  regular_4901_and_up : ∀ n, n > 4900 → RegularNumber n := sorry
