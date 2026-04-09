import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.List.Basic

def IsPerfectSquare (n : ℕ) : Prop := ∃ k, k * k = n

def RegularList : List ℕ → Prop
  | []             => True
  | [_]            => True
  | a :: b :: rest => IsPerfectSquare (a + b) ∧ RegularList (b :: rest)

def RegularNumber (n : ℕ) : Prop :=
  ∃ l : List ℕ, l.Perm (List.range' 1 n) ∧ RegularList l


instance decIsPerfectSquare (n : ℕ) : Decidable (IsPerfectSquare n) :=
  decidable_of_iff ((List.range (n + 1)).any (fun k => k * k = n) = true) <| by
    unfold IsPerfectSquare
    simp only [List.any_eq_true, List.mem_range, decide_eq_true_eq]
    constructor
    · rintro ⟨k, _, hk⟩; exact ⟨k, hk⟩
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_, hk⟩
      rcases k with _ | k
      · omega
      · have : k + 1 ≤ (k + 1) * (k + 1) := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
        omega

instance decRegularList : ∀ l, Decidable (RegularList l)
  | []          => instDecidableTrue
  | [_]         => instDecidableTrue
  | a :: b :: rest =>
    have : Decidable (RegularList (b :: rest)) := decRegularList (b :: rest)
    show Decidable (IsPerfectSquare (a + b) ∧ RegularList (b :: rest)) from
      instDecidableAnd
