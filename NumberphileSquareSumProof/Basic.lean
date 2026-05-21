import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.List.Basic

def IsPerfectSquare (n : ℕ) : Prop := ∃ k, k * k = n

def RegularList : List ℕ → Prop
  | []             => True
  | [_]            => True
  | a :: b :: rest => IsPerfectSquare (a + b) ∧ RegularList (b :: rest)

def CyclicalRegularList : List ℕ → Prop
  | []     => True
  | a :: rest => RegularList (a :: rest) ∧ IsPerfectSquare ((a :: rest).getLast (by simp) + a)

def sameIndexParity (S L : List ℕ) : Prop :=
  ∀ x ∈ S, ∀ i, S[i]? = some x → ∃ j, L[j]? = some x ∧ i % 2 = j % 2

def NinjaPair (S L : List ℕ) : Prop :=
  L.length = S.length + 1 ∧
  L.Perm (List.range' 1 L.length) ∧
  S.Perm (List.range' 1 S.length) ∧
  CyclicalRegularList S ∧
  CyclicalRegularList L ∧
  S.head? = some 1 ∧
  L.head? = some 1 ∧
  (S.length % 2 = 1 → S.getLast? = some 3) ∧
  (S.length % 2 = 0 → S.getLast? = some 8) ∧
  (L.length % 2 = 1 → L.getLast? = some 3) ∧
  (L.length % 2 = 0 → L.getLast? = some 8) ∧
  sameIndexParity S L

def RegularNumber (n : ℕ) : Prop :=
  ∃ l : List ℕ, l.Perm (List.range' 1 n) ∧ RegularList l

def CyclicalRegularNumber (n : ℕ) : Prop :=
  ∃ l : List ℕ, l.Perm (List.range' 1 n) ∧ CyclicalRegularList l

def NinjaNumber (n : ℕ) : Prop :=
  ∃ S : List ℕ, ∃ L : List ℕ, S.length = n ∧ NinjaPair S L

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

instance decCyclicalRegularList : ∀ l, Decidable (CyclicalRegularList l)
  | []     => instDecidableTrue
  | a :: rest =>
    show Decidable (
      RegularList (a :: rest) ∧
      IsPerfectSquare ((a :: rest).getLast (by simp) + a)
    ) from instDecidableAnd

theorem sameIndexParity_iff_bounded (S L : List ℕ) :
    sameIndexParity S L ↔
    ∀ x ∈ S, ∀ i : Fin S.length, S[i.val]? = some x →
      ∃ j : Fin L.length, L[j.val]? = some x ∧ i.val % 2 = j.val % 2 := by
  constructor
  · intro h x hx ⟨i, hi⟩ hS
    obtain ⟨j, hL, hpar⟩ := h x hx i hS
    have hjlt : j < L.length := by
      by_contra hge
      rw [List.getElem?_eq_none (by omega)] at hL
      exact absurd hL (by simp)
    exact ⟨⟨j, hjlt⟩, hL, hpar⟩
  · intro h x hx i hS
    have hilt : i < S.length := by
      by_contra hge
      rw [List.getElem?_eq_none (by omega)] at hS
      exact absurd hS (by simp)
    obtain ⟨⟨j, _⟩, hL, hpar⟩ := h x hx ⟨i, hilt⟩ hS
    exact ⟨j, hL, hpar⟩

instance decSameIndexParity (S L : List ℕ) : Decidable (sameIndexParity S L) :=
  decidable_of_iff _ (sameIndexParity_iff_bounded S L).symm

instance decNinjaPair (S L : List ℕ) : Decidable (NinjaPair S L) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))
