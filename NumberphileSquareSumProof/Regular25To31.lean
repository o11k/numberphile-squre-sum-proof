import NumberphileSquareSumProof.Basic

set_option linter.style.longLine false in
private def regular_25_to_31_list := [
  [23,2,14,22,3,13,12,4,21,15,10,6,19,17,8,1,24,25,11,5,20,16,9,7,18],
  [15,21,4,12,13,3,22,14,2,23,26,10,6,19,17,8,1,24,25,11,5,20,16,9,7,18],
  [12,13,23,26,10,15,21,4,5,20,16,9,27,22,3,6,19,17,8,1,24,25,11,14,2,7,18],
  [25,24,1,15,10,26,23,13,12,4,21,28,8,17,19,6,3,22,27,9,16,20,5,11,14,2,7,18],
  [28,21,4,5,11,25,24,12,13,3,6,19,17,8,1,15,10,26,23,2,14,22,27,9,16,20,29,7,18],
  [30,19,17,8,28,21,15,1,24,25,11,5,4,12,13,3,6,10,26,23,2,14,22,27,9,16,20,29,7,18],
  [1,24,25,11,14,22,27,9,16,20,29,7,18,31,5,4,12,13,3,6,30,19,17,8,28,21,15,10,26,23,2],
]

theorem regular_number_of_ge_25_le_31 :
∀ n : ℕ, n ≥ 25 → n ≤ 31 → RegularNumber n := by
  intro n hn hle
  have hwitness : ∀ i : Fin 7,
      (regular_25_to_31_list[i.val]).Perm (List.range' 1 (i.val + 25)) ∧
      RegularList (regular_25_to_31_list[i.val]) := by decide
  have hi : n - 25 < 7 := by omega
  have hperm := (hwitness ⟨n - 25, hi⟩).1
  have hreg  := (hwitness ⟨n - 25, hi⟩).2
  simp only [Nat.sub_add_cancel hn] at hperm
  exact ⟨_, hperm, hreg⟩
