import NumberphileSquareSumProof.Basic
import NumberphileSquareSumProof.Regular25To98

theorem regular_number_of_gt_25 : ∀ n : ℕ, n ≥ 25 → RegularNumber n := by
  intro n hn
  by_cases h1 : n ≤ 98
  · exact regular_25_to_98 n hn h1
  by_cases h2 : n ≤ 4900
  · exact regular_99_to_4900 n (by omega) h2
  · exact regular_4901_and_up n (by omega)
where
  regular_99_to_4900 : ∀ n, n ≥ 99 → n ≤ 4900 → RegularNumber n := sorry
  regular_4901_and_up : ∀ n, n ≥ 4901 → RegularNumber n := sorry
