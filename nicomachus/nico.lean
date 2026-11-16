import Mathlib

open Finset

/-- Gauss: twice the sum 0 + 1 + ... + n is n(n+1). -/
lemma two_mul_sum_range (n : ℕ) :
    2 * ∑ i ∈ range (n + 1), i = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, mul_add (2 : ℕ), ih]
    ring

/-- Four times the sum of cubes 0³ + 1³ + ... + n³ is (n(n+1))². -/
lemma four_mul_sum_cubes (n : ℕ) :
    4 * ∑ i ∈ range (n + 1), i ^ 3 = (n * (n + 1)) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, mul_add (4 : ℕ), ih]
    ring

/-- Nicomachus's theorem: 1³ + 2³ + ... + n³ = (1 + 2 + ... + n)². -/
theorem nicomachus (n : ℕ) :
    ∑ i ∈ range (n + 1), i ^ 3 = (∑ i ∈ range (n + 1), i) ^ 2 := by
  have h : 4 * ∑ i ∈ range (n + 1), i ^ 3
      = 4 * (∑ i ∈ range (n + 1), i) ^ 2 := by
    rw [four_mul_sum_cubes,
      show 4 * (∑ i ∈ range (n + 1), i) ^ 2
        = (2 * ∑ i ∈ range (n + 1), i) ^ 2 by ring,
      two_mul_sum_range]
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h

#check nicomachus
