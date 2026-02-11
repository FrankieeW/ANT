import Mathlib

open Ideal Zsqrtd

abbrev R := Zsqrtd (-5)

theorem factorization_of_two :
    span {(2 : R)} = (span {2, 1 + sqrtd}) ^ 2 := by
  let J : Ideal R :=
    span ({(2 : R) * (2 : R), (2 : R) * (1 + sqrtd), (1 + sqrtd) * (2 : R),
      (1 + sqrtd) * (1 + sqrtd)} : Set R)
  have hsq : (1 + sqrtd : R) * (1 + sqrtd) = (2 : R) * (-2 + sqrtd) := by
    ext <;> norm_num [Zsqrtd.sqrtd]
  have hpow : (span ({(2 : R), (1 + sqrtd)} : Set R) : Ideal R) ^ 2 = J := by
    simp [J, pow_two, Ideal.span_pair_mul_span_pair]
  apply _root_.le_antisymm
  · rw [Ideal.span_singleton_le_iff_mem, hpow]
    have h21 : (2 : R) * (1 + sqrtd) ∈ J := Ideal.subset_span (by simp)
    have h11 : (1 + sqrtd : R) * (1 + sqrtd) ∈ J := Ideal.subset_span (by simp)
    have h22 : (2 : R) * (2 : R) ∈ J := Ideal.subset_span (by simp)
    have hmem : (2 : R) * (1 + sqrtd) - (1 + sqrtd) * (1 + sqrtd) - (2 : R) * (2 : R) ∈ J :=
      J.sub_mem (J.sub_mem h21 h11) h22
    have hcalc :
        (2 : R) * (1 + sqrtd) - (1 + sqrtd) * (1 + sqrtd) - (2 : R) * (2 : R) = (2 : R) := by
      rw [hsq]
      ring
    exact hcalc ▸ hmem
  · rw [hpow]
    refine Ideal.span_le.2 ?_
    intro x hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact Ideal.mem_span_singleton.mpr ⟨(2 : R), rfl⟩
    · exact Ideal.mem_span_singleton.mpr ⟨(1 + sqrtd : R), rfl⟩
    · exact Ideal.mem_span_singleton.mpr ⟨(1 + sqrtd : R), by simp [mul_comm]⟩
    · exact Ideal.mem_span_singleton.mpr ⟨(-2 + sqrtd : R), hsq⟩
/-
Package theorems about the factorization of ideals in `Z[√-5]` here. The main results are:
-/
lemma principal_eq_of_le_of_le
  {I J : Ideal R} (h₁ : I ≤ J) (h₂ : J ≤ I) :
  I = J :=
le_antisymm h₁ h₂
lemma in_span_of_eq
  {x y : R} (h : x = y) (hy : y ∈ (I : Ideal R)) :
  x ∈ I :=
by simpa [h] using hy



theorem factorization_of_three :
    span {(3 : R)} = (span {3, 1 + sqrtd}) * (span {3, 1 - sqrtd}) := by
  sorry

theorem factorization_of_one_plus_sqrtd :
    span {(1 + sqrtd : R)} = (span {2, 1 + sqrtd}) * (span {3, 1 + sqrtd}) := by
  sorry

theorem factorization_of_one_minus_sqrtd :
    span {(1 - sqrtd : R)} = (span {2, 1 + sqrtd}) * (span {3, 1 - sqrtd}) := by
  sorry

-- for these: maybe use `N(I) = #(R/I)`, and show in general that an ideal of prime norm is prime

theorem ideal_of_prime_norm_is_prime {R : Type*} [CommRing R] [IsDedekindDomain R]
    [Module.Free ℤ R] (I : Ideal R) (hI : I.absNorm.Prime) : I.IsPrime := by
  apply Ideal.isPrime_of_irreducible_absNorm
  exact hI

theorem isPrime_span_two_one_plus_sqrtd :
    IsPrime (span {2, 1 + sqrtd} : Ideal R) := by
  -- Strategy: Show absNorm = 2 (prime), then use ideal_of_prime_norm_is_prime
  -- apply ideal_of_prime_norm_is_prime
  -- Need to show: (span {2, 1 + sqrtd}).absNorm.Prime
  sorry

theorem isPrime_span_three_one_plus_sqrtd :
    IsPrime (span {3, 1 + sqrtd} : Ideal R) := by
  sorry

theorem isPrime_span_three_minus_plus_sqrtd :
    IsPrime (span {3, 1 - sqrtd} : Ideal R) := by
  sorry
