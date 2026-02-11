import Mathlib

open Ideal Zsqrtd

abbrev R := Zsqrtd (-5)

theorem factorization_of_two :
    span {(2 : R)} = (span {2, 1 + sqrtd}) ^ 2 := by
  apply _root_.le_antisymm
  · 
  · sorry

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
  -- might already be in mathlib: `Ideal.isPrime_of_irreducible_absNorm`
  sorry

theorem isPrime_span_two_one_plus_sqrtd :
    IsPrime (span {2, 1 + sqrtd} : Ideal R) := by
  sorry

theorem isPrime_span_three_one_plus_sqrtd :
    IsPrime (span {3, 1 + sqrtd} : Ideal R) := by
  sorry

theorem isPrime_span_three_minus_plus_sqrtd :
    IsPrime (span {3, 1 - sqrtd} : Ideal R) := by
  sorry
