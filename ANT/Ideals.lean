import ANT.Basic
import ANT.Tactic
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Ideal Zsqrtd ANT.Tactic

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

lemma principal_eq_of_le_of_le
  {I J : Ideal R} (h₁ : I ≤ J) (h₂ : J ≤ I) :
  I = J :=
le_antisymm h₁ h₂
lemma in_span_of_eq
  {x y : R} (h : x = y) (hy : y ∈ (I : Ideal R)) :
  x ∈ I :=
by simpa [h] using hy

/-- If `a` divides every element of `S`, then `span S ≤ span {a}`. -/
lemma span_le_span_singleton_of_forall_dvd
    {α : Type*} [CommSemiring α] {a : α} {S : Set α}
    (h : ∀ x ∈ S, a ∣ x) :
    span S ≤ span {a} :=
  Ideal.span_le.2 fun x hx => Ideal.mem_span_singleton.mpr (h x hx)


theorem factorization_of_three :
    span {(3 : R)} = (span {3, 1 + sqrtd}) * (span {3, 1 - sqrtd}) := by
    rw [Ideal.span_pair_mul_span_pair]
    apply principal_eq_of_le_of_le
    · rw [Ideal.span_singleton_le_iff_mem]
      -- linear_combination
      have three_eq: (3 : R) = 3 * 3 - (1 + sqrtd) * (1 - sqrtd) := by
        ext <;> norm_num [Zsqrtd.sqrtd]
      exact in_span_of_eq three_eq
        ((span _).sub_mem (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp)))
    · apply span_le_span_singleton_of_forall_dvd
      intro x hx
      -- rw [← Ideal.mem_span_singleton]
      rcases hx with rfl  | rfl | rfl | rfl
      · simp
      · simp
      · simp
      · exact ⟨2, by ext <;> norm_num [Zsqrtd.sqrtd]⟩



theorem factorization_of_one_plus_sqrtd :
    span {(1 + sqrtd : R)} = (span {2, 1 + sqrtd}) * (span {3, 1 + sqrtd}) := by
  rw [Ideal.span_pair_mul_span_pair]
  apply principal_eq_of_le_of_le
  · rw [Ideal.span_singleton_le_iff_mem]
    -- 1 + sqrtd = 0 * (2*3) + (-1) * (2*(1+sqrtd)) + 1 * ((1+sqrtd)*3) + 0 * ((1+sqrtd)*(1+sqrtd))
    have one_plus_sqrtd_eq :
        (1 + sqrtd : R) = (1 + sqrtd) * 3 - 2 * (1 + sqrtd) := by ring
    exact in_span_of_eq one_plus_sqrtd_eq
      ((span _).sub_mem (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp)))
  · apply span_le_span_singleton_of_forall_dvd
    intro x hx
    rcases hx with rfl | rfl | rfl | rfl
    · -- 2 * 3 = 6 = (1 + sqrtd) * (1 - sqrtd)
      exact ⟨1 - sqrtd, by ext <;> norm_num [Zsqrtd.sqrtd]⟩
    · -- 2 * (1 + sqrtd) = (1 + sqrtd) * 2
      -- exact ⟨2, by ring⟩
      simp
    · -- (1 + sqrtd) * 3
      -- exact ⟨3, by ring⟩
      simp
    · -- (1 + sqrtd) * (1 + sqrtd)
      -- exact ⟨1 + sqrtd, rfl⟩
      simp

theorem factorization_of_one_minus_sqrtd :
    span {(1 - sqrtd : R)} = (span {2, 1 - sqrtd}) * (span {3, 1 - sqrtd}) := by
  rw [Ideal.span_pair_mul_span_pair]
  apply principal_eq_of_le_of_le
  · rw [Ideal.span_singleton_le_iff_mem]
    have one_mins_sqrtd_eq :
        (1 - sqrtd : R) = (1 - sqrtd) * 3 - 2 * (1 - sqrtd) := by ring
    exact in_span_of_eq one_mins_sqrtd_eq
      ((span _).sub_mem (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp)))
  · apply span_le_span_singleton_of_forall_dvd
    intro x hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨1 + sqrtd, by ext <;> norm_num [Zsqrtd.sqrtd]⟩
    · simp
    · simp
    · simp

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
