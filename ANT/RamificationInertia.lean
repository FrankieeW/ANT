import ANT.Ideals
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

open Ideal Zsqrtd

-- Note: R is defined in ANT.Ideals

--------------------------------------------------------------------
-- RAMIFICATION AND INERTIA COMPUTATIONS
--------------------------------------------------------------------

-- Results for Q(sqrt(-5)) / Q:
--
-- Prime p = 2:
--   Factorization: (2) = P^2 with P = <2, 1+sqrt(-5)>
--   Ramification index: e = 2
--   Inertia degree: f = 1 (since R/P ~ Z/2Z)
--   Check: e * f = 2 = [Q(sqrt(-5)):Q] OK
--
-- Prime p = 3:
--   Factorization: (3) = P1 * P2 with P1 = <3, 1+sqrt(-5)>, P2 = <3, 1-sqrt(-5)>
--   For each prime: e = 1, f = 1
--   Check: e1*f1 + e2*f2 = 1 + 1 = 2 = [Q(sqrt(-5)):Q] OK

-- Prime ideals in Z[sqrt(-5)]
/-- The prime ideal ⟨2, 1+√-5⟩ in ℤ[√-5]. -/
def P2 : Ideal R := span {2, 1 + sqrtd}

/-- The prime ideal ⟨3, 1+√-5⟩ in ℤ[√-5]. -/
def P3plus : Ideal R := span {3, 1 + sqrtd}

/-- The prime ideal ⟨3, 1-√-5⟩ in ℤ[√-5]. -/
def P3minus : Ideal R := span {3, 1 - sqrtd}

/-- P2 is a prime ideal. -/
instance : P2.IsPrime := isPrime_span_two_one_plus_sqrtd

/-- P3plus is a prime ideal. -/
instance : P3plus.IsPrime := isPrime_span_three_one_plus_sqrtd

/-- P3minus is a prime ideal. -/
instance : P3minus.IsPrime := isPrime_span_three_one_minus_sqrtd

/-- The ideal (2) in ℤ[√-5] equals P2^2. -/
theorem ideal_2_factorization : span {(2 : R)} = P2 ^ 2 :=
  factorization_of_two

/-- The ideal (3) in ℤ[√-5] equals P3plus * P3minus. -/
theorem ideal_3_factorization : span {(3 : R)} = P3plus * P3minus :=
  factorization_of_three



--------------------------------------------------------------------
-- Computed using mathlib definitions
--------------------------------------------------------------------

/-- The ramification index of 2 using Ideal.ramificationIdx. -/
theorem ramificationIdx_2 :
    Ideal.ramificationIdx (algebraMap ℤ R) (Ideal.span {(2 : ℤ)}) P2 = 2 := by
  apply Ideal.ramificationIdx_spec
  · -- Show map(ℤ→R)(span{2}) ≤ P2^2
    simp only [Ideal.map_span, Set.image_singleton, map_ofNat]
    exact le_of_eq ideal_2_factorization
  · -- Show ¬(map(ℤ→R)(span{2}) ≤ P2^3)
    simp only [Ideal.map_span, Set.image_singleton, map_ofNat,
               Ideal.span_singleton_le_iff_mem]
    -- Need: (2:R) ∉ P2^3
    -- Key: P2^3 = P2^2 * P2 = span{2} * P2, so 2 ∈ P2^3 → 1 ∈ P2 → P2 = ⊤
    rw [pow_succ, ← ideal_2_factorization, Ideal.mem_span_singleton_mul]
    rintro ⟨z, hz, heq⟩
    -- From 2 * z = 2, extract coordinates to get z = 1
    have hone : z = 1 := by
      have hre := congr_arg Zsqrtd.re heq
      have him := congr_arg Zsqrtd.im heq
      simp only [Zsqrtd.re_mul, Zsqrtd.im_mul] at hre him
      norm_num at hre him
      exact Zsqrtd.ext hre him
    -- But 1 ∈ P2 contradicts P2 ≠ ⊤
    rw [hone] at hz
    have : P2 ≠ ⊤ := Ideal.IsPrime.ne_top (inferInstance : P2.IsPrime)
    exact this ((Ideal.eq_top_iff_one (I := P2)).mpr hz)

/-- The inertia degree of P2 using Ideal.inertiaDeg. -/
theorem inertiaDeg_2 : (Ideal.span {(2 : ℤ)}).inertiaDeg P2 = 1 := by
  sorry

/-- The ramification index of P3plus using Ideal.ramificationIdx. -/
theorem ramificationIdx_3_P3plus :
    Ideal.ramificationIdx (algebraMap ℤ R) (Ideal.span {(3 : ℤ)}) P3plus = 1 := by
  sorry

/-- The inertia degree of P3plus using Ideal.inertiaDeg. -/
theorem inertiaDeg_3_P3plus : (Ideal.span {(3 : ℤ)}).inertiaDeg P3plus = 1 := by
  sorry

/-- The ramification index of P3minus using Ideal.ramificationIdx. -/
theorem ramificationIdx_3_P3minus :
    Ideal.ramificationIdx (algebraMap ℤ R) (Ideal.span {(3 : ℤ)}) P3minus = 1 := by
  sorry

/-- The inertia degree of P3minus using Ideal.inertiaDeg. -/
theorem inertiaDeg_3_P3minus : (Ideal.span {(3 : ℤ)}).inertiaDeg P3minus = 1 := by
  sorry
