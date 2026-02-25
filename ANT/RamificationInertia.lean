import ANT.Ideals
import Mathlib.NumberTheory.RamificationInertia.Basic
-- import Mathlib.Tactic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.NumberTheory.QuadraticField

open Ideal Zsqrtd NumberField

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
-- Computed using mathlib definitions (proofs with sorries)
--------------------------------------------------------------------
#check Ideal.span_mul_span
/-- The ramification index of 2 using Ideal.ramificationIdx. -/
theorem ramificationIdx_2 :
    Ideal.ramificationIdx (algebraMap ℤ R) (Ideal.span {(2 : ℤ)}) P2 = 2 := by
  -- By definition: ramificationIdx = sup { n | map f p ≤ P^n }
  -- Since (2)R = P^2, we have pO_K ⊆ P^2
  -- We need to show pO_K ⊈ P^3
  apply Ideal.ramificationIdx_spec
  · -- Show map(ℤ→R)(2) ⊆ P2^2
    simp [Ideal.map_span, ideal_2_factorization]
  · -- Show map(ℤ→R)(2) ⊈ P2^3
    -- If (2) ⊆ P^3, then since (2) = P^2, we'd have P^2 ⊆ P^3
    -- But for a proper prime ideal P, we have P^2 < P^3
    haveI : IsDedekindDomain R := inferInstance
    have h_not_top : P2 ≠ ⊤ := Ideal.IsPrime.ne_top inferInstance
    have h_not_bot : P2 ≠ ⊥ := by
      -- P2 = span {2, 1+√-5} contains 2, which is nonzero in R
      apply ne.symm
      intro h_eq
      have : (2 : R) ∈ (⊥ : Ideal R) := by simp [P2, h_eq]
      exact Ideal.mem_bot.mp this
    -- Now prove ¬span{2} ≤ P2^3
    by_contra h
    -- Simplify: map (span {2}) = span {2}
    replace h : span {(2 : R)} ≤ P2 ^ 3 := by
      simp only [Ideal.map_span, Set.image_singleton] at h
      exact h
    -- If span{2} ≤ P2^3, then since span{2} = P2^2, we'd have P2^2 ≤ P2^3
    -- But for a proper prime ideal, P2^2 < P2^3
    rw [ideal_2_factorization] at h
    -- Use the strict decreasing property of powers for a proper prime ideal
    have := pow_succ_lt_pow inferInstance h_not_bot (i := 1)
    exact this.2 h
















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
