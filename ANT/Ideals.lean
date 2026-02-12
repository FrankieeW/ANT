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

/-- An element of ℤ[√-5] belongs to span {2, 1 + √(-5)} iff re + im is even. -/
private lemma mem_span_two_one_plus_sqrtd_iff (z : R) :
    z ∈ (span ({2, 1 + sqrtd} : Set R) : Ideal R) ↔ Even (z.re + z.im) := by
  constructor
  · intro hz
    rw [Ideal.mem_span_pair] at hz
    obtain ⟨a, b, hab⟩ := hz
    have hre := congr_arg Zsqrtd.re hab
    have him := congr_arg Zsqrtd.im hab
    simp only [Zsqrtd.re_add, Zsqrtd.re_mul, Zsqrtd.im_add, Zsqrtd.im_mul,
               Zsqrtd.sqrtd] at hre him
    -- Simplify concrete values: re 2 = 2, im 2 = 0, re 1 = 1, im 1 = 0
    norm_num at hre him
    exact ⟨a.re + a.im + b.re - 2 * b.im, by linarith⟩
  · intro ⟨k, hk⟩
    rw [Ideal.mem_span_pair]
    refine ⟨⟨k - z.im, 0⟩, ⟨z.im, 0⟩, ?_⟩
    ext
    · simp [Zsqrtd.sqrtd]; linarith
    · simp [Zsqrtd.sqrtd]

-- set_option maxHeartbeats 800000 in
theorem isPrime_span_two_one_plus_sqrtd :
    IsPrime (span {2, 1 + sqrtd} : Ideal R) := by
  rw [Ideal.isPrime_iff]
  refine ⟨?_, ?_⟩
  · -- Show I ≠ ⊤: 1 ∉ I since 1.re + 1.im = 1 is odd
    intro h
    have h1 : (1 : R) ∈ (span ({2, 1 + sqrtd} : Set R) : Ideal R) := by rw [h]; trivial
    rw [mem_span_two_one_plus_sqrtd_iff] at h1
    simp at h1
  · -- Show ∀ a b, a * b ∈ I → a ∈ I ∨ b ∈ I
    intro a b hab
    simp only [mem_span_two_one_plus_sqrtd_iff] at hab ⊢
    -- Key identity: (a*b).re + (a*b).im = (a.re+a.im)*(b.re+b.im) - 6*a.im*b.im
    have key : (a * b).re + (a * b).im =
        (a.re + a.im) * (b.re + b.im) - 6 * a.im * b.im := by
      simp only [Zsqrtd.re_mul, Zsqrtd.im_mul]; ring
    rw [key] at hab
    have h6 : Even (6 * a.im * b.im) := ⟨3 * a.im * b.im, by ring⟩
    have hprod : Even ((a.re + a.im) * (b.re + b.im)) := by
      obtain ⟨k1, hk1⟩ := hab; obtain ⟨k2, hk2⟩ := h6
      exact ⟨k1 + k2, by linarith⟩
    exact Int.even_mul.mp hprod

/-- An element of ℤ[√-5] belongs to span {3, 1 + √(-5)} iff 3 divides re - im. -/
private lemma mem_span_three_one_plus_sqrtd_idx (z : R) :
    z ∈ (span ({3, 1 + sqrtd} : Set R) : Ideal R) ↔ 3 ∣ (z.re - z.im) := by
  constructor
  · intro hz
    rw [Ideal.mem_span_pair] at hz
    obtain ⟨a, b, hab⟩ := hz
    have hre := congr_arg Zsqrtd.re hab
    have him := congr_arg Zsqrtd.im hab
    simp only [Zsqrtd.re_add, Zsqrtd.re_mul, Zsqrtd.im_add, Zsqrtd.im_mul,
               Zsqrtd.sqrtd] at hre him
    norm_num at hre him
    exact ⟨a.re - a.im - 2 * b.im, by linarith⟩
  · intro ⟨k, hk⟩
    rw [Ideal.mem_span_pair]
    refine ⟨⟨k, 0⟩, ⟨z.im, 0⟩, ?_⟩
    ext
    · simp [Zsqrtd.sqrtd]; linarith
    · simp [Zsqrtd.sqrtd]

theorem isPrime_span_three_one_plus_sqrtd :
    IsPrime (span {3, 1 + sqrtd} : Ideal R) := by
  rw [Ideal.isPrime_iff]
  refine ⟨?_, ?_⟩
  · -- Show I ≠ ⊤: 1 ∉ I since 3 ∤ 1.re - 1.im = 1
    intro h
    have h1 : (1 : R) ∈ (span ({3, 1 + sqrtd} : Set R) : Ideal R) := by rw [h]; trivial
    rw [mem_span_three_one_plus_sqrtd_idx] at h1
    norm_num at h1
  · -- Show ∀ a b, a * b ∈ I → a ∈ I ∨ b ∈ I
    intro a b hab
    simp only [mem_span_three_one_plus_sqrtd_idx] at hab ⊢
    -- Key identity: (a*b).re - (a*b).im = (a.re-a.im)*(b.re-b.im) - 6*a.im*b.im
    have key : (a * b).re - (a * b).im =
        (a.re - a.im) * (b.re - b.im) - 6 * a.im * b.im := by
      simp only [Zsqrtd.re_mul, Zsqrtd.im_mul]; ring
    rw [key] at hab
    have h6 : (3 : ℤ) ∣ 6 * a.im * b.im := ⟨2 * a.im * b.im, by ring⟩
    have hprod : (3 : ℤ) ∣ (a.re - a.im) * (b.re - b.im) := by
      obtain ⟨k1, hk1⟩ := hab; obtain ⟨k2, hk2⟩ := h6
      exact ⟨k1 + k2, by linarith⟩
    exact (show Prime (3 : ℤ) by norm_num).dvd_or_dvd hprod

/-- An element of ℤ[√-5] belongs to span {3, 1 - √(-5)} iff 3 divides re + im. -/
private lemma mem_span_three_one_minus_sqrtd_idx (z : R) :
    z ∈ (span ({3, 1 - sqrtd} : Set R) : Ideal R) ↔ 3 ∣ (z.re + z.im) := by
  constructor
  · intro hz
    rw [Ideal.mem_span_pair] at hz
    obtain ⟨a, b, hab⟩ := hz
    have hre := congr_arg Zsqrtd.re hab
    have him := congr_arg Zsqrtd.im hab
    simp only [Zsqrtd.re_add, Zsqrtd.re_mul, Zsqrtd.im_add, Zsqrtd.im_mul,
               Zsqrtd.sqrtd] at hre him
    norm_num at hre him
    exact ⟨a.re + a.im + 2 * b.im, by linarith⟩
  · intro ⟨k, hk⟩
    rw [Ideal.mem_span_pair]
    refine ⟨⟨k - 2 * z.im, 0⟩, ⟨0, z.im⟩, ?_⟩
    ext
    · simp [Zsqrtd.sqrtd]; linarith
    · simp [Zsqrtd.sqrtd]

theorem isPrime_span_three_one_minus_sqrtd :
    IsPrime (span {3, 1 - sqrtd} : Ideal R) := by
  rw [Ideal.isPrime_iff]
  refine ⟨?_, ?_⟩
  · -- Show I ≠ ⊤: 1 ∉ I since 3 ∤ 1.re + 1.im = 2
    intro h
    have h1 : (1 : R) ∈ (span ({3, 1 - sqrtd} : Set R) : Ideal R) := by rw [h]; trivial
    rw [mem_span_three_one_minus_sqrtd_idx] at h1
    norm_num at h1
  · -- Show ∀ a b, a * b ∈ I → a ∈ I ∨ b ∈ I
    intro a b hab
    simp only [mem_span_three_one_minus_sqrtd_idx] at hab ⊢
    -- Key identity: (a*b).re + (a*b).im = (a.re+a.im)*(b.re+b.im) - 6*a.im*b.im
    have key : (a * b).re + (a * b).im =
        (a.re + a.im) * (b.re + b.im) - 6 * a.im * b.im := by
      simp only [Zsqrtd.re_mul, Zsqrtd.im_mul]; ring
    rw [key] at hab
    have h6 : (3 : ℤ) ∣ 6 * a.im * b.im := ⟨2 * a.im * b.im, by ring⟩
    have hprod : (3 : ℤ) ∣ (a.re + a.im) * (b.re + b.im) := by
      obtain ⟨k1, hk1⟩ := hab; obtain ⟨k2, hk2⟩ := h6
      exact ⟨k1 + k2, by linarith⟩
    exact (show Prime (3 : ℤ) by norm_num).dvd_or_dvd hprod
