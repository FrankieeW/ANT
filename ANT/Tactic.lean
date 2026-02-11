import Mathlib

open Ideal Zsqrtd

namespace ANT.Tactic

private abbrev R := Zsqrtd (-5)

syntax (name := factorizationZsqrtdMins5) "factorization_Zsqrtd_mins_5" : tactic

macro_rules
  | `(tactic| factorization_Zsqrtd_mins_5) =>
      `(tactic|
        first
        | refine
            (show span {(?p : R)} =
                (span ({?a1, ?a2} : Set R) : Ideal R) *
                (span ({?b1, ?b2} : Set R) : Ideal R) from ?_)
          let J : Ideal R :=
            span ({?a1 * ?b1, ?a1 * ?b2, ?a2 * ?b1, ?a2 * ?b2} : Set R)
          have hmul :
              (span ({?a1, ?a2} : Set R) : Ideal R) *
              (span ({?b1, ?b2} : Set R) : Ideal R) = J := by
            unfold J
            rw [Ideal.span_pair_mul_span_pair]
            rfl
          apply _root_.le_antisymm
          · rw [Ideal.span_singleton_le_iff_mem, hmul]
          · rw [hmul]
            refine Ideal.span_le.2 ?_
            intro x hx
            rcases hx with rfl | rfl | rfl | rfl
            <;> first
              | exact Ideal.mem_span_singleton.mpr ⟨_, by ring⟩
              | exact Ideal.mem_span_singleton.mpr
                  ⟨_, by ext ⟨⟩ <;> norm_num [Zsqrtd.sqrtd]⟩
        | refine
            (show span {(?p : R)} =
                (span ({?a1, ?a2} : Set R) : Ideal R) ^ 2 from ?_)
          let I : Ideal R := (span ({?a1, ?a2} : Set R) : Ideal R)
          let J : Ideal R :=
            span ({?a1 * ?a1, ?a1 * ?a2, ?a2 * ?a1, ?a2 * ?a2} : Set R)
          have hpow : I ^ 2 = I * I := pow_two I
          have hmul : I * I = J := by
            unfold I J
            rw [Ideal.span_pair_mul_span_pair]
            rfl
          apply _root_.le_antisymm
          · rw [Ideal.span_singleton_le_iff_mem, hpow, hmul]
          · rw [hpow, hmul]
            refine Ideal.span_le.2 ?_
            intro x hx
            rcases hx with rfl | rfl | rfl | rfl
            <;> first
              | exact Ideal.mem_span_singleton.mpr ⟨_, by ring⟩
              | exact Ideal.mem_span_singleton.mpr
                  ⟨_, by ext ⟨⟩ <;> norm_num [Zsqrtd.sqrtd]⟩)

end ANT.Tactic

-- CHECK
theorem factorization_of_three :
    span {(3 : R)} = (span {3, 1 + sqrtd}) * (span {3, 1 - sqrtd}) := by
  factorization_Zsqrtd_mins_5
