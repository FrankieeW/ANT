import Mathlib

open Ideal Zsqrtd

namespace ANT.Tactic

private abbrev R := Zsqrtd (-5)

/-- Helper: convert the goal to `h` and close the equality by `ring` or `ext + norm_num`. -/
scoped macro "try_eq " h:term : tactic =>
  `(tactic| (convert ($h) using 1; first | ring | (ext <;> norm_num [Zsqrtd.sqrtd])))

syntax (name := factorizationZsqrtdMins5) "factorization_Zsqrtd_mins_5" : tactic

macro_rules
  | `(tactic| factorization_Zsqrtd_mins_5) =>
      `(tactic|
        first
        | -- Product case: span {p} = span {a1, a2} * span {b1, b2}
          refine
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
            have hg1 : ?a1 * ?b1 ∈ J := Ideal.subset_span (by simp)
            have hg2 : ?a1 * ?b2 ∈ J := Ideal.subset_span (by simp)
            have hg3 : ?a2 * ?b1 ∈ J := Ideal.subset_span (by simp)
            have hg4 : ?a2 * ?b2 ∈ J := Ideal.subset_span (by simp)
            first
            | exact hg1 | exact hg2 | exact hg3 | exact hg4
            | try_eq (J.sub_mem hg1 hg2) | try_eq (J.sub_mem hg1 hg3)
            | try_eq (J.sub_mem hg1 hg4) | try_eq (J.sub_mem hg2 hg1)
            | try_eq (J.sub_mem hg2 hg3) | try_eq (J.sub_mem hg2 hg4)
            | try_eq (J.sub_mem hg3 hg1) | try_eq (J.sub_mem hg3 hg2)
            | try_eq (J.sub_mem hg3 hg4) | try_eq (J.sub_mem hg4 hg1)
            | try_eq (J.sub_mem hg4 hg2) | try_eq (J.sub_mem hg4 hg3)
            | try_eq (J.sub_mem (J.sub_mem hg1 hg2) hg3)
            | try_eq (J.sub_mem (J.sub_mem hg1 hg2) hg4)
            | try_eq (J.sub_mem (J.sub_mem hg1 hg3) hg2)
            | try_eq (J.sub_mem (J.sub_mem hg1 hg3) hg4)
            | try_eq (J.sub_mem (J.sub_mem hg1 hg4) hg2)
            | try_eq (J.sub_mem (J.sub_mem hg1 hg4) hg3)
            | try_eq (J.sub_mem (J.sub_mem hg2 hg1) hg3)
            | try_eq (J.sub_mem (J.sub_mem hg2 hg1) hg4)
            | try_eq (J.sub_mem (J.sub_mem hg2 hg3) hg1)
            | try_eq (J.sub_mem (J.sub_mem hg2 hg3) hg4)
            | try_eq (J.sub_mem (J.sub_mem hg2 hg4) hg1)
            | try_eq (J.sub_mem (J.sub_mem hg2 hg4) hg3)
            | try_eq (J.sub_mem (J.sub_mem hg3 hg1) hg2)
            | try_eq (J.sub_mem (J.sub_mem hg3 hg1) hg4)
            | try_eq (J.sub_mem (J.sub_mem hg3 hg2) hg1)
            | try_eq (J.sub_mem (J.sub_mem hg3 hg2) hg4)
            | try_eq (J.sub_mem (J.sub_mem hg3 hg4) hg1)
            | try_eq (J.sub_mem (J.sub_mem hg3 hg4) hg2)
            | try_eq (J.sub_mem (J.sub_mem hg4 hg1) hg2)
            | try_eq (J.sub_mem (J.sub_mem hg4 hg1) hg3)
            | try_eq (J.sub_mem (J.sub_mem hg4 hg2) hg1)
            | try_eq (J.sub_mem (J.sub_mem hg4 hg2) hg3)
            | try_eq (J.sub_mem (J.sub_mem hg4 hg3) hg1)
            | try_eq (J.sub_mem (J.sub_mem hg4 hg3) hg2)
          · rw [hmul]
            refine Ideal.span_le.2 ?_
            intro x hx
            rcases hx with rfl | rfl | rfl | rfl
            <;> first
              | exact Ideal.mem_span_singleton.mpr ⟨_, by ring⟩
              | exact Ideal.mem_span_singleton.mpr
                  ⟨_, by ext ⟨⟩ <;> norm_num [Zsqrtd.sqrtd]⟩
        | -- Squared case: span {p} = span {a1, a2} ^ 2
          refine
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
            have hg1 : ?a1 * ?a1 ∈ J := Ideal.subset_span (by simp)
            have hg2 : ?a1 * ?a2 ∈ J := Ideal.subset_span (by simp)
            have hg3 : ?a2 * ?a1 ∈ J := Ideal.subset_span (by simp)
            have hg4 : ?a2 * ?a2 ∈ J := Ideal.subset_span (by simp)
            first
            | exact hg1 | exact hg2 | exact hg3 | exact hg4
            | try_eq (J.sub_mem hg1 hg2) | try_eq (J.sub_mem hg1 hg3)
            | try_eq (J.sub_mem hg1 hg4) | try_eq (J.sub_mem hg2 hg1)
            | try_eq (J.sub_mem hg2 hg3) | try_eq (J.sub_mem hg2 hg4)
            | try_eq (J.sub_mem hg3 hg1) | try_eq (J.sub_mem hg3 hg2)
            | try_eq (J.sub_mem hg3 hg4) | try_eq (J.sub_mem hg4 hg1)
            | try_eq (J.sub_mem hg4 hg2) | try_eq (J.sub_mem hg4 hg3)
            | try_eq (J.sub_mem (J.sub_mem hg1 hg2) hg3)
            | try_eq (J.sub_mem (J.sub_mem hg1 hg2) hg4)
            | try_eq (J.sub_mem (J.sub_mem hg1 hg3) hg2)
            | try_eq (J.sub_mem (J.sub_mem hg1 hg3) hg4)
            | try_eq (J.sub_mem (J.sub_mem hg1 hg4) hg2)
            | try_eq (J.sub_mem (J.sub_mem hg1 hg4) hg3)
            | try_eq (J.sub_mem (J.sub_mem hg2 hg1) hg3)
            | try_eq (J.sub_mem (J.sub_mem hg2 hg1) hg4)
            | try_eq (J.sub_mem (J.sub_mem hg2 hg3) hg1)
            | try_eq (J.sub_mem (J.sub_mem hg2 hg3) hg4)
            | try_eq (J.sub_mem (J.sub_mem hg2 hg4) hg1)
            | try_eq (J.sub_mem (J.sub_mem hg2 hg4) hg3)
            | try_eq (J.sub_mem (J.sub_mem hg3 hg1) hg2)
            | try_eq (J.sub_mem (J.sub_mem hg3 hg1) hg4)
            | try_eq (J.sub_mem (J.sub_mem hg3 hg2) hg1)
            | try_eq (J.sub_mem (J.sub_mem hg3 hg2) hg4)
            | try_eq (J.sub_mem (J.sub_mem hg3 hg4) hg1)
            | try_eq (J.sub_mem (J.sub_mem hg3 hg4) hg2)
            | try_eq (J.sub_mem (J.sub_mem hg4 hg1) hg2)
            | try_eq (J.sub_mem (J.sub_mem hg4 hg1) hg3)
            | try_eq (J.sub_mem (J.sub_mem hg4 hg2) hg1)
            | try_eq (J.sub_mem (J.sub_mem hg4 hg2) hg3)
            | try_eq (J.sub_mem (J.sub_mem hg4 hg3) hg1)
            | try_eq (J.sub_mem (J.sub_mem hg4 hg3) hg2)
          · rw [hpow, hmul]
            refine Ideal.span_le.2 ?_
            intro x hx
            rcases hx with rfl | rfl | rfl | rfl
            <;> first
              | exact Ideal.mem_span_singleton.mpr ⟨_, by ring⟩
              | exact Ideal.mem_span_singleton.mpr
                  ⟨_, by ext ⟨⟩ <;> norm_num [Zsqrtd.sqrtd]⟩)

end ANT.Tactic
