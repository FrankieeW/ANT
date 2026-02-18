# Mathlib Gap Matrix (Quadratic / Zsqrtd Focus)

## Legend
- status: `exists` | `partial` | `missing`
- proof-path choice: `membership-criterion` | `absNorm-based` | `hybrid`
- scope: `generic` | `Zsqrtd d` | `d = -5 local`

| candidate lemma/theme | status | nearest theorem(s) + URL | repeat-pattern fingerprint (local) | proof-path choice | scope | confidence |
| --- | --- | --- | --- | --- | --- | --- |
| Membership in two-generator ideal | exists | `Ideal.mem_span_pair` — https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Ideal/Span.html#Ideal.mem_span_pair | Repeated in `ANT/Ideals.lean` private `mem_span_*_iff` proofs via coeff extraction | membership-criterion | generic | high |
| Product of two 2-generator spans | exists | `Ideal.span_pair_mul_span_pair` — https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Ideal/Operations.html#Ideal.span_pair_mul_span_pair | Repeated in `factorization_of_three`, `factorization_of_one_plus_sqrtd`, `factorization_of_one_minus_sqrtd` | membership-criterion | generic | high |
| absNorm irreducible => prime ideal | exists | `Ideal.isPrime_of_irreducible_absNorm` — https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Ideal/Norm/AbsNorm.html#Ideal.isPrime_of_irreducible_absNorm | Wrapper appears as `ideal_of_prime_norm_is_prime` | absNorm-based | generic | high |
| Dirichlet unit theorem in number fields | exists | `NumberField.Units.exist_unique_eq_mul_prod` and related APIs — https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/NumberField/Units/DirichletTheorem.html | N/A | N/A | generic | high |
| Pell theory completeness baseline | exists (substantial) | `Mathlib/NumberTheory/Pell.lean`, `Mathlib/NumberTheory/PellMatiyasevic.lean` | N/A | N/A | generic | high |
| Class-number finiteness baseline | exists | `Mathlib/NumberTheory/ClassNumber/Finite.lean`, `Mathlib/NumberTheory/NumberField/ClassNumber.lean` | N/A | N/A | generic | high |
| Zsqrtd-specific congruence membership criteria APIs (e.g. parity/divisibility on `re/im`) | partial/missing | nearest: generic `Ideal.mem_span_pair`; `Zsqrtd.Basic` has arithmetic/norm only — https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/Zsqrtd/Basic.html | `mem_span_two_one_plus_sqrtd_iff`, `mem_span_three_one_plus_sqrtd_idx`, `mem_span_three_one_minus_sqrtd_idx` | membership-criterion | Zsqrtd d | medium-high |
| Helper lemmas wrapping span-product reverse-inclusion boilerplate | partial/missing | nearest: `Ideal.span_pair_mul_span_pair` + general span lemmas | repeated `le_antisymm` + 4-generator split + `mem_span_singleton` witness pattern | membership-criterion | generic | medium-high |
| Explicit prime-ideal criteria for concrete `Zsqrtd d` two-generator ideals | partial/missing | nearest: generic `Ideal.isPrime_iff`, absNorm lemmas | repeated in `isPrime_span_two_one_plus_sqrtd`, `isPrime_span_three_*` | hybrid | Zsqrtd d / d=-5 local | medium |
| Ring-of-integers explicit bridge for quadratic orders by `d mod 4` | partial/missing (explicit ergonomic layer) | nearest: general `RingOfIntegers` framework in NumberField; `Zsqrtd.Basic` separate | no direct local abstraction yet | hybrid | Zsqrtd d -> NumberField bridge | medium |

## Current decisions (for execution)

1. Keep `factorization_Zsqrtd_mins_5` as setup automation only; move mathematical substance into named lemmas.
2. For primality proofs: default to `membership-criterion`; use `absNorm-based` support lemmas only where they shorten exclusion/divisibility subgoals.
3. Any generalization claim must declare scope (`Zsqrtd d` vs full ring of integers) and include `d mod 4` caveat when relevant.
4. Hard gate before/after edits: `rg -n "\bsorry\b|\badmit\b" ANT/*.lean test_*.lean`.
