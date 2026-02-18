# Mathlib Gap: Zsqrtd Ideals Implementation Plan (Revised)

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Extract reusable ideal-theory helpers from this ANT project, refactor local `Zsqrtd (-5)` proofs onto those helpers, and prepare a minimal upstreamable PR set.

**Architecture:** Two layers only: (1) generic helper lemmas (mathlib-candidate), (2) `d = -5` concrete corollaries (local). Before implementation, lock explicit theorem signatures and proof-path choices in a matrix to avoid vague extraction.

**Tech Stack:** Lean 4, Mathlib, Lake, Loogle/LeanSearch, GitHub PR workflow.

---

## Scope + Assumptions (must be explicit)

- Existing mathlib anchors (do not duplicate):
  - `Ideal.mem_span_pair`
  - `Ideal.span_pair_mul_span_pair`
  - `Ideal.isPrime_of_irreducible_absNorm`
- Current ANT implementation target: `R := Zsqrtd (-5)`.
- **Quadratic-order scope guard:**
  - `Zsqrtd d` is not automatically the full ring of integers for all `d`.
  - For `d ≡ 1 (mod 4)`, expected ring-of-integers representation differs (`ℤ[(1+√d)/2]`), so any `Zsqrtd` theorem must state applicability limits.
- Upstream priority is helper ergonomics + bridge lemmas, not re-proving large foundational number-theory theorems already in mathlib.

---

### Task 1: Baseline and inventory lock

**Files:**
- Modify: `docs/plans/2026-02-17-mathlib-gap-zsqrtd-ideals.md`
- Read: `ANT/Ideals.lean`, `ANT/Tactic.lean`

**Step 1: Confirm current declarations and repeated patterns**
Run: `rg -n "^(theorem|lemma|def|abbrev)\s" ANT/*.lean`
Expected: concentration in `ANT/Ideals.lean`.

**Step 2: Confirm hotspots used in this plan**
Run: `rg -n "factorization_Zsqrtd_mins_5|principal_eq_of_le_of_le|in_span_of_eq|span_le_span_singleton_of_forall_dvd|mem_span_.*_iff|isPrime_span" ANT/Ideals.lean ANT/Tactic.lean`
Expected: direct anchors for extraction work.

**Step 3: Hard gate on unfinished proofs (baseline)**
Run: `rg -n "\bsorry\b|\badmit\b" ANT/*.lean`
Expected: no hits.

---

### Task 2: Candidate matrix with decision columns

**Files:**
- Create: `docs/mathlib-gap-matrix.md`

**Required columns (no exceptions):**
1. candidate lemma/theme
2. exists/partial/missing
3. nearest theorem(s) + URL
4. **repeat-pattern fingerprint** (where repetition occurs)
5. **proof-path choice** (`membership-criterion` vs `absNorm-based`)
6. scope (`generic`, `Zsqrtd d`, `d=-5 only`)
7. confidence (`high/medium/low`)

**Step 1: Seed existing-theorem rows**
Include exact URL-backed rows for the 3 known anchors above.

**Step 2: Seed candidate rows from local repetition**
- congruence-style `mem_span_*_iff` extraction family
- span-product reverse inclusion boilerplate wrappers
- explicit prime-ideal criteria wrappers for concrete spans

**Step 3: Record proof-path decision point for prime proofs**
For each prime theorem, state whether local proof remains pedagogical (`Ideal.isPrime_iff` + membership criteria) or refactors to shorter norm path where assumptions are available.

---

### Task 3: Signature-locked helper extraction (before coding anything else)

**Files:**
- Create: `ANT/UpstreamPrep.lean`
- Modify: `ANT.lean` (import only after compile success)

**Step 1: Lock 2-3 concrete candidate signatures**
Start with these draft signatures (validate against existing names before proving):

```lean
lemma span_singleton_eq_of_mem_and_span_le
    {α : Type*} [CommSemiring α] {p : α} {J : Ideal α}
    (hp : p ∈ J) (hJ : J ≤ Ideal.span ({p} : Set α)) :
    Ideal.span ({p} : Set α) = J

lemma span_pair_mul_span_pair_le_span_singleton_of_dvd
    {α : Type*} [CommSemiring α] {a b c d p : α}
    (h11 : p ∣ a * c) (h12 : p ∣ a * d)
    (h21 : p ∣ b * c) (h22 : p ∣ b * d) :
    (Ideal.span ({a, b} : Set α) * Ideal.span ({c, d} : Set α)) ≤
      Ideal.span ({p} : Set α)

lemma span_pair_sq_le_span_singleton_of_dvd
    {α : Type*} [CommSemiring α] {a b p : α}
    (h11 : p ∣ a * a) (h12 : p ∣ a * b)
    (h21 : p ∣ b * a) (h22 : p ∣ b * b) :
    ((Ideal.span ({a, b} : Set α) : Ideal α) ^ 2) ≤
      Ideal.span ({p} : Set α)
```

**Step 2: De-dup check before implementation**
For each candidate:
- Loogle search exact/near names
- record nearest theorem + insufficiency note in matrix
- skip candidate if duplicate

**Step 3: Implement only smallest non-duplicate subset**
Run: `lake build ANT/UpstreamPrep.lean`
Expected: isolated compile success.

---

### Task 4: Decide tactic role, then refactor one block at a time

**Files:**
- Modify: `ANT/Ideals.lean`
- Optional modify: `ANT/Tactic.lean`

**Decision gate (must be written in matrix first):**
- **Option A (recommended first):** keep `factorization_Zsqrtd_mins_5` local and extract theorem-level helpers in `UpstreamPrep.lean`.
- **Option B:** actively refactor theorem proofs to use `factorization_Zsqrtd_mins_5` where applicable.

Do not mix A/B in same pass.

**Step 1: Refactor target order**
1. `factorization_of_three`
2. `factorization_of_one_plus_sqrtd`
3. `factorization_of_one_minus_sqrtd`

**Step 2: Preserve theorem statements**
Only change proof bodies.

**Step 3: Rebuild after each theorem**
Run: `lake build ANT/Ideals.lean`
Expected: green after each replacement.

---

### Task 5: Controlled generalization pre-work (before multi-d jump)

**Files:**
- Create: `docs/quadratic-generalization-notes.md`

**Step 1: Pencil-and-paper coefficient audit**
Document which terms are truly `d`-generic and which are `d`-dependent (e.g. constants arising from `sqrtd * sqrtd = d`).

**Step 2: Split theorem families by portability**
- generic skeleton
- requires per-`d` arithmetic witness

**Step 3: Only then add pilot file**
Create `ANT/QuadraticOrderTemplates.lean` and `test_quadratic_templates.lean` for one pilot `d`.

---

### Task 6: Verification gates (hard)

**Files:**
- Verify: all modified `.lean` files and new docs

**Step 1: No unfinished proofs gate**
Run: `rg -n "\bsorry\b|\badmit\b" ANT/*.lean test_*.lean`
Expected: zero hits.

**Step 2: Module-level builds**
Run:
- `lake build ANT/UpstreamPrep.lean`
- `lake build ANT/Ideals.lean`

Expected: pass.

**Step 3: Full verification**
Run:
- `lake build`
- `lake env lean test_norms.lean`
- `lake env lean test_quadratic_templates.lean` (if created)

Expected: pass.

---

### Task 7: Upstream packaging prep

**Files:**
- Create: `docs/upstream-pr-draft.md`
- Create: `docs/upstream-checklist.md`

**Step 1: PR-1 scope**
Only generic helper lemmas + tests/examples proving usefulness.

**Step 2: Mandatory per-lemma evidence**
- nearest existing theorem
- why insufficient
- why statement is generally useful beyond `d=-5`

**Step 3: PR-2 scope (local repo)**
Consume PR-1 lemmas to simplify `ANT/Ideals.lean`.

---

## Expanded Roadmap (updated)

### Track A (now): Proof Ergonomics
- Extract and consume helper lemmas to remove repeated inclusion boilerplate.

### Track B (after A): Prime-proof methodology alignment
- Decide and document when to prefer pedagogical membership proofs vs norm-based concise proofs.

### Track C (moved earlier in planning): Ring-of-integers bridge constraints
- Explicitly state applicability domain (`Zsqrtd d` vs full `𝓞 K`) before any generalization claims.

### Track D (later): Multi-discriminant pilots
- Run one extra `d` pilot only after coefficient audit is complete.

---

## Definition of Done

- `docs/mathlib-gap-matrix.md` exists with decision columns and URL evidence.
- At least one non-duplicate helper lemma in `ANT/UpstreamPrep.lean` compiles.
- `ANT/Ideals.lean` has at least one theorem block refactored with unchanged statement.
- Hard gate `sorry/admit` check is clean.
- `lake build` full pass.
- Upstream draft/checklist are ready.
