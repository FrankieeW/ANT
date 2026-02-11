# Agent Instructions

This project uses **bd** (beads) for issue tracking. Run `bd onboard` to get started.

## Quick Reference

```bash
bd ready              # Find available work
bd show <id>          # View issue details
bd update <id> --status in_progress  # Claim work
bd close <id>         # Complete work
bd sync               # Sync with git
```

---

## Project Overview

This is a **Lean 4** algebraic number theory project focused on proving properties of ideals in quadratic integer rings, specifically `ℤ[√-5]`. The project uses the Lean Lake build system and depends on Mathlib v4.28.0-rc1.

## Build, Test, and Lint Commands

### Building

```bash
# Build entire project
lake build

# Build specific target
lake build ANT

# Build specific module
lake build ANT.Ideals

# Build specific file
lake build ANT/Ideals.lean

# Clean build artifacts
lake clean

# Update dependencies
lake update
```

### Testing

Lean 4 uses interactive proof verification rather than traditional unit tests. To test:

```bash
# Build all files (verifies all proofs)
lake build

# Check a specific file for errors
lake env lean ANT/Ideals.lean

# Check a single file without rebuilding dependencies
lake env lean --server ANT/Ideals.lean
```

**Running test/example files:**
```bash
lake env lean test_norms.lean
```

### Linting

```bash
# Check if lint driver is configured
lake check-lint

# Run linter (if configured)
lake lint
```

**Manual style checks:**
- Use `#check` to verify types
- Use `#eval` to compute values
- Ensure no `sorry` in completed proofs (unless explicitly marked as TODO)

### Continuous Integration

The project uses GitHub Actions (`.github/workflows/lean_action_ci.yml`):
- Automatically builds on push/PR
- Generates documentation via `docgen`
- Deploys docs to GitHub Pages

---

## Code Style Guidelines

### General Principles

1. **Mathlib conventions**: Follow [Mathlib style guide](https://leanprover-community.github.io/contribute/style.html)
2. **Proof clarity**: Prioritize readable proofs over clever one-liners
3. **Documentation**: Add doc comments (`/-- ... -/`) for all public definitions/theorems
4. **Incremental proofs**: Break complex proofs into lemmas

### Naming Conventions

| Item | Convention | Example |
|------|------------|---------|
| Theorems | `snake_case` | `factorization_of_two` |
| Lemmas | `snake_case` | `principal_eq_of_le_of_le` |
| Definitions | `camelCase` | `isPrime` (follows Mathlib) |
| Abbreviations | `PascalCase` | `abbrev R := Zsqrtd (-5)` |
| Variables | `snake_case` or single letter | `I`, `J`, `h₁`, `hsq` |
| Tactics | `snake_case` | `factorization_setup` |

### File Organization

```
ANT/
  Basic.lean        # Basic definitions and utilities
  Ideals.lean       # Ideal factorization theorems
  ...
ANT.lean            # Main entry point (imports all modules)
test_*.lean         # Exploratory/test files (not imported by ANT.lean)
```

### Import Style

```lean
-- Always import Mathlib first
import Mathlib

-- Open namespaces after imports
open Ideal Zsqrtd

-- Define abbreviations early
abbrev R := Zsqrtd (-5)
```

### Type Annotations

```lean
-- Explicit types for clarity
let J : Ideal R := span {...}

-- Unicode symbols for mathematical notation
(I : Ideal R)  -- type ascription
(2 : R)        -- literal coercion
```

### Proof Structure

**Structured proofs (preferred):**
```lean
theorem my_theorem : statement := by
  -- Strategy comment
  have h₁ : ... := by ...
  have h₂ : ... := by ...
  apply some_lemma
  · -- Goal 1
    exact h₁
  · -- Goal 2
    exact h₂
```

**Term-mode proofs (for simple cases):**
```lean
lemma simple_fact : x = y :=
  le_antisymm h₁ h₂
```

### Tactics Style

- Use `;` for sequencing only when intentional
- Prefer `·` (interpunct) for focusing on goals
- Use `by simp` sparingly; prefer explicit rewrites
- Add comments before complex tactic sequences
- Use `sorry` with TODO comments for incomplete proofs

**Custom tactics:**
```lean
-- Define syntax
syntax (name := myTactic) "my_tactic" : tactic

-- Implement with macro_rules
macro_rules
  | `(tactic| my_tactic) => `(tactic| refine ...; ...)
```

### Error Handling

Lean uses dependent types for safety; runtime errors are rare. For partial functions:

```lean
-- Prefer total functions with Option/Except
def safeDivide (n m : ℕ) : Option ℕ := ...

-- Document preconditions in docstrings
/-- Division assuming m ≠ 0. -/
def divide (n m : ℕ) (h : m ≠ 0) : ℕ := ...
```

### Unicode Input

Lean supports Unicode math symbols. Use VSCode/Emacs abbreviations:

- `\alpha` → α
- `\to` → →
- `\le` → ≤
- `\in` → ∈
- `\cdot` → ·
- `\^2` → ²
- `\Z` → ℤ
- `\N` → ℕ
- `\R` → ℝ

**Subscripts/superscripts:**
- `h\1` → h₁
- `x\^n` → xⁿ

### Project-Specific Patterns

#### Working with Ideals

```lean
-- Standard pattern for ideal equality
apply _root_.le_antisymm
· -- Show I ≤ J
  rw [Ideal.span_singleton_le_iff_mem]
  ...
· -- Show J ≤ I
  refine Ideal.span_le.2 ?_
  intro x hx
  ...
```

#### Factorization Proofs

```lean
-- Use custom tactic for setup
factorization_setup
· -- First direction
  ...
· -- Second direction
  ...
```

#### Working with Zsqrtd

```lean
-- Ring-specific calculations
ext ⟨⟩  -- Extensionality for Zsqrtd
norm_num [Zsqrtd.sqrtd]  -- Normalize square root expressions
```

### Common Gotchas

1. **`sorry` tracking**: Use `#check @sorryAx` or search for `sorry` before committing
2. **Implicit arguments**: Use `@` to make implicit args explicit when debugging
3. **Type class resolution**: If stuck, try `haveI` or `letI` to provide instances manually
4. **Namespace pollution**: Minimize `open` directives; prefer qualified names
5. **Slow builds**: Use `lake build` incrementally; avoid touching heavily-imported files

### Documentation

```lean
/-- Brief one-line description.

Detailed explanation with LaTeX math: `$x^2 + y^2 = z^2$`.

**Example:**
```lean
example : factorization_of_two := by ...
```
-/
theorem factorization_of_two : ... := by ...
```

### LSP Integration

The Lean Language Server provides:
- **Infoview**: Shows goal state during proof development
- **Go to definition**: Ctrl+Click or F12
- **Hover**: Shows type information
- **Error diagnostics**: Real-time feedback

**Workflow:**
1. Write theorem statement
2. Add `by` to enter tactic mode
3. Use Infoview to see goals
4. Apply tactics incrementally
5. Check for orange bars (errors) and blue bars (warnings)

---

## Landing the Plane (Session Completion)

**When ending a work session**, you MUST complete ALL steps below. Work is NOT complete until `git push` succeeds.

**MANDATORY WORKFLOW:**

1. **File issues for remaining work** - Create issues for anything that needs follow-up
2. **Run quality gates** (if code changed):
   ```bash
   lake build         # All proofs must verify
   lake env lean test_norms.lean  # Run exploratory tests
   ```
3. **Update issue status** - Close finished work, update in-progress items
4. **PUSH TO REMOTE** - This is MANDATORY:
   ```bash
   git pull --rebase
   bd sync
   git push
   git status  # MUST show "up to date with origin"
   ```
5. **Clean up** - Clear stashes, prune remote branches
6. **Verify** - All changes committed AND pushed
7. **Hand off** - Provide context for next session

**CRITICAL RULES:**
- Work is NOT complete until `git push` succeeds
- NEVER stop before pushing - that leaves work stranded locally
- NEVER say "ready to push when you are" - YOU must push
- If push fails, resolve and retry until it succeeds
- NO `sorry` in committed code without explicit TODO comment + issue filed
