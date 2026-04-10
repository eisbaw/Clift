# Lean 4 Version Upgrade Guide

## Current Pin

- **Lean version**: `leanprover/lean4:v4.30.0-rc1`
- **Pinned in**: `lean-toolchain` (single line)
- **lake-manifest.json**: Tracks exact dependency versions
- **No Mathlib dependency** (dropped in commit 8879ba1 for RAM reasons)

## Why We Pin

Lean 4 is pre-1.0 and breaking changes are frequent. seL4 pins to specific
Isabelle versions for the same reason. Our project has 50+ files and ~30 theorems
that could break on any upstream change.

## Before Upgrading

1. **Check the changelog**: https://github.com/leanprover/lean4/releases
2. **Known risk areas** for our codebase:
   - `MetaM` / `Elab` API changes (affects Pipeline, L1Auto, L2Auto, L3Auto, L5Auto)
   - `Tactic` changes (affects all proof files)
   - `Syntax` changes (affects `clift` command parser)
   - Kernel changes (could affect proof checking time or acceptance)
   - `UInt32` / `BitVec` API changes (affects Generated code and specs)
3. **Ensure clean state**: `git status` should be clean, all tests passing

## Upgrade Procedure

```bash
# Step 1: Create upgrade branch
git checkout -b lean-upgrade-vX.Y.Z

# Step 2: Update lean-toolchain
echo "leanprover/lean4:vX.Y.Z" > lean-toolchain

# Step 3: Clean and rebuild from scratch
lake clean
lake build 2>&1 | tee upgrade-build.log

# Step 4: If build fails, categorize errors:
#   - Syntax errors: changed syntax (usually mechanical fix)
#   - Tactic errors: tactic behavior changed (may need proof rewrite)
#   - Kernel errors: proof term rejected (serious, may need redesign)
#   - API errors: MetaM/Elab API changed (update metaprograms)

# Step 5: Fix all errors, then run full test suite
just e2e

# Step 6: Run regression suite
just regression

# Step 7: If everything passes, merge
git checkout main
git merge lean-upgrade-vX.Y.Z
```

## Breaking Change Categories (from past experience)

| Category | Severity | Example | Fix approach |
|----------|----------|---------|-------------|
| Syntax | Low | `#check` output format | Mechanical search-replace |
| Tactic | Medium | `simp` behavior change | May need `simp only` or different lemma set |
| API | Medium | `MetaM.mkFreshExprMVar` signature | Update metaprogram calls |
| Kernel | High | Proof term rejection | May need proof strategy redesign |
| Performance | Medium | Slower heartbeat consumption | Increase `maxHeartbeats` or optimize proofs |

## Version History

| Version | Date | Notes |
|---------|------|-------|
| v4.30.0-rc1 | Current | Release candidate, stable for our use |
| v4.16.0 | Previous | Also installed locally |

## Decision: When to Upgrade

Upgrade when:
- A new stable (non-rc) release fixes bugs we hit
- A new version has features we need (e.g., better `grind`, `omega`)
- Security fix

Do NOT upgrade:
- During active feature development
- Right before a deadline
- To an rc version unless we need specific fixes
