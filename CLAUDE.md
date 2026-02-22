# CLAUDE.md -- GenSeq

## Problem

Formalise generating sequences for arbitrary groups and prove Theorem 5.16 from Schwiering
(2023): the Sambale sequence `Ξ_n` generates `Sn` for all `n`. A generating sequence is a
finite list `l` in a group `G` whose ordered span `{ gₘ^{bₘ}*…*g₁^{b₁} | bᵢ∈{0,1} }`
equals `G`.

## Critical API Note

**`Equiv.Perm.extendDomain` takes a `RightInverse` / `Subtype` argument** — check the exact
Mathlib 4.28 signature before committing to it for the map R. Fallback: define `mapR` by
cases on `Fin.cases` directly. Also, **`Nat.clog 2 n`** (not `Nat.log`) is ⌈log₂ n⌉.

## Build Command

```bash
lake build GenSeq 2>&1 | tail -40
```

**NEVER run bare `lake build`** -- it rebuilds all of mathlib (~2 hours).

## Project Structure

- `GenSeq/` -- Lean 4 source files
- `HANDOFF.md` -- Mathematical analysis and implementation plan
- `AGENTS.md` -- Agent workflow rules (issue tracking, session completion, push policy)

## Workflow

1. Read `HANDOFF.md` first
2. Read `AGENTS.md` next
2. Follow the **Implementation Order** in `HANDOFF.md` step by step
3. Write code in **10–50 LOC increments**: one definition or one lemma at a time
4. Build after every increment: `lake build GenSeq 2>&1 | tail -40`
5. Sorries with documented goal states = success; never leave a sorry undocumented
