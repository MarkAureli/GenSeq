# CLAUDE.md -- GenSeq

## Build Command

```bash
lake build GenSeq 2>&1 | tail -40
```

**NEVER run bare `lake build`** -- it rebuilds all of mathlib (~2 hours).

## Project Structure

- `GenSeq/` -- Lean 4 source files
- `HANDOFF.md` -- Mathematical analysis and implementation plan

## Workflow

1. Read `HANDOFF.md` first
2. Build after every step: `lake build GenSeq 2>&1 | tail -40`
3. Sorries with documented goal states = success
