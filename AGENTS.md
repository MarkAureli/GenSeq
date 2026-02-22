# Agent Instructions

## Project Context

Lean 4 formalization project. See `HANDOFF.md` for the central question and implementation plan.

## Build Command

```bash
lake build GenSeq 2>&1 | tail -40
```

**NEVER run bare `lake build`** — it rebuilds all of mathlib (~2 hours).

## Issue Tracking

Use `bd` (beads) to track remaining work:

```bash
bd new "..." -p P0              # file new work item (P0 = high priority)
bd ls                           # see open items
bd close <id>                   # mark done
```

File a task for every sorry, every TODO, and every planned follow-up
before ending a session.

## Adversarial Proof Trees

Use `af` (vibefeld) to manage structured, multi-agent proof trees for
specific conjectures. Create a subdirectory per conjecture:

```bash
# Initialise (once per conjecture)
mkdir <proof-dir>
af init --conjecture "..." --author "Claude" --dir <proof-dir>

# Navigate
af status              # view the proof tree
af jobs                # see available work

# Verifier workflow
af claim <id>          # claim a node
af accept <id>         # validate it
af challenge <id> "..."  # raise an objection

# Prover workflow
af claim <id>          # claim a challenged node
af refine <id> "..."   # break into sub-claims
af resolve-challenge <id> <ch-id> "..."

# Export
af export --format latex   # for reports
```

## Landing the Plane (Session Completion)

**MANDATORY — work is NOT complete until `git push` succeeds.**

1. File beads tasks for all remaining work
2. Run quality gates: `lake build GenSeq 2>&1 | tail -40`
3. Update `HANDOFF.md` session log — append what was done, current state, next steps
4. Commit and push:
   ```bash
   git add -p
   git commit -m "..."
   git pull --rebase
   git push
   git status  # must show "up to date with origin"
   ```
5. Verify the push succeeded before stopping

## Critical Rules

- **NEVER stop before pushing** — stranded local commits cannot be
  recovered by the next session
- **NEVER say "ready to push when you are"** — YOU must push
- If push fails, resolve the conflict and retry until `git status` is clean
