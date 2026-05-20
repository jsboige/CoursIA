# `session_state/` — portable shared state for the multi-agent Lean prover

Introduced by issue #1081 Part 2 ("reference documents injection"). The multi-agent prover
(`agent_tests/prover/`) used to start every iteration blind: its agents — including the
frontier-model `DirectorAgent` — had no access to reference material and rediscovered the
same proof strategies from scratch each run.

This directory is the **committed, portable shared state** that survives from one iteration
to the next, so agents can ground their guidance in real reference material.

## Layout

```
session_state/
  reference_docs/
    stable_marriage/
      mmaaz-git-gs-strategies.md   # proof STRATEGIES extracted from the original
                                   #   github.com/mmaaz-git/stable-marriage-lean repo
      gs-definitions.lean          # auto-copied snapshot: Definitions.lean + GSState.lean
      existing_proofs.lean         # auto-copied snapshot: our ported, PROVEN Lemmas.lean
      project_hints.md             # domain tactic patterns (issue #1081 Part 1 + cookbook)
  lessons_learned.json             # cross-session tactical lessons ({} placeholder + schema)
  session_summary.md               # bilan of the previous prover session (placeholder)
  README.md                        # this file
```

## Conservation vs cleanup policy

The whole point of this directory is to separate what must **persist** from what is
**ephemeral pollution** of a single iteration.

**Conservation (committed, kept across iterations):**
- `reference_docs/` — reference material. Stable; only changes when the underlying source
  files change (the `.lean` snapshots are re-copied) or when strategy notes are improved.
- `lessons_learned.json` — accumulated tactical lessons. Grows across sessions; the prover
  appends, deduplicating by goal signature. Never auto-deleted.
- `session_summary.md` — the previous session's bilan. Overwritten (not appended) by each
  new session, but always kept so the next session can read it.

**Cleanup (NOT stored here, must be wiped between sessions):**
- Failed tactic attempts of the current iteration, ephemeral proof-state dumps, scratch
  context. These live in the prover's transient state (`attempt_history.py`, `state.py`,
  `traces/`), not in `session_state/`. A new session must start from a clean transient
  state — only `session_state/` carries over.

Rule of thumb: if it is a *reference* (definitions, proven lemmas, strategies) or a
*distilled lesson*, it belongs here and is conserved. If it is *raw attempt noise* from one
run, it does not belong here and is cleaned up.

## Regenerating the auto-copied snapshots

`gs-definitions.lean` and `existing_proofs.lean` are verbatim snapshots of
`MyIA.AI.Notebooks/SymbolicAI/Lean/stable_marriage_lean/StableMarriage/` files
(`Definitions.lean` + `GSState.lean`, and `Lemmas.lean` respectively). They are **not part
of any Lake build** — they exist only as agent reference. When the source files change,
re-copy them (and update the header date). Do not edit the snapshots in place; edit the
real source under `stable_marriage_lean/`.

## How it is wired into the prover

`agent_tests/prover/instructions.py` exposes `load_reference_docs(project)` which reads the
`reference_docs/<project>/` files and returns a compact (~6000 char) concatenated summary.
`augment_instructions(..., include_references=True)` optionally prepends it to an agent's
instructions; the default is `False` so existing call sites are unaffected. The
`DIRECTOR_AGENT_INSTRUCTIONS` constant tells the Director to ground its APPROACH in this
reference material.
