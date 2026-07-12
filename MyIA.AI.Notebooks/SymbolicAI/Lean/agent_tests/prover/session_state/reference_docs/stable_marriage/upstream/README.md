# mmaaz-git stable-marriage-lean — Upstream Snapshot

**Purpose**: read-only snapshot of the original upstream Lean formalization to expose the **completed proofs** to the multi-agent prover. Used as reference / cookbook for translation-then-adaptation of the 3 intractable sorrys in `stable_marriage_lean/StableMarriage/GaleShapley.lean`.

**Origin**: <https://github.com/mmaaz-git/stable-marriage-lean>
**Commit**: `111e42c5ea8192247c70470a2e65cdf2c1ef2cba` (2026-01-13)
**Toolchain**: `leanprover/lean4:v4.25.0` (matches our project)
**License**: no LICENSE file in upstream repo — public GitHub repo, used here for **reference only** (no redistribution as our own work, attribution preserved). Author can request takedown.

**NOT part of any Lake build** — this is reference material auto-loaded by the multi-agent prover via the reference docs grounding mechanism (#1129).

## Layout (verbatim from upstream, commit 111e42c5)

```
upstream/
├── UPSTREAM_README_original.md   # original README from mmaaz-git
├── lean-toolchain                # v4.25.0
├── lakefile.lean
├── lake-manifest.json
├── Main.lean
├── StableMarriageLean.lean       # root module
└── StableMarriageLean/
    ├── Basic.lean                # 101 LOC — types, preferences, matchings, stability
    ├── GaleShapley.lean          # 171 LOC — GS state machine + algorithm
    ├── Lemmas.lean              # 1010 LOC — invariants + supporting lemmas
    └── Properties.lean          # 134 LOC — main results (terminates + stable + IR + noBlockingPairs)
```

## What is and is NOT proved in upstream

**Theorems with full upstream proofs** (5 total in `Properties.lean`) :

| Upstream theorem | Line | Our CoursIA correspondence | Status chez nous |
|------------------|------|----------------------------|------------------|
| `galeShapley_consistent` | L9 | (not yet ported) | n/a |
| `galeShapley_terminates` | L15 | corresponds to `gsRunSteps_terminates` (issue #997) | INTRACTABLE_UNTIL_GS_IMPL |
| `galeShapley_individuallyRational` | L35 | (not yet ported) | n/a |
| `galeShapley_noBlockingPairs` | L49 | partial in `GaleShapley.lean` | (used as lemma in `gale_shapley_stable`) |
| **`galeShapley_stable`** | **L125** | **`gale_shapley_stable` L73 (DEMO 15)** | **INTRACTABLE — UPSTREAM HAS THE PROOF** |

**Theorems NOT in upstream** (we will need to derive):

| Our theorem | Our line | Upstream status |
|-------------|----------|-----------------|
| `gale_shapley_man_optimal` | L91 (DEMO 16) | **NOT in upstream Properties.lean** — derive from `galeShapley_stable` + lattice duality (Knuth 1976) |
| `gale_shapley_woman_pessimal` | L119 (DEMO 17) | **NOT in upstream Properties.lean** — derive from `man_optimal` via lattice duality |

## Differences with our port (`stable_marriage_lean/StableMarriage/`)

| Aspect | Upstream mmaaz-git | Our port |
|--------|-------------------|----------|
| Preferences | Incomplete (subset of opposite side, includes `acceptable` filter) | **Total bijective** (each side ranks all of opposite — simplified) |
| Namespace | `StableMarriageLean` | `StableMarriage` |
| Stability definition | Allows individually-irrational matches | Bijection on `Fin n` |
| Module split | `Basic.lean` + `GaleShapley.lean` + `Lemmas.lean` + `Properties.lean` (4 files) | `Definitions.lean` + `GSState.lean` + `Lemmas.lean` + `GaleShapley.lean` (4 files) |

The **structural patterns** of the proofs transfer; the **exact lemma names + signatures** need adaptation for total bijective preferences.

## Prover usage recommendation

When tackling DEMO 15 / 16 / 17 sorrys :

1. **TacticAgent** : read `Properties.lean` L125 (`galeShapley_stable`) for the proof structure
2. **TacticAgent** : read `Lemmas.lean` for supporting lemmas (`runSteps_*`, `proposedCount_*`, etc.) and find our porting equivalents in `stable_marriage_lean/StableMarriage/Lemmas.lean`
3. **CoordinatorAgent** : split target into sub-goals matching the upstream proof skeleton
4. **For DEMO 16 (man_optimal)** : combine `galeShapley_stable` + observation that GS produces the m-optimal stable matching (each man gets his most preferred achievable woman). Use proof by induction on `runSteps`.
5. **For DEMO 17 (woman_pessimal)** : Knuth 1976 lattice duality — set of stable matchings forms a distributive lattice, m-optimal = w-pessimal. Derive `woman_pessimal` from `man_optimal` via lattice symmetry argument.

## How to regenerate

```bash
TMP=$(mktemp -d)
git clone --depth 1 https://github.com/mmaaz-git/stable-marriage-lean.git "$TMP/mmaaz"
UPSTREAM_DIR="MyIA.AI.Notebooks/SymbolicAI/Lean/agent_tests/prover/session_state/reference_docs/stable_marriage/upstream"
mkdir -p "$UPSTREAM_DIR/StableMarriageLean"
cp "$TMP/mmaaz/README.md" "$UPSTREAM_DIR/UPSTREAM_README_original.md"
cp "$TMP/mmaaz"/{lean-toolchain,lakefile.lean,lake-manifest.json,Main.lean,StableMarriageLean.lean} "$UPSTREAM_DIR/"
cp "$TMP/mmaaz/StableMarriageLean"/*.lean "$UPSTREAM_DIR/StableMarriageLean/"
rm -rf "$TMP"
```

## Attribution

All code in this directory is **the work of @mmaaz-git** (https://github.com/mmaaz-git) and is included here under fair use for **educational and research reference purposes** as part of CoursIA pedagogical material. If you are the author and want this removed or relicensed, please open an issue at <https://github.com/jsboige/CoursIA/issues>.
