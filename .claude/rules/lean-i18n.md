---
paths: "**/*.lean"
---

# Lean (i18n)

EPIC **#4980** — convention ratifiée par user 2026-07-04 (Option A, deux commentaires user datés 2026-07-04T11:58Z et 14:52Z sur l'issue, addendum mécanisme FR/EN inclus), voir l'inventaire de référence [`docs/lean/i18n-inventory-cycle-38.md`](../../docs/transients/2026-07-04-lean-i18n-inventory-cycle-38.md) (lane transiente, tranche 3b de #14623) + pilote livré [PR #5883](https://github.com/jsboige/CoursIA/pull/5883) (2026-07-10, module CooperativeGames désormais absorbé dans [`game_theory_lean/CooperativeGames/`](../../MyIA.AI.Notebooks/GameTheory/game_theory_lean/CooperativeGames/Shapley.lean), docstrings FR + siblings EN Pattern A sibling-pair).

- **Docstrings en français** par défaut dans les `*.lean` own (i.e. hors `.lake/packages/`, `_peters/`, `agent_tests/prover/session_state/reference_docs/`, et libs vendored).
- **Traduction anglaise optionnelle** pour les lakes destinés à une audience externe (publication, papier, dépôt public). Modèle **sibling pair** `Foo.lean` / `Foo_en.lean` :
  - Suffixe `_en` sur le **namespace** (`namespace FooLean` ↔ `namespace FooLean_en`) et sur les **imports** (`import Foo.Bar` ↔ `import Foo.Bar_en`) — anti-collision de noms.
  - Les **énoncés de théorèmes/lemmes**, **tactiques Lean**, **noms de lemmes**, **références Mathlib** restent en anglais (compat Mathlib 4, tactic DSL, lemmas officiels).
  - Seules les **docstrings `/-- ... -/`** et **commentaires `-- ...`** diffèrent entre les deux fichiers. **Préservation byte-identity** sur le reste (signatures, preuves, tactiques) — vérifiable par diff.
- **Trois formes de paire légitimes** (miroir auto-contenu `OK` / jumeau consommateur `OK-CONSUMER` qui importe le FR sans re-déclarer / divergence de qualifieur intrinsèque). Une sortie de checker `DRIFT`/`ORPHAN` est un **point de départ d'investigation, jamais un grain à exécuter verbatim** : line-verify + `lake build <cible>_en` avant de committer/dispatcher. Taxonomie + incidents fondateurs #6716/#6717 : [docs/lean/i18n-sibling-patterns.md](../../docs/lean/i18n-sibling-patterns.md). Outil : `scripts/lean/check_i18n_siblings.py` (#6711/#6718).
- **Pas de bloc bilingue inline** dans un même fichier (Option B rejetée : coût double + drift FR/EN + biais qualité).
- **Hors scope** (status quo) : `.lake/packages/` (Mathlib 4 vendored), `_peters/` (lake externe), `agent_tests/prover/session_state/reference_docs/` (fixtures tiers), libs vendored tierces (`foundry-lib/lib/**`).
- **Rollout** : fleet **DRAINED**. La source de vérité est le checker canonique `scripts/lean/check_i18n_siblings.py --all`, **jamais** une liste statique — « pas de `_en` sibling » ≠ « gap i18n » (les root aggregators sont FR-only *by design*). État daté et cas particuliers : [i18n-inventory-cycle-38.md](../../docs/transients/2026-07-04-lean-i18n-inventory-cycle-38.md) (lane transiente, tranche 3b de #14623).

## Source

Section extraite de [code-style.md](code-style.md) (ligne 10 du verdict du 2026-10-27, locus #12051) -- deplacement fidele, zero prescription reecrite ; la convention y reste resumee par un pointeur.
