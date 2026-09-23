# Bot Review Harness — pointer externe

> **Issue** : #16635 (résidu de #13517) — la mise à jour de harnais prescrite par #13517 aux deux bots Hermes et NanoClaw n'avait aucune surface citée dans le dépôt CoursIA. Ce fichier comble ce trou par un pointeur explicite.

## Bots concernés

| Bot | Rôle | Identité GitHub |
|---|---|---|
| **Hermes** | Cron intercom review, fleet ping, patrol erreurs, PR review fallback | `clusterManager-Myia` (compte **partagé** avec NanoClaw — résolu 2026-09-08 — voir `jsboige/roo-extensions#3219`) |
| **NanoClaw** | Audit à 60-83 % de faux positifs historiques (mesure archivée, statut **Resolved** via audit-reassessment `#499` — cf. `docs/archive/stabilization-phase1-matrix.md` l. 72) | `clusterManager-Myia` (même compte, distingué par préfixe `[NanoClaw]` dans le body de review) |

## Où vit le harnais

Le harnais de review des bots vit **hors du dépôt CoursIA**, dans le dépôt **`jsboige/roo-extensions`** :

- **Annuaire principal** : [`docs/harness/reference/bots-directory.md`](https://github.com/jsboige/roo-extensions/blob/main/docs/harness/reference/bots-directory.md)
  - Identité GitHub résolue (`jsboige/roo-extensions#3219`)
  - Schéduler Python `hermes-agent` (`github.com/jsboige/hermes-agent`, fork de `NousResearch/hermes-agent`) — `cron/scheduler.py`
  - Distribution des minutes des 183 reviews `[Hermes]` mesurée (po-2025, échantillon 200 PRs, **MAJ 2026-08-25 — `#3219` audit**)
  - MAJ continue via commits datés, le plus récent : `45294ef0` (2026-09-20T22:56Z) — ratio ~1.2:1, Hermes 6/6 formels
- **Bridge MCP** : `docs/harness/reference/roosync-tools-guide.md` — accès RooSync Hermes corrigé (#3413)
- **Règles split-vibesync** : `docs/harness/adr/011-mcp-split-vibesync.md`

## Substance livrée côté dépôt CoursIA (#13517 → #14254)

Suite au commentaire user 2026-08-29 sur `jsboige/CoursIA#13472` (« graphviz pas installée, les graphes de facteurs ne sont pas générés, les 2 bots n'ont pas fait un travail de review suffisament attentif »), PR #14254 (`docs(pr-review,#13517): §D.6 — vérifier le verdict Output-failure ratchet (base vs PR)`, merged 2026-09-02T18:25:52Z par `jsboige` — compte partagé, voir `jsboige/CoursIA#3219`) a ajouté la règle §D.6 dans `.claude/rules/pr-review-discipline.md` :

> « **PRs notebook : vérifier le verdict du check-run `Output-failure ratchet (base vs PR)`** (organe `scripts/notebook_tools/check_output_failure_text.py`, **bloquant** dans `scripts/ci/fast_lane_registry.py`) — il DOIT être `success`. `TOOL_FAILURE` (bannières « `program is not installed` ») ou `MACHINE_PATH` qui **augmente** sur la PR (ex. `0 → 21`) = **régression → `CHANGES_REQUESTED`**, même si les points 1-3 passent. »

Cette règle protège côté dépôt (garde bloquant), mais **la MAJ côté bots** (leur demander d'appliquer le même regard avant APPROVED) reste dans roo-extensions et n'est pas re-vérifiable depuis ce dépôt.

## Comment vérifier

Pour constater l'état de la MAJ côté bots :

1. Lire `https://github.com/jsboige/roo-extensions/blob/main/docs/harness/reference/bots-directory.md` à jour
2. `gh api repos/jsboige/roo-extensions/commits?path=docs/harness/reference/bots-directory.md&per_page=5` pour la liste des derniers commits
3. Comparer avec les ratios publiés (Hermes formel vs NanoClaw COMMENTED) — un écart stable signe un blocage structurel à escalader au mainteneur de roo-extensions

## Voir aussi

- `docs/reference/audit-reassessment-findings.md` — organe `scripts/audit-reassessment.md` (≈60 % FP mesurés sur échantillon initial, ramené à < 5 % par le protocole de vérification — Tell c.499 closed via `docs/archive/stabilization-phase1-matrix.md` l. 72)
- `docs/reference/pr-review-context.md` — règle §D.6 + incidents fondateurs `#3473`/`#11685`/`#13517` (…)
- Issue `jsboige/CoursIA#13517` (CLOSED) — origine du résidu
- Issue `jsboige/CoursIA#16635` (cette issue) — résolu par ce pointeur
