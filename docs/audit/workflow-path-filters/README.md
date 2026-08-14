# Audit workflow path-filters

Rapports d'audit sur la couverture `pull_request.paths` / `pull_request.paths-ignore`
des workflows GitHub Actions dans `.github/workflows/`.

## Origine

Issue **#10600** : "74 workflows se déclenchent sur chaque PR, 0 filtre de chemin".
Mesure G.1 firsthand (cf commentaire worker `myia-po-2024:CoursIA-2`, 2026-08-13) :
la prémisse est **partiellement fausse** — 62/72 workflows PR-triggered ont déjà un
filtre paths/paths-ignore. Restent 10 sans filtre (catalog-pr-guard, lane-claim-guard,
pr-gate, regression-guard, repo-size-advisory, secret-scan, stale-base-warning,
translation-guard, variation-light-genre, variation-tag-guard), tous gates requis
par construction ou advisories bon marché qui doivent voir chaque PR.

Le levier n'est donc pas "filtrer plus" mais **détecter les futures régressions**
(workflow ajouté sans filtre par erreur). Ce sous-grain transforme la mesure G.1
ponctuelle en organe périodique.

## Fichiers produits

| Fichier | Rôle |
|---|---|
| `scripts/notebook_tools/audit_workflow_path_filters.py` | Script d'audit (CLI) |
| `scripts/tests/test_audit_workflow_path_filters.py` | Pytest fixtures + asserts |
| `.github/workflows/workflow-path-filter-audit.yml` | CI advisory schedule + dispatch |

## Sortie

- **JSON** : `docs/audit/workflow-path-filters/audit-<timestamp>-<sha>.json` (complet)
- **Markdown** : `docs/audit/workflow-path-filters/audit-<timestamp>-<sha>.md` (résumé humain)
- **Latest** : `docs/audit/workflow-path-filters/latest.{json,md}` (le plus récent)

## Classification

| Catégorie | Critère |
|---|---|
| `filtered` | Workflow avec `pull_request.paths` ou `paths-ignore` non-vide |
| `required` | Workflow unfiltered dans `REQUIRED_UNFILTERED_WORKFLOWS` whitelist (gates/advisories) |
| `optional` | Workflow unfiltered hors whitelist (à investiguer) |
| `no_pr_trigger` | Workflow sans `pull_request` trigger (schedule, push, etc.) |

La whitelist `REQUIRED_UNFILTERED_WORKFLOWS` est OPT-IN : ajouter un nom uniquement
après audit (cf. issue #10600 et discussion lane-claim-protocol).

## Usage

```bash
# Audit basique (rapport dans docs/audit/workflow-path-filters/)
python scripts/notebook_tools/audit_workflow_path_filters.py

# Avec regression check (vs un audit précédent)
python scripts/notebook_tools/audit_workflow_path_filters.py \
  --check-regression docs/audit/workflow-path-filters/latest.json

# Tests pytest
npx pytest scripts/tests/test_audit_workflow_path_filters.py -v
```

## Tests

`pytest scripts/tests/test_audit_workflow_path_filters.py -v` couvre :
- Workflow filtré classifié correctement
- Workflow unfiltered-required classifié correctement
- Workflow avec `'on':` (PyYAML quirk) parsé correctement
- Workflow sans `pull_request` classifié tel quel
- Workflow unfiltered-optional classifié correctement
- Workflow avec `pull_request` (list de triggers) parsé
- Summary agrege correctement
- Regression check détecte nouveau workflow unfiltered
- Pas de faux positif sur audit identique
- CLI run end-to-end OK
- CLI echoue proprement sur workflows_dir inexistant

## Références

- Issue **#10600** — la mesure d'origine + conclusion G.1
- Issue **#10644** — support Linux/macOS (cross-OS workflows)
- `.claude/rules/cell-interpretation-ordering.md` — règle sémantique analogue pour les cellules d'interprétation notebook