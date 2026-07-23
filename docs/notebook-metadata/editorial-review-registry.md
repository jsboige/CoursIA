# Registre des revues éditoriales — `editorial_reviewed_by`

**Statut** : pilote fondateur (c.764, phase 2 issue #8051 critère #4)
**Issue parente** : [#8051](https://github.com/jsboige/CoursIA/issues/8051) — décomposer `maturity` en 3 axes
**Suite logique de** : [PR #8086 (c.763)](https://github.com/jsboige/CoursIA/pull/8086) — schéma 3-axes `editorial` × `reproducibility` × `scientific_review`
**Schéma de référence** : [docs/PARCOURS.md](../PARCOURS.md) — définitions contractuelles des 3 axes
**Auteur du registre** : ai-01 / lane `myia-po-2023:CoursIA-2`
**Date de fondation** : 2026-07-23
**Base SHA** : `6d33f5a9f` (origin/main)

---

## 1. Purpose

Le schéma 3-axes (c.763, PR #8086) définit `editorial_reviewed_by` comme le **signal canonique** permettant de promouvoir `editorial` de `BETA` à `FINAL` (cf [docs/PARCOURS.md](../PARCOURS.md) §Axe 1). Sans signal explicite, `classify_editorial()` n'émet jamais `FINAL` — c'est un design délibéré pour éviter l'auto-promotion par l'auteur du dernier commit.

**Problème** : par défaut, 598 entrées historiques du catalogue sont rétrogradées de `PRODUCTION` à `BETA` dans l'agrégat `maturity` (effet c.763), parce que `editorial_reviewed_by == null` côté catalogue. **Sans mécanisme de backfill**, ces notebooks restent `BETA` ad vitam.

**Solution** : un **registre whitelist YAML** curé manuellement, qui enregistre les revues éditoriales tierces (≥1 reviewer non-auteur du dernier commit). Le validateur `scripts/audit/check_editorial_review.py` croise ce registre avec le catalogue généré et signale toute dérive (registre obsolète, entrée catalogue sans signal alors que le registre la couvre, etc.).

**Pourquoi whitelist et pas heuristique** : l'heuristique `last_validator != owner_logique` est trop faible pour le cluster CoursIA, où l'auteur canonique est `po-2023` et où `jsboige` revalide souvent. La whitelist curatoriale est **honnête** : elle exige une décision humaine pour reconnaître qu'une PR a fait office de revue éditoriale.

## 2. Format YAML schema

Chaque entrée du registre suit le schéma :

```yaml
- notebook_path: <chemin relatif depuis MyIA.AI.Notebooks/>
  reviewer: <login GitHub ou email>
  review_date: <ISO 8601 date, "YYYY-MM-DD">
  evidence_pr: <"#NNNN" PR GitHub>
  review_scope: <factual|typo|pedagogie|substance|full>
  notes: "<libre, max 200 chars>"
```

| Champ | Type | Contrainte | Signification |
|-------|------|-----------|---------------|
| `notebook_path` | string | DOIT matcher exactement `path` d'une entrée du catalogue généré | Cible de la revue |
| `reviewer` | string | DOIT être ≠ `owner_logique` du notebook (sinon auto-review, ignorée) | Qui a relu |
| `review_date` | string | ISO 8601 `YYYY-MM-DD` | Date de la PR de revue |
| `evidence_pr` | string | `#NNNN` PR GitHub mergée | Preuve vérifiable (G.1) |
| `review_scope` | enum | `factual` / `typo` / `pedagogie` / `substance` / `full` | Profondeur de la revue (cf §3) |
| `notes` | string | Libre, 1 ligne | Contexte bref |

## 3. Curation rules (HARD)

### 3.1 Éligibilité d'une revue

Une PR compte comme `editorial_reviewed_by` valide **uniquement si** :

1. La PR est **mergée** sur `main` (pas draft, pas fermée).
2. La PR **touche au moins une cellule** du notebook (markdown OU code) — pas une PR qui n'aurait modifié que le README de la série.
3. Le diff contient au moins **1 insertion ou 1 suppression non-vide** dans le notebook cible.
4. L'auteur du commit de merge **n'est pas** l'`owner_logique` du notebook (sinon = auto-review, ne promeut pas).
5. La `review_scope` est cohérente avec le diff : `typo` exige corrections orthographiques ; `factual` exige corrections factuelles vérifiables (chiffres, dates, noms propres, théorèmes) ; `pedagogie` exige restructuration pédagogique ; `substance` exige corrections de fond (algorithme, équation, raisonnement) ; `full` exige les 4 dimensions.

### 3.2 Promotion `BETA → FINAL`

Le validateur promeut `editorial` à `FINAL` **uniquement si** :

- Au moins 1 entrée du registre whitelist le notebook (avec `evidence_pr` mergée).
- `review_scope ∈ {factual, substance, full}` (les `typo` et `pedagogie` ne suffisent pas, car ils ne garantissent pas la véracité technique).
- `reviewer ≠ owner_logique` du notebook (cf §3.1 #4).

### 3.3 Conflits avec d'autres signaux

`editorial_reviewed_by` est **complémentaire** de `last_validator` (champ catalogue existant). Si `last_validator ≠ owner_logique` ET registre whitelist absent, le registre prévaut comme source de vérité. Si les deux sont présents et **incohérents**, le validateur signale `DRIFT` (cf §9 anti-FP).

## 4. Pilote Sudoku (3 entrées whitelist)

Curation sur les PRs `fix(sudoku,#3801): ... factual errors` mergées sur main (G.1 vérifié 4 commits SHA + 4 paths + 4 auteurs + 4 dates) :

```yaml
# docs/notebook-metadata/editorial-review-registry.md — pilote c.764
# Format: voir §2. Éligibilité: §3. Promotion: §3.2.
#
# Note pilote : 4 PRs factuelles identifiées, 3 promotions effectives (les 3 par
# jsboigeEpita = tierce ≠ owner_logique po-2023). La PR #7970 (auteur jsboige)
# est documentée pour traçabilité mais NE promeut PAS le notebook (auto-review).

- notebook_path: Sudoku/Sudoku-18-Comparison-Python.ipynb
  reviewer: jsboigeEpita
  review_date: 2026-07-22
  evidence_pr: "#7904"
  review_scope: factual
  notes: "fix(sudoku,#3801): stale-benchmark-numbers honesty (cells 37+40)"

- notebook_path: Sudoku/Sudoku-11-Choco-Csharp.ipynb
  reviewer: jsboigeEpita
  review_date: 2026-07-22
  evidence_pr: "#7794"
  review_scope: factual
  notes: "fix(sudoku,#3801): reconcile '1-50 ms' claim with 728 ms cold-start output"

- notebook_path: Sudoku/Sudoku-12-Z3-Csharp.ipynb
  reviewer: jsboigeEpita
  review_date: 2026-07-22
  evidence_pr: "#7801"
  review_scope: factual
  notes: "fix(sudoku,#3801): reconcile 'entier plus rapide facile' + 'se valent' with committed benchmark"
```

**Non-promotion documentée** (pour traçabilité audit, ne pas retirer) :

| Notebook | PR | Auteur | Raison non-promotion |
|----------|-----|--------|----------------------|
| `Sudoku/Sudoku-14-BDD-Csharp.ipynb` | #7970 | `jsboige@gmail.com` | auteur = owner_logique (`po-2023` aliased jsboige) — auto-review par règle §3.1 #4 |

## 5. Acceptance criteria

- [ ] `scripts/audit/check_editorial_review.py --check` exit 0 sur pilote Sudoku (3 entrées valides + 1 entrée explicitement non-promouvante)
- [ ] `scripts/notebook_tools/generate_catalog.py --series Sudoku --output-dir <HORS worktree>` émet `editorial = FINAL` pour les 3 notebooks whitelistés (vs BETA par défaut) + `editorial_reviewed_by` non-null dans le payload
- [ ] Distribution post-backfill documentée : 3/36 = 8.3% des entrées Sudoku passent `BETA → FINAL`
- [ ] Cohérence agrégat `maturity` : les 3 notebooks whitelistés passent `BETA → PRODUCTION` dans `maturity` (rétro-compat c.763)
- [ ] Aucune autre entrée touchée (33/36 restent à leur état antérieur)

## 6. How to add a new entry

1. Identifier une PR mergée éligible (§3.1) qui touche un notebook.
2. Vérifier firsthand que la PR est bien mergée (`git log --grep="#NNNN"`, `gh pr view N --json state,mergedAt`).
3. Vérifier que le `reviewer` est non-auteur du dernier commit du notebook (`git log -1 --format="%an"` sur le notebook).
4. Ajouter l'entrée dans la section `## 4. Pilote` (ou créer une nouvelle section `## N. <Nom de la famille>` si famille distincte).
5. Lancer `python scripts/audit/check_editorial_review.py --check` pour validation.
6. Documenter la nouvelle entrée dans le `[DONE]` dashboard workspace avec PR# + raison.

## 7. How to remove an entry

1. Si la PR est annulée (`gh pr view N --json state` retourne `CLOSED` après merge, ou revert commit), retirer l'entrée du registre.
2. Si le reviewer devient `owner_logique` (réassignation de lane), retirer l'entrée.
3. Si le notebook est archivé/déplacé dans `_archives/`, retirer l'entrée.
4. Documenter la suppression dans le changelog (§11).

## 8. Interaction avec `classify_editorial()`

Le classifier dans `scripts/notebook_tools/generate_catalog.py` consomme ce registre via la fonction `load_editorial_review_registry()` (signature stable, voir §API du validateur). Le payload catalogue s'enrichit du champ `editorial_reviewed_by` (curated git field, préservé à travers les merges cf incident fondateur #2376/#2383/#2385 `stale-catalog-silent-revert`).

**Algorithme de promotion** :

```python
def classify_editorial(notebook, code_cells, *, is_template=False,
                       registry_entries=None) -> str:
    # ... (logique existante c.763 : DRAFT / ALPHA / BETA) ...
    
    # NOUVEAU c.764 : promouvoir BETA → FINAL si signal registre
    if editorial == "BETA" and registry_entries:
        for entry in registry_entries:
            if (entry["notebook_path"] == notebook["path"]
                and entry["review_scope"] in ("factual", "substance", "full")
                and entry["reviewer"] != notebook["owner_logique"]):
                return "FINAL"
    
    return editorial
```

## 9. Anti-FP / edge cases

- **Auto-review déguisée** : si `reviewer` est un alias de l'`owner_logique` (ex: `jsboige` vs `jsboige@gmail.com`), le validateur signale `DRIFT_REVIEWER_ALIAS`.
- **PR qui ne touche pas le notebook** : si le diff de la `evidence_pr` ne touche pas le `notebook_path` whitelisté, le validateur signale `DRIFT_PR_NOT_TOUCHING`.
- **PR non mergée** : si `state != "MERGED"`, le validateur signale `WARN_PR_NOT_MERGED`.
- **Double-entrée** : 2 entrées pour le même `notebook_path` sont tolérées (plusieurs revues = cumulable), mais un warning est posté.
- **`review_scope` invalide** : valeur hors enum → `ERROR_SCOPE_INVALID`, l'entrée est ignorée mais le registre n'est pas invalidé.

## 10. References

- Issue [#8051](https://github.com/jsboige/CoursIA/issues/8051) — décomposer `maturity` en 3 axes (c.763 critères 1-3 + c.764 critère #4 phase 2)
- [PR #8086](https://github.com/jsboige/CoursIA/pull/8086) — c.763 schéma 3-axes (OPEN MERGEABLE)
- [docs/PARCOURS.md](../PARCOURS.md) — définitions contractuelles des 3 axes (c.763)
- `scripts/notebook_tools/generate_catalog.py` — classifier `classify_editorial()` (c.763) + extension c.764
- `scripts/audit/check_editorial_review.py` — validateur (c.764 NEW)
- `scripts/audit/check_dataset_registry.py` — analogue pattern (c.795, OPEN sweep-ready #8083)
- `docs/notebook-metadata/dataset-registry.md` — analogue structure (c.795)
- EPIC [#4208](https://github.com/jsboige/CoursIA/issues/4208) — open-courseware fiabilisé (parent)
- Incident fondateur [#2376](https://github.com/jsboige/CoursIA/issues/2376) / [#2383](https://github.com/jsboige/CoursIA/issues/2383) / [#2385](https://github.com/jsboige/CoursIA/issues/2385) — `stale-catalog-silent-revert` (CURATED_GIT_FIELDS préservés)

## 11. Changelog

| Date | Auteur | Cycle | Changement |
|------|--------|-------|------------|
| 2026-07-23 | ai-01 / po-2023 | c.764 | Création du registre (NEW). Pilote Sudoku : 3 entrées whitelist (Sudoku-18, Sudoku-11-Choco, Sudoku-12-Z3) + 1 entrée non-promouvante documentée (Sudoku-14-BDD auto-review #7970). |
