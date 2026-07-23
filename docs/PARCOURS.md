# PARCOURS — Schéma maturité 3 axes

**Issue** : [#8051](https://github.com/jsboige/CoursIA/issues/8051)
**Statut** : ACCEPTÉ (2026-07-23), pilote en cours (c.763 critères 1-3)
**Auteur du schéma** : ai-01 / lane `myia-po-2023:CoursIA-2` (po-2023 = générateur)
**Date** : 2026-07-23
**Base SHA** : `8092a4aec` (post-merge pool QC, post-#8064)

---

## Pourquoi décomposer le monolithique `maturity`

Le catalogue généré (`COURSE_CATALOG.generated.json`) porte aujourd'hui un champ **`maturity`** monolithique à 5 valeurs (`TEMPLATE / PRODUCTION / BETA / ALPHA / DRAFT`). Ce schéma mélange trois préoccupations **orthogonales** qu'il vaut mieux séparer pour les rendre auditables indépendamment :

1. **Maturité éditoriale** — où en est la *prose pédagogique* ? (de DRAFT = jamais relu à FINAL = relu, stable, prêt à publier).
2. **Reproductibilité** — le notebook a-t-il *réellement tourné* et avec quel niveau de garantie ? (de UNTESTED = aucune cellule exécutée à REPRODUCED = ré-exécuté de bout en bout avec succès, horodaté).
3. **Revue scientifique** — la *substance technique* a-t-elle été validée et par qui ? (de UNREVIEWED = auteur seul à FORMALLY_VERIFIED = preuve formelle ou peer-review externe).

Mélanger ces axes en une seule étiquette (PRODUCTION, BETA…) a trois défauts :
- **Illisible** : « BETA » ne dit pas si le notebook a réellement exécuté, ni si la substance est revue — il dit juste « pas tout à fait finalisé ».
- **Non-auditable** : on ne peut pas filtrer « notebooks qui n'ont jamais exécuté » ou « notebooks dont la substance n'est pas relue » parce que la granularité est perdue.
- **Non-réversible** : si la prose est FINAL mais l'exécution a régressé, on doit downgrader toute l'étiquette alors qu'un seul axe a changé.

## Les 3 axes — définitions contractuelles

### Axe 1 — `editorial` (maturité éditoriale)

| Valeur | Définition | Critère vérifiable |
|--------|-----------|--------------------|
| `DRAFT` | Première rédaction, structure incomplète, fautives fréquentes | `cells_markdown / cells_total < 0.20` OU titre placeholder OU TODO dans la première cellule markdown |
| `ALPHA` | Structure pédagogique en place, exemples partiels, trous assumés | DRAFT non vérifié ET ≥1 cellule markdown d'introduction ET ≥1 exemple |
| `BETA` | Pédagogie complète, tous les concepts couverts, relecture interne auteur | `cells_markdown >= 0.40` ET conclusion présente ET ≥3 exercices (cf [`three-exercises-per-notebook.md`](../.claude/rules/three-exercises-per-notebook.md)) |
| `FINAL` | Relecture externe (cluster ou peer), stable, prêt à publier | `BETA` + relu par ≥1 agent non-auteur (signal `editorial_reviewed_by` non-null dans le catalogue) |

### Axe 2 — `reproducibility` (reproductibilité)

**Source de vérité** : forensic scan (`scripts/notebook_tools/forensic_scan.py`) — categories A/B/C/D + timestamp `last_commit_sha`.

| Valeur | Définition | Critère vérifiable (catégorie forensic) |
|--------|-----------|----------------------------------------|
| `UNTESTED` | Aucune cellule code exécutée | `C_NEVER_EXECUTED` OU `NO_CODE` |
| `STATIC_OK` | Notebook *valide statiquement* (parse OK, structure OK) mais non exécuté | `STATIC_OK` (parse réussi, `n_code > 0`, `n_exec == 0`, pas d'erreur statique) |
| `EXECUTED` | Toutes les cellules code exécutées avec succès | `A_ALL_EXEC_OK` — `execution_count != null` partout + 0 erreur |
| `REPRODUCED` | Ré-exécution *horodatée* de bout en bout, SHA engagé | `EXECUTED` + `last_commit_sha` cohérent avec `executed_at` (±7 jours) ET `metadata.last_success_sha == last_commit_sha` |

**Différence EXECUTED vs REPRODUCED** : `EXECUTED` est un état *intrinsèque* du fichier (au moment du commit) ; `REPRODUCED` est un état *daté* (on peut affirmer « ce notebook a tourné le JJ/MM avec succès sur le SHA X »). REPRODUCED est ce qui permet de répondre « oui, ce notebook marche *aujourd'hui* » ; EXECUTED peut dater de 2 ans et avoir régressé depuis.

### Axe 3 — `scientific_review` (revue scientifique)

| Valeur | Définition | Critère vérifiable |
|--------|-----------|--------------------|
| `UNREVIEWED` | Aucun passage en revue hors l'auteur | Pas de signal `scientific_reviewed_by` ni de PR/discussion de substance attachée |
| `AUTHOR_REVIEWED` | L'auteur a relu sa propre substance (cross-check, sanity-checks) | Présence d'une note « Self-review » dans le notebook OU signal PR auteur `self-reviewed` |
| `PEER_REVIEWED` | Relecture par ≥1 agent tiers du cluster ou reviewer externe | `scientific_reviewed_by` non-null ET ≠ auteur du dernier commit |
| `FORMALLY_VERIFIED` | Preuve formelle (Lean, Coq, Agda) ou benchmark reproductible validé | Présence d'un fichier `.lean` companion OU `lake build SUCCESS` daté OU benchmark QC multi-seed ≥4 seeds |

---

## Migration / rétro-compatibilité

Le champ `maturity` monolithique actuel reste **présent** dans `COURSE_CATALOG.generated.json` pour ne casser aucun consommateur existant (README, dashboards, scripts tiers). Il est désormais **calculé comme l'agrégat** des 3 axes, selon la règle :

```
editorial == "FINAL" AND reproducibility in ("EXECUTED", "REPRODUCED") AND scientific_review in ("PEER_REVIEWED", "FORMALLY_VERIFIED")
  → maturity = "PRODUCTION"
editorial in ("BETA", "FINAL") AND reproducibility in ("EXECUTED", "REPRODUCED")
  → maturity = "BETA"
editorial in ("ALPHA", "BETA") AND reproducibility in ("STATIC_OK", "EXECUTED")
  → maturity = "ALPHA"
is_template (filename contains "template")
  → maturity = "TEMPLATE"
sinon
  → maturity = "DRAFT"
```

**Le consommateur qui veut plus de granularité** lit directement `editorial`, `reproducibility`, `scientific_review`. Celui qui veut l'ancien label lit `maturity`. Aucun breaking change.

## Statut séparé — non touché par ce schéma

Le champ `status` (`READY`, `DEMO`, `RESEARCH`, `BROKEN`) reste **orthogonal** aux 3 axes maturité. Un notebook peut être :
- `editorial=FINAL` + `reproducibility=REPRODUCED` + `scientific_review=PEER_REVIEWED` + `status=BROKEN` (ex : notebook qui marchait mais dont une dépendance externe est cassée) ;
- `editorial=ALPHA` + `reproducibility=EXECUTED` + `scientific_review=AUTHOR_REVIEWED` + `status=DEMO` (ex : démo scientifique sans valeur pédagogique aboutie).

`status` répond à « *peut-on le faire tourner en l'état ?* », les 3 axes répondent à « *où en est sa substance ?* ». Séparer les deux est une décision architecturale stable (issue #8051 acceptance critère 2).

## Métadonnée d'exécution horodatée (critère 3)

Le catalogue embarque, par notebook, deux nouveaux champs :

| Champ | Type | Source | Signification |
|-------|------|--------|---------------|
| `last_success_sha` | string (7 chars hex) | `git rev-parse --short HEAD` au moment du commit si forensic = `A_ALL_EXEC_OK` | Commit court qui correspond à la dernière exécution validée |
| `executed_at` | ISO 8601 string | `last_commit` du forensic scan (ISO 8601, `+00:00` UTC) | Date de la dernière exécution vérifiée |

Ces deux champs permettent de calculer `reproducibility = REPRODUCED` (cohérence `last_success_sha` avec le SHA HEAD) et de répondre « *quand ce notebook a-t-il été vérifié pour la dernière fois ?* ».

## Critères d'acceptance #8051 (extrait)

- [x] **#1** Schéma 3 axes + définitions contractuelles → ce document.
- [x] **#2** Le générateur de catalogue émet `editorial`, `reproducibility`, `scientific_review` + champ rétro-compatible `maturity`.
- [x] **#3** Métadonnée d'exécution horodatée (`last_success_sha` + `executed_at`) branchée sur le forensic scan.
- [ ] **#4** Pilote sur 2 familles (Sudoku + GenAI) → phase 2, c.764+.

## Liens

- **Issue [#8051](https://github.com/jsboige/CoursIA/issues/8051)** — décomposer `maturity` en 3 axes.
- **[`scripts/notebook_tools/generate_catalog.py`](../scripts/notebook_tools/generate_catalog.py)** — générateur (modifié c.763).
- **[`scripts/notebook_tools/forensic_scan.py`](../scripts/notebook_tools/forensic_scan.py)** — source des catégories A/B/C/D + `last_commit_sha`.
- **[`COURSE_CATALOG.generated.json`](../COURSE_CATALOG.generated.json)** — artefact généré, regénéré par cron.
- **EPIC [#4208](https://github.com/jsboige/CoursIA/issues/4208)** — open-courseware fiabilisé (parent).
- **[`.claude/rules/three-exercises-per-notebook.md`](../.claude/rules/three-exercises-per-notebook.md)** — règle ≥3 exercices, critère `BETA` axe éditorial.