# `scripts/notebook_tools/_archive/` — convention standardisée

S'applique au sous-dossier `_archive/` de `scripts/notebook_tools/`. Référence parente :
[`docs/reference/_archive-convention.md`](../../../../docs/reference/_archive-convention.md) (modèle ML-Training-Pipeline généralisé,
4 critères d'éligibilité, header disposition per-function).

## État au 2026-09-01

1 fichier archivé. Origine : sous-grain `#13745` (umbrella « 92 orphelins notebook_tools/ + fusions sélectives V3 »),
claim `myia-po-2026:CoursIA-2` du 2026-09-01 (paths: `scripts/notebook_tools/_fix_leaks_batch1.py`,
`scripts/notebook_tools/_archive/**`). Pool des autres candidats discriminés first-hand :
2 fantômes (`c785_insert_ackley.py`, `c786_insert_lean_descvisuelle.py` — jamais existé sur disque) ;
1 vivant critique (`hopf_s6_reproduction.py` — référencé ×6 par Lean-30 notebook + 2 README, INTRINSIC v4.32.1) ;
1 gris (`optimize_dvs.py` — successeur à nommer avant archivage, hors scope de cette PR).

## Table 4 colonnes (convention `_archive/`)

| Script | Verdict | Superseded by | Verdict recorded in |
|--------|---------|---------------|---------------------|
| `_fix_leaks_batch1.py` | NO BEATS (one-shot batch terminé ; 70 leaks `Exercice → Exemple guide` posés sur 27 notebooks Search) | none (closed dead-end ; batch 2+ absorbed by `detect_solution_leaks.py` gate — PRs #8407, #10049, #10004, #8294, #8900, #12390, etc.) | PR `0cd10575d` "fix(search): relabel 70 solution leaks as Exemple guide (#1205 Batch 1)" ; commentaire dashboard `[issue #13745]` |

## Pourquoi ce standard

Sans `_archive/` standardisé, un script superseded rejoint un puits de code mort sans en-tête de disposition —
personne ne sait s'il est **encore vivant mal étiquetté** ou **réellement abandonné**. Ce README rend la
décision **vérifiable** : pour chaque fichier archivé, le verdict est daté, le successeur nommé, et la
référence durable (PR mergée, commit, commentaire dashboard) citée.

## Périmètre

- **Inclus** : scripts Python archivés sous `scripts/notebook_tools/_archive/` selon la convention parente.
- **Exclus** : `_archive/` d'autres domaines — chacun a son propre dossier, sa propre table, sa propre
  convention de nommage. Pas d'unification en `docs/archive/code/` (cf convention parente §4 — garder
  `_archive/` près du domaine, scripts référencent des chemins relatifs).

## Pour ajouter un fichier à ce `_archive/`

1. Vérifier les **4 critères** (convention parente §3) : NO BEATS verdict, zéro référence, zéro import, successeur nommé.
2. Ajouter l'en-tête de disposition per-function au fichier déplacé (`# Archive header (standard _archive convention, ...)`).
3. Ajouter la ligne dans la table ci-dessus, datée du jour d'archivage.
4. PR + claim-AMEND sur l'issue umbrella parente avec paths ciblé.

## Voir aussi

- Convention parente : [`docs/reference/_archive-convention.md`](../../../../docs/reference/_archive-convention.md)
- Claim parent : `#13745` « [consolidation] notebook_tools/ : 92 orphelins sur 152 + fusions sélectives (V3) »
- Pipeline de détection successor : `scripts/notebook_tools/detect_solution_leaks.py` (PR #12390 + suite)

---

`Grain: LIGHT/refactor — lane myia-po-2026:CoursIA-2 — prev: MED/research-code #14137`