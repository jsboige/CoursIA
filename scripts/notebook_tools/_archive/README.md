# `scripts/notebook_tools/_archive/` — convention standardisée

S'applique au sous-dossier `_archive/` de `scripts/notebook_tools/`. Référence parente :
[`docs/reference/_archive-convention.md`](../../../docs/reference/_archive-convention.md) (modèle ML-Training-Pipeline généralisé,
4 critères d'éligibilité, header disposition per-function).

## État au 2026-10-01

11 fichiers archivés.

### Origine 2026-09-01 (sous-grain `#13745`, claim `myia-po-2026:CoursIA-2`)

- 1 fichier archivé : `_fix_leaks_batch1.py`.
- Pool des autres candidats discriminés first-hand :
  - 2 fantômes (`c785_insert_ackley.py`, `c786_insert_lean_descvisuelle.py` — déclarés « jamais existé sur disque ») ;
  - 1 vivant critique (`hopf_s6_reproduction.py` — référencé ×6 par Lean-30 notebook + 2 README, INTRINSIC v4.32.1) ;
  - 1 gris (`optimize_dvs.py` — successeur à nommer avant archivage, hors scope de cette PR).

### Origine 2026-10-01 (sous-grain `#18153` palier 1, claim `myia-po-2023:CoursIA-2`)

- **10 nouveaux fichiers archivés** (palier 1 vérifié par ai-01 dans #18153, axe D #16473) :
  - 4 batches successeurs de `_fix_leaks_batch1.py` (`_fix_leaks_batch{2,3,4,5}_*.py`) — terminaux absolus, leurs produits sont sur `main` ;
  - 2 insertions déclarées temporaires (`_fix_gt15b_compilation.py`, `_fix_lean34_unused_vars.py`) — produits sur `main`, codepath machine-local ;
  - 2 insertions (`c785_insert_ackley.py`, `c786_insert_lean_descvisuelle.py`) — pas des fantômes (le README du 2026-09-01 se trompait ; ils ont été ajoutés le 2026-07-22 par #7993) ;
  - 2 one-shots machine-local (`_exec_bdd_csharp.py`, `optimize_dvs.py`).

Correction du chapeau 2026-09-01 : les `c785/c786` ne sont pas des fantômes — ce sont des one-shots temporaires, archivés ici en 2026-10-01.

## Table 4 colonnes (convention `_archive/`)

| Script | Verdict | Superseded by | Verdict recorded in |
|--------|---------|---------------|---------------------|
| `_fix_leaks_batch1.py` | NO BEATS (one-shot batch terminé ; 70 leaks `Exercice → Exemple guide` posés sur 27 notebooks Search) | none (closed dead-end ; batch 2+ absorbed by `detect_solution_leaks.py` gate — PRs #8407, #10049, #10004, #8294, #8900, #12390, etc.) | PR `0cd10575d` "fix(search): relabel 70 solution leaks as Exemple guide (#1205 Batch 1)" ; commentaire dashboard `[issue #13745]` |
| `_fix_leaks_batch2_probas.py` | NO BEATS (one-shot batch terminé ; probas solution leaks posés) | none (closed dead-end ; absorbed by `detect_solution_leaks.py` gate — PR #8900) | PR #8900 « fix(search): relabel solution leaks as Exemple guide (#1205 Batch 2) » ; #13745 thread |
| `_fix_leaks_batch3_sudoku.py` | NO BEATS (one-shot batch terminé ; Sudoku solution leaks posés) | none (closed dead-end ; absorbed by `detect_solution_leaks.py` gate — PR #10049) | PR #10049 « fix(sudoku): relabel solution leaks as Exemple guide (#1205 Batch 3) » ; #13745 thread |
| `_fix_leaks_batch4_remaining.py` | NO BEATS (one-shot batch terminé ; remaining solution leaks posés) | none (closed dead-end ; absorbed by `detect_solution_leaks.py` gate — PR #12390) | PR #12390 « fix: relabel remaining solution leaks as Exemple guide (#1205 Batch 4) » ; #13745 thread |
| `_fix_leaks_batch5_c874.py` | NO BEATS (one-shot batch terminé ; c874 Lean solution leaks posés) | none (closed dead-end ; absorbed by `detect_solution_leaks.py` gate — PR #14071) | PR #14071 « fix(lean): relabel c874 solution leaks as Exemple guide (#1205 Batch 5) » ; #13745 thread |
| `_fix_gt15b_compilation.py` | NO BEATS (one-shot compilation fix for GameTheory-15b ; header « temporary ») | none (closed dead-end ; produit sur `main`) | #18153 palier 1 + #13745 umbrella |
| `_fix_lean34_unused_vars.py` | NO BEATS (one-shot unused var cleanup in Lean-34 ; header « temporary », codepath machine-local) | none (closed dead-end ; produit sur `main`) | #18153 palier 1 + #13745 umbrella |
| `c785_insert_ackley.py` | NO BEATS (one-shot Ackley insertion ; codepath machine-local) | none (closed dead-end ; insertion sur `main` via PR #7993) | PR #7993 + #18153 palier 1 |
| `c786_insert_lean_descvisuelle.py` | NO BEATS (one-shot Lean descvisuelle insertion ; codepath machine-local) | none (closed dead-end ; insertion sur `main` via PR #7993) | PR #7993 + #18153 palier 1 |
| `_exec_bdd_csharp.py` | NO BEATS (one-shot BDD C# execution driver ; codepath machine-local) | none (closed dead-end ; pas de consommateur survivant) | #18153 palier 1 + #13745 umbrella |
| `optimize_dvs.py` | NO BEATS (one-shot DVS optimizer ; codepath machine-local) | none (closed dead-end ; pas de consommateur survivant — successeur non nommé, archive décidée sur constat d'usage nul) | #18153 palier 1 + #13745 umbrella |

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

- Convention parente : [`docs/reference/_archive-convention.md`](../../../docs/reference/_archive-convention.md)
- Claim parent : `#13745` « [consolidation] notebook_tools/ : 92 orphelins sur 152 + fusions sélectives (V3) »
- Sous-grain palier 1 : `#18153` « scripts/ : 71 candidats a l'archivage ou au cablage (audit haiku du 27/09, axe D de #16473) »
- Pipeline de détection successor : `scripts/notebook_tools/detect_solution_leaks.py` (PR #12390 + suite)

---

`Grain: LIGHT/refactor — lane myia-po-2023:CoursIA-2 — prev: MED/notebook-python #18598`