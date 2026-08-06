# `scripts/_archive/recycle_csp/` — CSP recycle one-shots (archived 2026-08-06)

## Contexte

Cette archive contient les **7 one-shots historiques** (`recycle_csp3.py` à `recycle_csp9.py`) qui recyclaient les solutions étudiantes des notebooks CSP-3-Advanced à CSP-9-Distributed en `Exemple` labelés + créaient de nouveaux `Exercice` stubs avec variantes.

## Date d'archivage

2026-08-06 (cycle worker po-2023 wakeup 39, c.9535-item4 partial).

## Justification (`Consolider ≠ Archiver`, CLAUDE.md global)

1. **ANALYZE** ✓ — chaque script a une seule fonction : modifier **un** notebook CSP-* (recycler solutions étudiantes en labeled Exemples + créer exercise stubs variants).
2. **MERGE** ✓ — la fonctionnalité est **déjà mergée dans les notebooks cibles**. Plus rien à fusionner ailleurs.
3. **ARCHIVE** ✓ — déplacer vers ce dossier avec header documentant date + PRs supersedantes + features préservées.

## PRs supersedantes (post-archivage)

| Notebook | PR supersedante | Statut |
|---|---|---|
| `CSP-3-Advanced` | [#469](https://github.com/jsboige/CoursIA/pull/469) (`fix(csp-3): recycle student solutions into Exemples + new exercise stubs (refs #463)`) | MERGED 2026-04-22 |
| `CSP-9-Distributed` | [#475](https://github.com/jsboige/CoursIA/pull/475) (`fix(csp): recycle CSP-9-Distributed solutions into exercices with variant stubs (refs #463)`) | MERGED 2026-04-22 |
| `CSP-4/5/6/7/8` | (même famille #463, dates avoisinantes) | MERGED |

Issue #463 (CLOSED 2026-04-22) : « CSP leak recyclage » — entièrement résolu par ces 7 PRs.

## Features préservées (par script)

| Script | Fonction archivée | Notebook cible |
|---|---|---|
| `recycle_csp3.py` (373 L) | SEND+MORE → Exemple, Ex1: CROSS+ROADS=DANGER ; N-Reines symmetry → Exemple, Ex2: N-Reines 12x12 ; Mini-TSP Circuit → Exemple, Ex3: TSP 6 nodes | `CSP-3-Advanced.ipynb` |
| `recycle_csp4.py` (240 L) | (variante CSP-4) | `CSP-4-...ipynb` |
| `recycle_csp5.py` (285 L) | (variante CSP-5) | `CSP-5-...ipynb` |
| `recycle_csp6.py` (276 L) | (variante CSP-6) | `CSP-6-...ipynb` |
| `recycle_csp7.py` (252 L) | (variante CSP-7) | `CSP-7-...ipynb` |
| `recycle_csp8.py` (238 L) | (variante CSP-8) | `CSP-8-...ipynb` |
| `recycle_csp9.py` (238 L) | N-reines distribuées ABT → 5-node graph coloring with 5 colors ; ABT vs AWC comparison → constraint density impact study ; Multi-agent negotiation → 5-agent task allocation ; Information leakage measure → 3-level privacy comparison (38 → 46 cells, +8 : 4 md énoncés + 4 code stubs) | `CSP-9-Distributed.ipynb` |

## Call-sites

- **Repo-wide** : `grep -rln "recycle_csp" --include="*.py" --include="*.ipynb" --include="*.md" --include="*.yml" --include="*.json"` = **0** résultats (en dehors des 7 fichiers eux-mêmes et ce README).
- **scripts-reference.md** : aucun résultat.
- Aucun import, aucune référence fonctionnelle ailleurs.

## Pourquoi archiver plutôt que supprimer

- **Traçabilité** : ce sont des one-shots liés à des **PRs MERGED avec valeur historique**. Supprimer = perte du diff-source.
- **PR-review** : un reviewer qui regarde un commit de 2026-04 doit pouvoir retrouver le script utilisé.
- **Anti-regression** : `git log --follow scripts/_archive/recycle_csp/recycle_csp9.py` continue de pointer vers le commit initial (`fd7b8eea` / `cf755fe6`).

## Pattern sœur

Cette archive suit la convention `scripts/_archive/<famille>/` déjà utilisée pour d'autres familles historiques du repo.

---

**Refs** : #9535 item 4 partial · #463 (CLOSED) · PRs #469/#475 (et sœurs).