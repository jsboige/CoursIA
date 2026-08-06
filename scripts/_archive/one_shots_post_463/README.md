# Archive — one-shots post-#463 (item 4-bis #9535)

**Date d'archivage** : 2026-08-06
**Décision** : `chore(repo,#9535): archive 10 one-shots post-#463 (item 4-bis)`
**PR** : [#TBD après push](https://github.com/jsboige/CoursIA/pull/TBD)
**PR sœur** : [#9575](https://github.com/jsboige/CoursIA/pull/9575) (item 4 partial, recycle_csp* 7f/1902L)

## Contexte

Issue #9535 item 4 propose d'archiver les **one-shots** de `scripts/` racine dont la mission est remplie.
**PR #9575** (item 4 partial, mergeable 2026-08-06) a archivé la famille `recycle_csp3-9.py` (7 fichiers, 1902 LOC) issue de l'EPIC #463 (CSP/App recyclage).

Cette PR sœur (item 4-bis) archive les **10 autres one-shots post-#463** identifiés par `git ls-files scripts/` :

| Fichier | LOC | Date création | Mission |
|---|---:|---|---|
| `fix_app1_recycle.py` | 364 | 2026-04-22 | recyclage App-1-NQueens (PR #480) |
| `fix_app2_recycle.py` | 223 | 2026-04-22 | recyclage App-2-GraphColoring (PR #480) |
| `fix_app3_recycle.py` | 197 | 2026-04-22 | recyclage App-3-... (PR #480) |
| `fix_app5_recycle.py` | 78 | 2026-04-22 | recyclage App-5-... (PR #480) |
| `fix_app6_recycle.py` | 313 | 2026-04-22 | recyclage App-6-Minesweeper (PR #480) |
| `fix_app11_recycle.py` | 157 | 2026-04-22 | recyclage App-11-... (PR #480) |
| `fix_csp9_abt.py` | 655 | 2026-05-.. | correctif ABT/AWC implementation CSP-9 |
| `fix_csp9_stale_markdown.py` | 193 | 2026-05-.. | markdown sync post-correction ABT/AWC (suivi PR #578) |
| `fix_issue_420.py` | 319 | 2026-04-22 | recyclage CSP-1/CSP-2 stubs (issue #420) |
| `create_nb8.py` | 498 | 2026-.. | création notebook GameTheory-8-CombinatorialGames (issue #910) |
| **Total** | **2997** | | |

## Justification d'archivage (vs suppression)

Discipline **« Consolider ≠ Archiver »** (CLAUDE.md global) :
1. **ANALYZE** : chaque script = un one-shot dont la mission a été vérifiée remplie.
2. **MERGE** : la fonctionnalité a été mergée dans les notebooks cibles (App-1..11, CSP-1/2/9, GameTheory-8). 0 call-site repo-wide (grep `MyIA.AI.Notebooks/ scripts/ docs/ .github/ .claude/`).
3. **ARCHIVE** : `git mv` vers `scripts/_archive/one_shots_post_463/` (cf #9575 sister PR pour `recycle_csp` → `scripts/_archive/recycle_csp/`). Historique git 100% préservé (chacun des 10 fichiers a **exactement 1 commit** sur origin/main).

## Pourquoi archiver plutôt que supprimer

- **Préservation historique** : `git log --follow` doit pouvoir retrouver le source d'un commit de 2026-04-22 (anti-régression). Archive = supprimer-de-la-racine-mais-préserver-trace.
- **Référence future** : un audit ultérieur peut avoir besoin de comparer la version pré-fix d'un notebook avec le post-fix (le script archive contient la transformation).
- **Convention disciple** : `Consolider ≠ Archiver` (CLAUDE.md global) — on archive le outillage mort, on ne le rm pas.
- **Sister pattern** : analogue exact à #9575 (`recycle_csp3-9.py` archivés 2026-08-06). Mêmes conventions, même canal, même gitignore (l'archive n'est PAS gitignored — elle reste trackée).

## Preuves G.9 (firsthand)

1. **Call-sites repo-wide = 0** pour 8/10 fichiers :
   ```
   grep -rln "<nom_fichier>" --include="*.py" --include="*.ipynb" --include="*.md" \
     --include="*.yml" --include="*.json" MyIA.AI.Notebooks/ scripts/ docs/ .github/ .claude/
   → 0 résultats hors les fichiers eux-mêmes
   ```
   Exceptions : `fix_issue_420.py` est référencé dans `scripts/recycle_csp3.py` + `recycle_csp4.py` (cross-ref textuel dans le code source). Mais ces 2 fichiers viennent juste d'être archivés (#9575 sister PR) → lien archive → archive, OK.

2. **scripts-reference.md** : 0 mention des 10 fichiers archive candidats (les `extract_*` mentionnés dans le catalogue ne sont **PAS** dans cette PR — outils actifs, hors scope).

3. **Historique Git 1 commit/fichier** : chaque archive candidat a exactement 1 commit upstream (vérifié `git log origin/main -- <fichier>`).

4. **Mission remplie** :
   - **App-1..11** : PR #480 MERGED 2026-04-22 (cf `fix(app-1): recyclage solutions etudiants + stubs TODO (#463) (#480)`).
   - **CSP-9 ABT** : `fix(csp-9): correct ABT/AWC implementation` MERGED antérieurement.
   - **CSP-9 markdown** : `fix(csp-9): sync 3 markdown cells post-ABT/AWC fix` (suivi PR #578).
   - **CSP-1/2 (#420)** : PR antérieure MERGED.
   - **GameTheory-8** : notebooks `GameTheory-8-CombinatorialGames.ipynb` + `GameTheory-8b-Lean-CombinatorialGames.ipynb` + `GameTheory-8c-CombinatorialGames-Csharp.ipynb` + `GameTheory-8c-CombinatorialGames-Python.ipynb` existent tous sur main. Le script `create_nb8.py` a fait son travail.

## Hors scope (volontairement NON archivés)

| Fichier | LOC | Raison |
|---|---:|---|
| `scripts/extract_pptx_titles.py` | 59 | OUTIL ACTIF — référencé `docs/reference/scripts-reference.md` L200 + 5 fichiers de tests (notebook_tools/tests/, scripts/tests/) |
| `scripts/extract_slidev_titles.py` | 88 | OUTIL ACTIF — idem, 5 fichiers de tests |

Ces 2 outils sont des **helpers outillés** (CLAUDE.md global « un script dédié existe ») et restent à la racine `scripts/`. Pas des one-shots.

## Liens

- **#9535** — Epic cleanup repo pérenne (item 4-bis partial)
- **#9575** — PR sœur wakeup 39 : archive `recycle_csp*` 7f/1902L
- **#463** — Issue source : « CSP/App recyclage »
- **PR #480** — `fix(app-1): recyclage solutions etudiants + stubs TODO (#463)`
- **PR #578** — `fix(csp-9): correct ABT/AWC implementation`
- **#910** — Issue source : « repository cleanup — debris »
- CLAUDE.md global — « Consolider ≠ Archiver » : ANALYZE → MERGE → ARCHIVE avec header date + superseded-by + merged features
- `.claude/rules/harness-hygiene.md` — 3 tiers d'info ; status = dashboard, pas repo
- `.claude/rules/catalog-pr-hygiene.md` — R3 atomique <3000L / <15 fichiers

## Convention de référence

Tout futur agent qui tombe sur un fichier dans `scripts/_archive/` doit :
1. **Vérifier `git log --follow`** pour comprendre la mission d'origine (historique préservé).
2. **NE PAS réactiver** sans issue dédiée (l'archive est un snapshot, pas un outil).
3. **Si l'outil est réactivé** : le **sortir** de `_archive/` via `git mv` + PR dédiée avec justification.
