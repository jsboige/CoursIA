# Archive — one-shot fix scripts (item 4-ter #9535)

**Date d'archivage** : 2026-08-06
**Décision** : `chore(repo,#9535): archive 4 one-shot fix scripts + 2 tests (item 4-ter)`
**PR sœurs** : [#9580](https://github.com/jsboige/CoursIA/pull/9580) (item 4-bis, 10 one-shots post-#463) · [#9575](https://github.com/jsboige/CoursIA/pull/9575) (item 4 partial, `recycle_csp*`)

## Contexte

Issue #9535 item 4 propose d'archiver les **one-shots** de `scripts/` racine dont la mission est remplie. Les PR sœurs ci-dessus ont déjà archivé la famille `recycle_csp*` (#9575) puis 10 autres one-shots post-#463 (#9580). Cette PR (item 4-ter) archive les **4 derniers one-shots `fix_*`/`patch_*`** restant à la racine dont la mission est prouvée remplie, avec leurs 2 tests associés.

## Fichiers archivés

| Fichier | LOC | PR d'origine | Mission (one-shot) |
|---|---:|---|---|
| `fix_app14_mcts.py` | 273 | [#580](https://github.com/jsboige/CoursIA/pull/580) | App-14-ConnectFour MCTS state-reset : `MCTS.search()` ne restaurait pas l'état initial → `run_benchmark_mcts()` dérivait vers des positions terminales. Fix : save/restore + `deepcopy`. **Prouvé mergé** : le notebook cible contient désormais `deepcopy` / `initial_state` / `save`. |
| `fix_sudoku_hierarchy.py` | 256 | [#8654](https://github.com/jsboige/CoursIA/pull/8654) | Sudoku HINT-AS-HEADING (tranche 3, EPIC #3966) : dégrade `### Indices` / `### Étapes` etc. en blockquotes `> **… :**`. |
| `fix_texte_hierarchy.py` | 236 | [#8630](https://github.com/jsboige/CoursIA/pull/8630) | GenAI/Texte H1-DEEP / MULTI-H1 / HINT-AS-HEADING burn-down (c.929 re-application, EPIC #3966). |
| `patch_c917_repli.py` | 395 | [#8663](https://github.com/jsboige/CoursIA/pull/8663) | GenAI/Text c.917 repli v2 : réécriture de 12 cellules markdown distinguant run cloud #8281 vs run local-only c.917. |
| `test_fix_sudoku_hierarchy.py` | 300 | [#8654](https://github.com/jsboige/CoursIA/pull/8654) | Test du script ci-dessus (paire). |
| `test_fix_texte_hierarchy.py` | 278 | [#8630](https://github.com/jsboige/CoursIA/pull/8630) | Test du script ci-dessus (paire). |
| **Total** | **1738** | | |

## Justification d'archivage (vs suppression)

Discipline **« Consolider ≠ Archiver »** (CLAUDE.md global) :

1. **ANALYZE** : chaque script est un one-shot dont la mission a été vérifiée remplie firsthand (G.9). Les 4 PR (#580, #8654, #8630, #8663) sont **merged** ; les notebooks cibles portent le fix (ex. App-14 contient `deepcopy`/`save` ; les headings Sudoku/Texte sont dégradés en blockquotes).
2. **MERGE** : 0 call-site repo-wide pour les 4 scripts (grep `MyIA.AI.Notebooks/ scripts/ docs/ .github/ .claude/` — 0 référence externe hors self + doc). Aucune mention dans `docs/reference/scripts-reference.md`.
3. **ARCHIVE** : `git mv` vers `scripts/_archive/one_shot_fixes/` (cf. PR sœurs #9580 / #9575 pour la convention). Historique git 100% préservé (`git log --follow` retrouve le source).

## Pourquoi pas `scripts/notebook_tools/` ?

La disposition item 4 distingue **réutilisable → `notebook_tools/`** vs **one-shot mort → archive**. Ces 4 scripts hardcodent des notebooks et cellules spécifiques à une tranche passée (ex. `fix_sudoku_hierarchy.py` cible 5 patterns de headings Sudoku précis ; `patch_c917_repli.py` réécrit 12 cellules d'un notebook GenAI/Text précis). Ils ne sont pas réutilisables tels quels. Le **pattern** réutilisable (détection HINT-AS-HEADING) vit déjà dans `scripts/notebook_tools/` (détecteur `scan_md_hierarchy`) — ces scripts n'étaient que des applicateurs one-shot de ce pattern sur une tranche donnée.

## Tests archivés ensemble

Les 2 scripts `fix_sudoku_hierarchy.py` et `fix_texte_hierarchy.py` ont chacun un test dans `scripts/tests/` qui les importe par chemin. Archiver le script sans son test laisserait un test cassé dans `scripts/tests/` (le test serait collecté par `pytest.ini` testpaths et échouerait). Les tests sont donc archivés **en paire** avec leur script. `scripts/_archive/` n'est pas dans `pytest.ini` testpaths → les tests archivés ne sont plus collectés (comportement souhaité).

## Pourquoi archiver plutôt que supprimer

- **Préservation historique** : `git log --follow` doit pouvoir retrouver le source d'un commit de 2026-07 (anti-régression). Archive = retirer-de-la-racine-mais-préserver-trace.
- **Référence future** : un audit peut comparer la version pré-fix d'un notebook avec le post-fix (le script archive contient la transformation exacte appliquée).
- **Convention disciple** : `Consolider ≠ Archiver` (CLAUDE.md global) — on archive l'outillage mort, on ne le `rm` pas.

---

# item 4-quater — 2 dead scripts racine (c.9689 / 2026-08-06)

**Décision** : `chore(repo,#9535): archive 2 dead scripts from scripts/ racine (item 4-quater)`
**PR** : [#9731](https://github.com/jsboige/CoursIA/pull/9731) (myia-po-2023:CoursIA-2)

## Fichiers archivés

| Fichier | LOC | Type de mort | Justification |
|---|---:|---|---|
| `fix_string_cells.py` (racine) | 108 | DUPLICATE superseded | Remplacé par `scripts/notebook_tools/fix_string_cells.py` (canonical, argparse + `--genai-only`). Le test `test_fix_string_cells.py` importe depuis le path canonical via `sys.path.insert(0, …/notebook_tools)`, **pas** depuis le root. Le fichier root = 0 call-site en code (4 mentions : self + 2 docs + 1 docstring test). |
| `mcp_buffering_smoke_test.py` | 231 | ONE-SHOT mission remplie | Verify du fix MCP buffering #835 (smoke test `create_stress_notebook` + `run_smoke_test`). Mission prouvée remplie (le fix MCP est en place depuis #835, instrument validé une fois pour toutes). Test pair archivé ensemble (le test importe par `importlib.util.spec_from_file_location`, le path est mis à jour pour pointer le fichier co-localisé dans `_archive/one_shot_fixes/`). |
| **Total** | **339** | | |

## Pourquoi pas suppression

Mêmes invariants que item 4-ter ci-dessus. `git log --follow` doit pouvoir remonter au source pour audit anti-régression ; le pattern « un outil canonique a absorbé la fonctionnalité » est lui-même une leçon de discipline (#9140 : un fix canonique DOIT supprimer ses précurseurs — ici fait via `git mv` archive, jamais `git rm`).

## Note sur `fix_string_cells.py` : la canonicalisation était déjà la bonne décision

`scripts/notebook_tools/fix_string_cells.py` (canonical) :
- API argparse + `--genai-only` + `--apply` + `--dry-run`
- 113 LOC, type hints
- Couvert par `scripts/notebook_tools/tests/test_fix_string_cells.py` (48 tests PASS)

`scripts/fix_string_cells.py` (root, archived) :
- API legacy `fix_notebook_sources` + alias `fix_string_cells = fix_notebook_sources`
- 108 LOC, pas d'argparse
- Pas de test (le seul test importe la version canonical, pas la root)

La migration est **implicite** : la version `notebook_tools/` a supplanté la root sans formaliser le retrait. Item 4-quater formalise l'archivage de la précurseure.

