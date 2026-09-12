# Archive — scripts de correction ponctuelle

**Date d'archivage** : 2026-08-06

**Décisions** : PR #9607 (item 4-ter de #9535) et PR #9731 (item 4-quater)

**Standard** : [`docs/reference/_archive-convention.md`](../../../docs/reference/_archive-convention.md)

Ce dossier conserve neuf scripts retirés de l'outillage actif après livraison de
leur mission ou absorption de leur comportement. Ils restent consultables pour
retrouver les transformations exactes appliquées en 2026 ; ils ne doivent pas
être importés ni rejoués sans une issue dédiée.

## Registre de disposition

| Script | Verdict | Superseded by | Verdict recorded in |
|---|---|---|---|
| `fix_app14_mcts.py` | MISSION FULFILLED (2026-04-10) | sortie : cellules `mcts-impl`, `benchmark-mcts` et `2a282f84` de `MyIA.AI.Notebooks/Search/Applications/Search/App-14-ConnectFour-Adversarial.ipynb` | PR #580 (`0ff88db90`), PR #9607 |
| `fix_string_cells.py` | DUPLICATE SUPERSEDED | `scripts/notebook_tools/fix_string_cells.py` (`convert_string_to_list`, `fix_list_newlines`, `fix_notebook`, `main`) | PR #9731 ; `scripts/notebook_tools/tests/test_fix_string_cells.py` |
| `fix_sudoku_hierarchy.py` | OBSOLETE — 34 démotions livrées | `scripts/notebook_tools/demote_md_asides.py` ; garde `scripts/notebook_tools/scan_md_hierarchy.py` | PR #8654 (`4827e297b`), PR #9607 |
| `fix_texte_hierarchy.py` | OBSOLETE — burn-down livré | `scripts/notebook_tools/demote_md_asides.py` pour les apartés ; aucun successeur pour `_demote_first_line_h1` | PR #8630 (`bbf6f9a70`), PR #9607 |
| `mcp_buffering_smoke_test.py` | MISSION FULFILLED — instrument one-shot validé | none — closed dead-end ; le correctif #835 vit dans le serveur MCP externe `jupyter-papermill-mcp-server` | PR #835 (`2d1f644ca`), PR #9731 |
| `patch_c917_repli.py` | SUPERSEDED — repli local-only remplacé par une exécution réelle | none — closed dead-end ; sortie retirée de `10_LocalLlama.ipynb` par PR #8707 | PR #8663 (`45fad5df4`), PR #8707 (`207a87d77`), PR #8743, PR #9607 |
| `test_fix_sudoku_hierarchy.py` | PAIR-ARCHIVED — import dormant cassé après déplacement | couverture vivante : `scripts/notebook_tools/tests/test_demote_md_asides.py` | PR #9273 (`53b984a74`), PR #9607 |
| `test_fix_texte_hierarchy.py` | PAIR-ARCHIVED — import dormant cassé après déplacement | couverture partielle des apartés : `test_demote_md_asides.py` ; aucun successeur pour `_demote_first_line_h1` | PR #9607 |
| `test_mcp_buffering_smoke_test.py` | PAIR-ARCHIVED — import co-localisé valide | none — test historique conservé avec son instrument | PR #2546 (`e7069641f`), PR #9731 |

## Analyse et préservation

### App-14 MCTS

La PR #580 a appliqué le reset d'état MCTS et livré le script avec son notebook.
Sur `main`, la cellule `mcts-impl` sauvegarde et restaure `initial_state`, la
cellule `benchmark-mcts` crée un jeu frais, et `2a282f84` porte l'interprétation
post-correction. Le script n'a donc plus de rôle exécutable.

### Cellules source

La version racine de `fix_string_cells.py` a été absorbée par
`scripts/notebook_tools/fix_string_cells.py`. Le successeur sépare la conversion
STRING→LIST (`convert_string_to_list`), la réparation des retours à la ligne
(`fix_list_newlines`) et le pilote (`fix_notebook`), avec une CLI argparse
`--dry-run` / `--genai-only`. Le README antérieur lui attribuait à tort un flag
`--apply`, absent du source actuel.

### Hiérarchie markdown

`fix_sudoku_hierarchy.py` est entièrement absorbé par `demote_md_asides.py` :
détection des cibles, préservation du format nbformat, démotion, pilote et CLI.
Les 34 apartés livrés par #8654 subsistent sous forme de blockquotes et le garde
`scan_md_hierarchy.py` couvre la régression.

Pour `fix_texte_hierarchy.py`, l'absorption est partielle et documentée sans
l'élargir artificiellement : `demote_md_asides.py` couvre `Indices` et les
variantes `Pistes d'…`, mais pas les variantes `Pistes pour aller plus loin`.
La fonction `_demote_first_line_h1` reste une référence sans successeur : le
garde actif détecte H1-DEEP, mais aucun démoteur canonique ne l'applique.

### Repli c.917

La PR #8663 avait appliqué le repli local-only de `patch_c917_repli.py`. La PR
#8707 l'a ensuite remplacé par la vraie ré-exécution de `10_LocalLlama.ipynb`
sur trois endpoints ; #8743 et #12331 ont poursuivi les exécutions réelles. Le
notebook actuel ne contient plus le récit local-only du repli ; deux notes de
provenance préfixées subsistent dans des cellules héritées de #8281. Le script
est conservé comme trace d'une voie transitoire résolue, pas comme patch à
rejouer.

### Buffering MCP

`mcp_buffering_smoke_test.py` fabriquait trois notebooks de stress et le plan de
validation du correctif #835. Le serveur concerné vit hors de ce dépôt. Le test
co-localisé reste importable, mais ni l'instrument ni son test ne sont collectés
par défaut depuis `scripts/_archive/`.

## État des tests archivés

Les tests ont été déplacés avec leurs scripts afin de ne laisser aucun test
collecté cassé dans `scripts/tests/`. Ils sont désormais des témoins historiques,
pas une suite active :

- `test_fix_sudoku_hierarchy.py` calcule encore son module via
  `parent.parent`, donc pointe vers `scripts/_archive/fix_sudoku_hierarchy.py`,
  qui n'existe pas ;
- `test_fix_texte_hierarchy.py` ajoute `scripts/_archive` à `sys.path`, donc son
  import plat ne trouve plus le module co-localisé ;
- `test_mcp_buffering_smoke_test.py` utilise le chemin co-localisé correct.

Ces deux imports dormants cassés sont consignés plutôt que réparés : les réparer
réactiverait des tests volontairement sortis de la collecte, sans restaurer les
outils comme API active. La couverture vivante de la démotion d'apartés se trouve
dans `scripts/notebook_tools/tests/test_demote_md_asides.py`.

## Pourquoi archiver plutôt que supprimer

- `git log --follow` préserve le source exact et les décisions de 2026 ;
- les headers donnent une disposition à chaque fonction ou entrée top-level ;
- aucun script actif n'importe ces fichiers ;
- toute réactivation doit passer par une issue puis un `git mv` vers un
  emplacement actif, avec tests remis dans la collecte.

## Références

- #9535 — nettoyage et rangement du dépôt
- PR #9607 — archivage item 4-ter
- PR #9731 — archivage item 4-quater
- #13749 — standardisation des dossiers `_archive/`
- `scripts/_archive/one_shots_post_463/README.md` — tranche sœur
- `scripts/_archive/recycle_csp/README.md` — tranche sœur
