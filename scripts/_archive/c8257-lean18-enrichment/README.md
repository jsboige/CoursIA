# Archive — c.8257 Lean-18 enrichment helpers

**Date d'archivage** : 2026-09-02
**Décision** : `chore(scripts,#14251): archiver scripts c.8257 enrich_lean18.py + verify_lean18.py (chemin obsolète post-#13685)`
**Issue** : [#14251](https://github.com/jsboige/CoursIA/issues/14251)
**Refs** : #13841 (issue parent), #13685 (descent Search/Part1-Foundations), #14250 (rename minimal)

## Contexte

Issue #14251 : les scripts c.8257 `scripts/enrich_lean18.py` et `scripts/verify_lean18.py` réfèrent l'ancien chemin du notebook qui n'a **plus** la même position depuis PR #13685 (descent vers `Search/Part1-Foundations/`) :

```python
NB_PATH = Path("MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-18-Search-AStar-Optimality.ipynb")  # ← N'EXISTE PLUS
```

Après PR #13685, le notebook est sous `MyIA.AI.Notebooks/Search/Part1-Foundations/Lean-18-Search-AStar-Optimality.ipynb` (descent vers Search/). PR #14250 a ensuite ajouté le rename minimal (`Lean-18-Search-AStar-Optimality` → `Search-03e-AStar-Optimality`) — voir PR #14250 body pour la décision sur le préfixe.

**Cause structurelle** : ces scripts sont des **helpers one-shot c.8257** utilisés pour enrichir et vérifier le notebook lors de l'enrichissement initial. Une fois leur travail terminé (c.8257 = #10720), ils sont devenus **historiques** mais n'ont pas été archivés.

## Fichiers archivés

| Fichier | LOC | PR d'origine | Mission (one-shot) |
|---|---:|---|---|
| `enrich_lean18.py` | 86 | [#10720](https://github.com/jsboige/CoursIA/pull/10720) (commit `283676536a`, 2026-08-14) | Enrichissement : append des blocs "**Le pont**" à 13 markdown cells de Lean-18, préserve le format `source` list-of-strings (L935 ★), ne modifie que les `cell_id` ciblés. **Prouvé rempli** : le notebook cible contient désormais les 13 blocs "Le pont" — toute re-exécution du script sur le notebook actuel échouerait avec `KeyError` sur les `cell_id` (le format et les ids ont changé depuis). |
| `verify_lean18.py` | 26 | [#10720](https://github.com/jsboige/CoursIA/pull/10720) | Vérification post-enrichissement : compte cells, chars/code, ids uniques, nbformat, CRLF/LF. **Prouvé rempli** : les invariants sont satisfaits (le notebook est committé avec les bons chiffres). |

## Préservation

- **`git mv`** (pas `rm`) : l'historique git complet est préservé (blobs + trees).
- **Blobs toujours accessibles** : `git log --all -- scripts/_archive/c8257-lean18-enrichment/enrich_lean18.py` et `verify_lean18.py` continuent à montrer le commit d'origine `283676536a` (#10720).
- **Chemin de référence conservé** dans ce README pour quiconque voudrait re-trouver le script par cycle (c.8257 → #10720).
- Aucun script n'est **perdu** : tout est récupérable via `git show 283676536a:scripts/enrich_lean18.py` ou via ce dossier.

## Hors scope (préservé pour info)

- **PR #14250** (rename minimal `Lean-18-Search-AStar-Optimality` → `Search-03e-AStar-Optimality`) : n'a PAS modifié le chemin dans ces scripts (le rename était minimal = juste le notebook). PR #14251 archive les scripts — le rename complet notebook + scripts aurait été trop large.
- **PR #13685** (descent Search/Part1-Foundations) : le notebook a été déplacé, mais les scripts référençaient encore l'ancien chemin via un Path string littéral — pas de wildcard, pas de glob, pas de résolution runtime. **Cause du bug** : path hardcodé.
- Aucune référence aux scripts `enrich_lean18.py` / `verify_lean18.py` ailleurs dans le repo (vérifié par `git grep` — voir PR body) : archivage sans risque d'import cassé.

## Convention

Voir les autres dossiers `scripts/_archive/` pour les PRs sœurs de la même initiative (#9535) : `one_shot_fixes/` (item 4-ter), `one_shots_post_463/` (item 4-bis), `recycle_csp/` (item 4 partial).