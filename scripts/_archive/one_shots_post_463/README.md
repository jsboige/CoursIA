# Archive — one-shots post-#463 (item 4-bis #9535)

**Date d'archivage** : 2026-08-06

**Décision d'archivage** : [PR #9580](https://github.com/jsboige/CoursIA/pull/9580)

**PR sœur** : [#9575](https://github.com/jsboige/CoursIA/pull/9575) (`recycle_csp3-9.py`)

## Registre de disposition

Les dix scripts sont des migrations ponctuelles dont la sortie a été incorporée
dans les notebooks cibles. Ils sont conservés pour la traçabilité historique,
pas pour être importés ou rejoués. Chaque fichier porte désormais le détail de
disposition de ses fonctions selon la
[convention `_archive/`](../../../docs/reference/_archive-convention.md).

| Script | Verdict | Superseded by | Verdict recorded in |
|---|---|---|---|
| `create_nb8.py` | MISSION FULFILLED (2026-01-31) | sortie : `GameTheory-08-CombinatorialGames.ipynb` | `3fb947748`, PR #911, PR #9580, PR #12241 |
| `fix_app1_recycle.py` | MISSION FULFILLED (2026-04-22) | sortie : `App-1-NQueens.ipynb` | PR #480 (`a398145d9`), PR #9580 |
| `fix_app2_recycle.py` | MISSION FULFILLED (2026-04-22) | sortie : `App-2-GraphColoring.ipynb` | PR #477 (`c8f95b233`), PR #9580 |
| `fix_app3_recycle.py` | MISSION FULFILLED (2026-04-22) | sortie : `App-3-NurseScheduling.ipynb` | PR #468 (`23b98f3de`), PR #9580 |
| `fix_app5_recycle.py` | MISSION FULFILLED (2026-04-22) | sortie : `App-5-Timetabling.ipynb` | PR #482 (`24ecee8ad`), PR #9580 |
| `fix_app6_recycle.py` | MISSION FULFILLED (2026-04-22) | sortie : `App-6-Minesweeper.ipynb` | PR #478 (`3cfd8dd68`), PR #9580 |
| `fix_app11_recycle.py` | MISSION FULFILLED (2026-04-22) | sortie : `App-11-Picross.ipynb` | PR #476 (`49fb3d5a6`), PR #9580 |
| `fix_csp9_abt.py` | MISSION FULFILLED (2026-04-28) | sortie : code et interprétations de `CSP-9-Distributed.ipynb` | `d45c05dda` (attribué à PR #578 par le suivi `d4ee281aa`), PR #9580 |
| `fix_csp9_stale_markdown.py` | MISSION FULFILLED (2026-04-28) | sortie : cellules `f7e21456`, `070a53e6`, `8f050be3` de `CSP-9-Distributed.ipynb` | `d4ee281aa`, PR #9580 |
| `fix_issue_420.py` | FULFILLED puis SUPERSEDED | none — closed dead-end après le TP étudiant #601 et les reprises lib-vs-lib | PR #453 (`cc4f86d55`), PR #601, PRs #11789/#11797, PR #9580 |

Les chemins complets des sorties figurent dans les headers des scripts afin que
le registre reste lisible sans alourdir cette table.

## Analyse et préservation

L'issue #9535 item 4 a archivé les one-shots de `scripts/` racine dont la
mission était remplie. PR #9575 a traité la famille `recycle_csp3-9.py`; PR
#9580 a déplacé les dix scripts ci-dessus via `git mv`, préservant leur
historique.

L'audit per-function de 2026-09 a vérifié les points suivants :

1. **Chaque fonction a une disposition.** Les helpers locaux restent conservés
   comme référence ; les fonctions de migration pointent vers le notebook ou
   les cellules qui ont reçu leur résultat.
2. **Les sorties sont présentes.** Les marqueurs des migrations App-1/2/3/5/6/11
   sont encore visibles dans les notebooks actuels. Les réécritures ABT/AWC et
   les trois cellules markdown de CSP-9 sont également présentes.
3. **Le cas #420 est explicitement historique.** La transformation a bien été
   appliquée par PR #453, puis son résultat a été légitimement remplacé par le
   TP étudiant #601 et les reprises lib-vs-lib #11789/#11797. Le script est un
   témoin du pré-TP, pas un successeur actif.
4. **Aucun import actif.** Les seuls renvois textuels vers `fix_issue_420.py`
   viennent de deux scripts eux-mêmes archivés sous `recycle_csp/`.
5. **Aucune entrée au catalogue d'outils.** Aucun de ces dix fichiers n'est
   référencé par `docs/reference/scripts-reference.md`.

L'audit a aussi corrigé deux affirmations trop larges du README initial : les six
scripts App ne relevaient pas tous de PR #480, et `create_nb8.py` a quatre
commits dans son histoire (création, déplacement, archivage, puis zero-padding),
pas un seul.

## Pourquoi archiver plutôt que supprimer

- **Préservation historique** : `git log --follow` retrouve le source et les
  transformations d'origine.
- **Auditabilité** : les scripts montrent exactement comment les notebooks ont
  été mutés lors des migrations ponctuelles.
- **Non-réactivation implicite** : l'archive reste un snapshot ; toute reprise
  passe par une issue et un `git mv` vers un emplacement actif.

## Hors scope volontairement non archivé

| Fichier | Raison |
|---|---|
| `scripts/extract_pptx_titles.py` | outil actif, documenté et testé |
| `scripts/extract_slidev_titles.py` | outil actif, documenté et testé |

Ces deux helpers restent à la racine `scripts/`; ils ne sont pas des one-shots.

## Références

- #9535 — Epic de nettoyage du dépôt (item 4-bis)
- PR #9580 — archivage des dix scripts de ce dossier
- PR #9575 — archive sœur `recycle_csp/`
- #463 — recyclage CSP/App
- #420 — correction des stubs CSP-1/CSP-2
- #910 — nettoyage ayant déplacé `create_nb8.py` vers `scripts/`
- #13749 — standardisation des dossiers `_archive/`
- `docs/reference/_archive-convention.md` — standard README + headers per-function

## Convention de réactivation

Tout futur agent qui rencontre un fichier dans ce dossier doit :

1. lire son header et `git log --follow` ;
2. ne pas le réactiver sans issue dédiée ;
3. le sortir de `_archive/` par `git mv` dans une PR justifiant son nouveau rôle.
