# Archive — SymbolicLearning

Ce dossier conserve le matériel de veille sorti de la série. Il suit la
[convention `_archive/`](../../../../docs/reference/_archive-convention.md) :
le niveau `_archive/` porte le registre de disposition, chaque lot archivé vit
dans un sous-dossier **daté** qui nomme sa propre archive.

## Registre de disposition

| Fichier | Verdict | Superseded by | Verdict recorded in |
|---|---|---|---|
| `2026-07-04-Neurosymbolic-EML-precurseur-SL12/EML-NAND-Explore.ipynb` | INCONCLUSIF — veille #4653 close (atome EML non booléen : erreur max 0,253 sur les coins) | [`../SL-12-DifferentiableLogicGateNetworks.ipynb`](../SL-12-DifferentiableLogicGateNetworks.ipynb) (difflogic, porte logique apprise parmi 16) | [README du sous-dossier](2026-07-04-Neurosymbolic-EML-precurseur-SL12/README.md) ; `SL-12` cell[2] ; issue #4653 |
| `2026-07-04-Neurosymbolic-EML-precurseur-SL12/EML-NAND-Compose.ipynb` | INCONFIRMÉ — la discipline de composition (Table 3) ne franchit pas la barrière parité-3 (plafond 0,250) | [`../SL-12-DifferentiableLogicGateNetworks.ipynb`](../SL-12-DifferentiableLogicGateNetworks.ipynb) (difflogic) | [README du sous-dossier](2026-07-04-Neurosymbolic-EML-precurseur-SL12/README.md) ; `SL-12` cell[2] ; issue #4653 |

Les sorties des deux carnets (MSE, exactitudes, tableaux de multistarts) sont
conservées telles quelles dans leurs cellules : la preuve du verdict vit dans
l'enregistrement, pas dans une reformulation.

## Règle d'usage

- **Aucun import actif** : ces carnets ne sont référencés par aucun autre
  notebook de la série ; le successeur `SL-12` les cite comme préquelle.
- **Réactivation explicite** : la procédure `git mv` de restauration est
  consignée dans le README du sous-dossier daté. Elle exige une issue dédiée.
- **Préservation, pas suppression** : l'archivage du 2026-07-04 conserve
  l'historique complet, conformément à « Consolider != Archiver ».

## Références

- #13749 — standardisation des dossiers `_archive/`
- #4653 — veille EML (fermée avec lien vers cette archive)
- [README du lot daté](2026-07-04-Neurosymbolic-EML-precurseur-SL12/README.md)
- [convention `_archive/`](../../../../docs/reference/_archive-convention.md)
