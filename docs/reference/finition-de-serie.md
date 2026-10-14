# Finition de série : critères de sortie

Régime validé par le mainteneur le 2026-10-05 (issue de suivi #19297). Une série passe en **finition** quand on cesse d'y ajouter des carnets pour la rendre lisible de bout en bout. Elle en sort quand les critères ci-dessous sont remplis.

## Critères

1. **Objectifs de série.** Le README de la série a une section `## Objectifs d'apprentissage`. Elle dit ce que le lecteur saura faire à la fin, en phrases vérifiables (« implémenter A* et justifier son admissibilité »), jamais en thèmes (« la recherche heuristique »).
2. **Blocs de fin de carnet.** Chaque carnet du chemin principal de la série se termine par trois blocs markdown, dans cet ordre :

   | Bloc | Contenu |
   |---|---|
   | `## À retenir` | 3 à 5 points, chacun tiré de ce que le carnet a effectivement montré (une sortie, une mesure, une preuve) |
   | `## Vérifiez votre compréhension` | 2 à 4 questions dont la réponse se trouve dans le carnet. La réponse suit, repliée (`<details>`) ou en fin de bloc |
   | `## Pour aller plus loin` | le carnet suivant de la série, puis lectures et carnets voisins d'autres séries |

   Le tableau récapitulatif de fin de section majeure (déjà exigé) reste en place : « À retenir » le complète, il ne le remplace pas.
3. **Capstone, là où il vient naturellement.** Un carnet qui réinvestit plusieurs carnets de la série sur un problème plus grand. Il n'est pas exigé dans une série où aucun problème ne s'y prête. Si la série n'en a pas, son README le dit en une phrase.

Au niveau du dépôt : un **parcours 0 de 2 h**, tiré du chemin local existant (Search → Sudoku → ML, README racine) et chronométré, est proposé en entrée.

## Comment appliquer

- **Série par série**, quand la série passe en finition. Pas de reprise rétroactive en masse sur les séries qui ne sont pas en finition.
- **Écrire depuis le contenu.** Les points « À retenir » et les questions « Vérifiez » se rédigent après lecture du carnet et de ses sorties. Une question générique (« qu'avez-vous appris ? ») ne compte pas.
- **Markdown seulement.** Ajouter ces blocs ne modifie aucune cellule de code : la ré-exécution n'est pas requise (C.2), et les sorties des carnets non modifiés ne se re-sérialisent pas (C.3).
- **Ne pas toucher deux fois un carnet.** Quand une série a aussi une réorganisation en cours, les blocs commencent par les carnets qui ne sont pas renommés. Les carnets renommés reçoivent leurs blocs après le renommage.
- **Pas de nouvelle taxonomie.** Les classements de maturité existants restent les seuls ; ce régime n'en ajoute pas.

## Mesure

Comptage de départ (2026-10-05, 1492 carnets hors `_archive` et `_output`, sur les titres des cellules markdown) :
- « À retenir » : 14 % des carnets ;
- « Vérifiez votre compréhension » : 1 % ;
- « Pour aller plus loin » : 18 %.

Une section d'objectifs manque dans 5 READMEs de série sur 14 : Complexity, Compression, NLP, RL, SymbolicAI.

Ce comptage de départ inclut les titres voisins : « Points clés à retenir », « Ce qu'il faut retenir », et les titres numérotés comme « ## 7. Pour aller plus loin ». Ce sont les formes les plus fréquentes du dépôt. Une série n'est **finie** qu'avec les titres du tableau ci-dessus. La mesure distingue donc un bloc **présent sous un titre voisin**, qu'il suffit de renommer, d'un bloc **absent**, qu'il faut écrire. Ce partage sert à répartir le travail.

Le chemin principal d'une série est l'ensemble de ses carnets, sous-dossiers compris. En sont exclus `_archive`, `_output`, ainsi que les dossiers que le README de la série écarte nommément. Il ne se définit pas par une profondeur de dossier.

La mesure par série est portée par un script dédié (à écrire, cf #19297), qui permet de déclarer une série finie sans recompter à la main.

## Ordre de passage

1. Search (carte validée, #19253) ;
2. RL (#19255) ;
3. les séries sans objectifs : Complexity, Compression, NLP, SymbolicAI.
