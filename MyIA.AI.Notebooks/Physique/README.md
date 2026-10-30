# Physique numérique et théorie des champs

La physique est le terrain où une méthode numérique se vérifie le plus durement : les
équations y possèdent souvent une **solution exacte** connue, et un solveur qui ne la
retrouve pas est faux — pas « approximatif ». Cette série prend ce levier au sérieux.
Chaque carnet pose un problème dont la vérité est établie indépendamment du code, puis
fait calculer, et compare.

C'est la raison d'être de la série : ailleurs, un résultat numérique se juge à sa
plausibilité ; ici, il se juge contre une référence exacte, une identité de symétrie ou
une limite analytique.

## Trois sous-séries

Les carnets vivent dans trois dossiers, chacun avec son propre `README.md` qui présente
ses carnets un par un.

### `Jauge/` — symétries et théories de jauge

Trois carnets, du théorème aux réseaux :

- **Théorème de Noether** — la correspondance entre symétrie continue et quantité
  conservée, dérivée symboliquement et vérifiée sur des cas où la conservation est
  connue par ailleurs (énergie, impulsion, charge).
- **Invariance de jauge U(1) → SU(2)** — ce que « jauge » veut dire : la transformation
  dépend du point, le champ de jauge est ce qu'il faut ajouter pour que la dérivée
  reste covariante, et le tenseur de champ est ce qui transforme sans le champ.
- **Yang–Mills sur réseau** — la théorie non abélienne discrétisée, dans le cas
  bidimensionnel où une solution exacte existe, ce qui donne une vérité plantée pour
  comparer l'estimation numérique.

### `Numerique/` — analyse numérique vérifiée

Équations aux dérivées partielles traitées par volumes finis, avec solveur de Riemann
pour les flux : le cas de Burgers sert de banc d'essai, parce qu'il développe un
choc que l'on sait placer et dont la vitesse de propagation est connue
analytiquement — un schéma qui étale le choc ou le déplace au mauvais endroit est
détecté sans ambiguïté.

### `Integrales/` — intégrales et calculs exacts

Le versant calculatoire : intégrales définies et impropres, méthodes analytiques et
vérification numérique croisée. Ces carnets viennent de la série Probas, où ils
servaient d'outils ; ils sont ici chez eux.

## Ce que la série suppose acquis

- **Analyse** : dérivées partielles, intégrales multiples, séries de Fourier.
- **Algèbre** : matrices, groupes et représentations (pour `Jauge/`).
- **Python scientifique** : `numpy`, `scipy`, `matplotlib`, `sympy` pour le calcul
  symbolique.

Aucun prérequis de physique théorique avancée n'est nécessaire pour `Numerique/` et
`Integrales/` ; `Jauge/` introduit les notions dont il a besoin.

## Environnement

- **Kernels** : `python3` pour tous les carnets de la série.
- **GPU** : non requis — calculs symboliques et maillages modestes, dimensionnés pour
  tourner sur un poste CPU.
- **Bibliothèques** : `numpy`, `scipy`, `sympy`, `matplotlib`, installées par le carnet
  de chaque sous-série.

## Ramifications

- **[Probas](../Probas/README.md)** — d'où viennent les carnets d'intégrales, et où les
  mêmes outils servent à l'inférence plutôt qu'à la mécanique.
- **[SymbolicAI](../SymbolicAI/README.md)** — la branche Lean 4 du dépôt : les
  identités que `Jauge/` vérifie numériquement peuvent, pour certaines, être
  démontrées formellement.
- **[Search](../Search/README.md)** — les solveurs de contraintes et les heuristiques
  de recherche qui sous-tendent une partie du calcul scientifique.

## Où trouver l'inventaire

Le catalogue du dépôt (`COURSE_CATALOG.generated.md`) liste les carnets de la série avec
leur noyau, leurs besoins matériels et leur statut — c'est la source des décomptes, et
elle est régénérée automatiquement. Ce README présente les carnets, il ne les compte pas.
