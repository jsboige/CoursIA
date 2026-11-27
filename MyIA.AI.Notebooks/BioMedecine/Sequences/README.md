# Séquences — l'optimum s'aligne, il ne se devine pas

[↑ Bio & Médecine](../README.md)

Comparer deux séquences d'ADN ou de protéines, c'est chercher un appariement de caractères qui maximise un score : accords récompensés, désaccords et brèches pénalisés. L'alignement optimal n'est pas celui qui « ressemble » le plus à l'œil : c'est celui dont le score est le plus grand parmi tous les alignements possibles, et ce maximum se calcule exactement.

Cette sous-série écrit les algorithmes classiques à partir de zéro — Needleman-Wunsch pour l'alignement global, Smith-Waterman pour l'alignement local — puis les soumet à une bibliothèque de référence qui ne partage aucune ligne avec eux. Elle construit ensuite deux cas où le contrôle doit échouer, pour montrer qu'il sait le faire.

Le carnet s'adresse à un étudiant de licence qui connaît Python et sait ce qu'est une récurrence. Aucune connaissance préalable de la bio-informatique n'est supposée : chaque notion — jeu de score, matrice de substitution, pénalité de brèche — est introduite avant d'être employée.

## Comment lire ce README — Découverte

Le principe [« Choisir sa vitesse de lecture »](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture) distingue le parcours principal, les approfondissements et les prolongements de recherche.

- **Vous découvrez** : commencez par Séquences-01. Le modèle, la récurrence, le contrôle, puis les deux contre-témoins, dans l'ordre du carnet.
- **Vous creusez un palier** : la section « Approfondissements » dit ce que chaque contrôle mesure et ce qu'il laisse ouvert.
- **Vous cherchez la recherche en cours** : « Pour aller plus loin » nomme les extensions prévues de la sous-série et les questions qu'elles ouvrent.

## Parcours principal — Licence

| # | Notebook | Ce qu'on y apprend | Public | Pour approfondir |
|---|---|---|---|---|
| 01 | [Séquences-01 — Aligner deux séquences : l'optimum se calcule, il ne se devine pas](Sequences-01-Alignement-Programmation-Dynamique-Python.ipynb) | La récurrence de Needleman-Wunsch et son retour sur trace, écrits à la main, dont le score s'accorde avec `Bio.Align.PairwiseAligner` sur **200 paires** d'ADN sans un seul désaccord (scores de `-13` à `4`, moyenne `-2,79`). L'alignement local de Smith-Waterman, qui isole un motif planté à `9` points là où l'alignement global de la même paire n'en vaut que `4`. Un aligneur glouton, qui perd sur `197` paires sur `200` (écart médian `14`, maximal `29`). Le contrôle lui-même, privé de son jeu de score, qui rend `200` désaccords sur `200`. Enfin BLOSUM62 chargée telle quelle, avec laquelle les deux voies s'accordent sur `12` pour `HEAGAWGHEE` / `PAWHEAE`. | Licence : Python, récurrences, tableaux numpy. Outils : numpy, matplotlib, biopython. | Les trois exercices (brèche affine, dénombrement des optimaux, matrice et colonnes), puis les extensions de la sous-série. |

Un seul carnet pour l'instant. Les feuilles suivantes — matrices de poids positionnelles et inférence de motif, heuristiques de graines de type BLAST, profils HMM — viendront s'ajouter ici.

## Approfondissements — Licence avancée

### Autour de 01 : un contrôle, trois usages

Le carnet n'a qu'une bibliothèque de contrôle, mais il l'interroge sur trois questions différentes — et c'est la variété des questions, non celle des outils, qui fait la valeur du contrôle.

**Le score global.** La récurrence écrite dans le carnet remplit une table `F[i][j]` à partir de trois origines possibles ; la bibliothèque fait de même dans son propre code. Les deux rendent des entiers, comparés sans tolérance sur 200 paires tirées avec une graine fixe : zéro désaccord. Sur l'exemple du manuel, le score vaut `2` des deux côtés, et la bibliothèque dénombre `3` alignements optimaux là où le retour sur trace n'en rend qu'un.

**Le score local.** Même comparaison, en mode local, sur une paire où un motif de huit caractères a été inséré dans deux fonds différents : `9` de part et d'autre. Le point de comparaison interne est le score global de la même paire, `4` : le local refuse de payer les extrémités divergentes, et c'est toute la différence entre les deux algorithmes.

**Une matrice publiée.** BLOSUM62 est chargée depuis Biopython, convertie en dictionnaire, puis employée par le calcul écrit ici : sur `HEAGAWGHEE` / `PAWHEAE` avec une brèche linéaire à `-4`, les deux voies tombent sur `12`. L'accord ne dépend donc pas de la matrice d'identité du carnet.

### Autour de 01 : les contre-témoins, et ce qu'ils attrapent

Un contrôle qui ne sait pas échouer ne prouve rien. Le carnet construit trois cas d'échec, de natures différentes.

- **Un aligneur glouton.** Il suit la diagonale tant que la colonne ne coûte pas, et lorsqu'elle coûte, il consomme un caractère sans jamais revenir sur son choix. Résultat mesuré : il perd sur `197` paires sur `200`, écart médian `14`, écart maximal `29`. Une récurrence qui compare trois origines n'est donc pas une élégance de manuel.
- **Le contrôle privé de son jeu de score.** On donne à la bibliothèque une pénalité de brèche deux fois plus chère, sans toucher au calcul. Les désaccords passent de `0` à `200` sur `200`, pour un écart moyen de `5,37` points. Un zéro qui ne peut pas devenir un autre nombre ne mesurait rien.
- **L'extension locale au-delà du motif.** Le meilleur alignement local vaut `9` alors que le motif planté, seul, vaudrait `8` : prolonger une identité de part et d'autre rapporte encore. Le fragment retrouvé n'est donc pas égal au motif, il le contient — et le carnet vérifie la contenance, pas l'égalité. Un algorithme local ne dit pas « voici le motif », il dit « voici la meilleure fenêtre ».

### Ce que le carnet n'établit pas

Le corpus est synthétique et petit : 200 paires d'ADN de longueur 8 à 20, dix paires protéiques dans l'exercice 3. L'accord mesuré ne vaut pas équivalence sur des séquences de plusieurs milliers de caractères, où les implémentations optimisées en mémoire peuvent diverger, ni sur des alphabets étendus.

La pénalité de brèche est **linéaire** — une brèche de longueur $k$ coûte $k$ fois le prix d'une colonne. C'est le modèle le plus simple et le plus éloigné de la pratique courante, qui facture l'ouverture plus cher que l'extension ; le carnet le dit, et l'exercice 1 est là pour mesurer ce que le modèle affine déplace.

Le carnet ne calcule aucune significativité : un score de `12` ne dit rien de la probabilité qu'il apparaisse au hasard entre deux séquences sans parenté. Il ne justifie pas non plus le choix des nombres `+1`, `-1`, `-1` — ils sont posés pour que le contrôle porte sur l'algorithme.

## Installation — pratique, tous niveaux

Le carnet tourne sur le noyau `python3`, sans GPU. Il est reproductible : la graine du corpus est fixée (`20261127`), donc chaque exécution rejoue les mêmes paires et les mêmes nombres.

```bash
python -m pip install jupyterlab ipykernel numpy matplotlib biopython
jupyter lab MyIA.AI.Notebooks/BioMedecine/Sequences/Sequences-01-Alignement-Programmation-Dynamique-Python.ipynb
```

L'exécution complète prend quelques secondes. L'environnement commun aux sous-séries est décrit dans la section « Installation » de [Bio & Médecine](../README.md).

## Pour aller plus loin — Recherche

**Extensions prévues.** Les matrices de poids positionnelles et l'inférence d'un motif à partir de séquences qui le contiennent. Les heuristiques de graines, qui échangent l'optimum contre la vitesse en ne visitant qu'une partie de la table. Les profils HMM, qui remplacent une matrice fixe par une distribution par position.

**Questions ouvertes.** À partir de quelle longueur une implémentation exacte cesse-t-elle d'être praticable, et quel compromis une heuristique de graines fait-elle perdre exactement ? Un profil HMM et une matrice de substitution encodent-ils la même information sur un motif, ou la seconde ne garde-t-elle que la moyenne de la première ?

**Ponts.** [GameTheory/Dynamics](../../GameTheory/Dynamics/README.md) porte la dynamique des réplicateurs, mécanique de sélection dont les matrices de substitution sont une photographie statistique. [NLP/05-HMM-Viterbi](../../NLP/05-HMM-Viterbi.ipynb) traite le décodage de Viterbi dont dépendent les profils. Le pli **Évolution** de cette série reconstruira des arbres à partir des alignements écrits ici.

## Ressources — tous niveaux

- Algorithmes : Needleman-Wunsch (1970), Smith-Waterman (1981) ; matrice BLOSUM62 (Henikoff & Henikoff, 1992), chargée depuis Biopython sans être recalculée.
- Contrôle : `Bio.Align.PairwiseAligner`, dont le code ne partage rien avec celui du carnet.
- [Bio & Médecine](../README.md) : présentation de la série, contrat de méthode, plis à venir.
- [Catalogue du dépôt](../../../COURSE_CATALOG.generated.md) : inventaire exhaustif avec noyaux et statuts.

[↑ Bio & Médecine](../README.md) · [Catalogue du dépôt](../../../COURSE_CATALOG.generated.md)
