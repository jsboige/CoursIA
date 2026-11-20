# Information quantique — tester l'intrication d'états mixtes par le calcul

[↑ Physique](../README.md)

Un état quantique partagé entre deux systèmes est-il intriqué ? Pour un état pur, la réponse se lit sur un spectre. Pour un état mixte, elle demande des critères, et certains restent ouverts. Cette sous-série fait calculer ces critères sur des matrices explicites : états de Werner, transposition partielle, témoins de distillabilité, matrice de Choi d'un canal. Chaque seuil cité est d'abord retrouvé numériquement, puis confronté à l'énoncé de la source.

Le mot « intrication » a ici son sens habituel en information quantique : un état composé qui ne s'écrit pas comme un mélange de produits. La sous-série voisine [Chaînes](../Chaines/README.md) emploie le même mot pour un axiome combinatoire sur des paires. Le carnet commence par séparer les deux emplois. Il s'adresse à un lecteur qui connaît l'algèbre linéaire (matrices hermitiennes, spectre, valeurs singulières) et numpy ; aucun cours de physique quantique n'est supposé.

## Comment lire ce README — Découverte

Le principe [« Choisir sa vitesse de lecture »](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture) distingue le parcours principal, les approfondissements et les prolongements de recherche.

- **Vous découvrez** : lisez le carnet du parcours principal dans l'ordre. Chaque section pose un cadre court, calcule, puis commente le nombre obtenu.
- **Vous creusez** : la section « Approfondissements » décrit les deux parties les plus fines du carnet, la distillabilité et les canaux, puis les exercices.
- **Vous cherchez la recherche en cours** : « Pour aller plus loin » nomme les deux questions ouvertes que le carnet rencontre et dit ce qu'il ne démontre pas.

## Parcours principal — Licence avancée et Master

| # | Notebook | Ce qu'on y apprend | Public | Pour approfondir |
|---|---|---|---|---|
| 01 | [InfoQuant-01 — Intrication quantique : états mixtes, Werner, PPT, distillabilité](InfoQuant-01-Intrication-Werner-PPT-Distillation-Python.ipynb) | Les états mixtes et leur purification : un mélange de trois états purs a une pureté de `0.54`, et sa purification redonne l'état de départ par trace partielle. La décomposition de Schmidt, qui lit l'intrication d'un état pur sur le spectre de son état réduit. Les états de Werner, famille à un paramètre : le seuil de séparabilité, $p = 1/3$ à deux qubits, s'écrit $\lambda = 1/2$ dans la paramétrisation valable en toute dimension. Le critère PPT : la transposée partielle d'un état séparable reste positive. Les spectres calculés coïncident avec ceux publiés par Peres, et un mélange à 99 % de produit local reste détecté comme intriqué (valeur propre minimale `-0.000025`). Le critère suffit en dimensions $2 \times 2$ et $2 \times 3$, pas au-delà. | Licence avancée et Master : algèbre linéaire, numpy. Les notions physiques sont introduites sur place. | La distillabilité et les canaux à rupture d'intrication, dans le même carnet (voir « Autour de 01 »). |

## Approfondissements — Master

La sous-série n'a pas de palier lettré. Ses approfondissements sont les deux dernières parties du carnet et ses exercices.

### Autour de 01 : la distillabilité et son trou

Distiller, c'est extraire des paires presque parfaites à partir de nombreuses copies d'un état bruité, par des opérations locales. Le carnet calcule le critère sur les états de Werner. À deux qubits, tout état de Werner intriqué est distillable avec une seule copie. Le témoin n'est pourtant pas l'état qui compose le mélange : sur le singulet, la valeur d'attente reste positive pour tout $p$.

En dimension 3, un intervalle apparaît. Pour $1/2 < \lambda \leq 3/5$, l'état est intriqué mais aucun témoin à une copie n'existe. Le minimum numérique suit la forme fermée $(3 - 5\lambda)/12$, nulle au seuil `0.600000` de Dür et al. Le carnet suit ensuite le poids antisymétrique des copies successives. Parti de `0.550000`, il passe à `0.495000`, puis `0.500500` : il oscille en s'amortissant autour de $1/2$, sans dépasser sa valeur de départ sur les copies calculées. Les protocoles de distillation ne peuvent donc pas compter sur un simple effet de cumul.

### Autour de 01 : les canaux à rupture d'intrication

Un canal « casse » l'intrication quand il détruit toute intrication partagée avec un tiers. Le critère passe par la matrice de Choi du canal : le canal casse l'intrication si et seulement si cette matrice est séparable. Pour le canal dépolarisant, le carnet retrouve le seuil $p \geq d/(d+1)$ : la valeur propre minimale de la transposée partielle change de signe à `0.6667` en dimension 2 et à `0.7500` en dimension 3. Il calcule enfin l'indice de rupture, c'est-à-dire le nombre d'applications en série qui suffisent. Le calcul direct coïncide en tout point avec la formule de Lami et al. (éq. 34).

### Autour de 01 : exercices

Trois exercices reprennent les fonctions du carnet : vérifier le seuil $\lambda = 1/2$ des états de Werner en dimension 4, purifier un état de Werner à deux qubits, et balayer le seuil de rupture d'intrication du canal dépolarisant en dimension 3. Les cellules s'exécutent sans erreur tant qu'elles ne sont pas complétées.

## Installation — pratique, tous niveaux

Le carnet tourne sur le noyau `python3`. Il n'importe que `numpy` et le module `math` de la bibliothèque standard. Aucune bibliothèque de calcul quantique n'est utilisée, et aucun GPU n'est requis.

```bash
python -m pip install jupyterlab ipykernel numpy
jupyter lab MyIA.AI.Notebooks/Physique/InformationQuantique/InfoQuant-01-Intrication-Werner-PPT-Distillation-Python.ipynb
```

L'environnement commun aux sous-séries est décrit dans la section « Installation » de [Physique](../README.md).

## Pour aller plus loin — Recherche

**Ce qui est calculé, ce qui est cité.** Le carnet produit des nombres : spectres, seuils, frontières. Il ne démontre pas les théorèmes qu'il met en œuvre. La suffisance du critère PPT en petites dimensions, la non-distillabilité des états PPT et la caractérisation des canaux à rupture d'intrication sont cités avec leur référence, puis vérifiés sur des exemples.

**Deux questions ouvertes.** Le carnet les repère dans la revue de Horodecki et al. (2009). La question n° 2 : tout état dont la transposée partielle a une valeur propre négative est-il distillable ? L'intervalle $1/2 < \lambda \leq 3/5$ en dimension 3 en est le cas d'école. La question n° 38 demande si un canal dont la matrice de Choi est PPT casse toujours l'intrication quand on l'applique deux fois ; l'indice de rupture lui donne son vocabulaire.

**Ce que le carnet laisse de côté.** Il nomme l'enchevêtrement lié, ces états intriqués et non distillables, et en donne le mécanisme. Il n'en construit pas d'exemple explicite.

**Formalisations Lean.** La violation d'une inégalité de Bell est le témoin opérationnel de l'intrication. Elle est démontrée formellement dans [Lean-13b — la borne de Tsirelson](../../SymbolicAI/Lean/Lean-13b-CHSH-Tsirelson-Native.ipynb) et [Lean-13c — la saturation de Tsirelson](../../SymbolicAI/Lean/Lean-13c-CHSH-Landau-Saturation.ipynb). Le carnet les cite sans les réimplémenter ; la série est présentée dans [SymbolicAI](../../SymbolicAI/README.md).

**Ponts.** [Constructeur-01](../Constructeur/Constructeur-01-Lois-Comme-Taches-Python.ipynb) utilise une mesure d'intrication, la négativité, comme témoin de non-classicité. [Chaînes-01](../Chaines/Chaines-01-Axiome-Intrication-Constante-Structure-Fine-Python.ipynb) porte l'autre emploi du mot « intrication ».

## Ressources — tous niveaux

La bibliographie complète figure à la fin du carnet, avec les équations utilisées. Les sources principales :

- A. Peres, *Separability Criterion for Density Matrices*, 1996 — [arXiv:quant-ph/9604005](https://arxiv.org/abs/quant-ph/9604005). Critère PPT et exemples.
- W. Dür et al., *Distillability and Partial Transposition in Bipartite Systems*, 2000 — [arXiv:quant-ph/9910022](https://arxiv.org/abs/quant-ph/9910022). Seuil de distillabilité à une copie.
- R. Horodecki et al., *Quantum Entanglement*, 2009 — [arXiv:quant-ph/0702225](https://arxiv.org/abs/quant-ph/0702225). Revue : états de Werner, critère de distillabilité, questions ouvertes.
- Lami et al., *Entanglement-Breaking Indices*, 2015 — [arXiv:1411.2517](https://arxiv.org/abs/1411.2517). Seuil et indice du canal dépolarisant.

[↑ Physique](../README.md) · [Catalogue du dépôt](../../../COURSE_CATALOG.generated.md)
