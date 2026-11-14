# Information quantique — tester l'intrication d'états mixtes par le calcul

[↑ Physique](../index.qmd)

Sous-série Physique de la collection [MyIA.AI.Notebooks](../../README.md). Le fil
« information quantique » fait calculer les objets opérationnels de l'intrication des
états mixtes — états de Werner, transposition partielle, témoins, canal de Choi —
sur des matrices explicites, pas sur des phrases. Chaque seuil cité (séparabilité,
distillabilité, indice de rupture d'intrication) est **retrouvé numériquement** par le
carnet avant d'être confronté à son énoncé théorique dans la source archivée ; les
nombres que les sources n'établissent pas ne sont pas attribués.

La sous-série se distingue du fil « Chaînes » voisin : Chaînes-01/02 étudient un
programme de physique-de-l'information où l'« intrication » désigne un axiome
combinatoire sur des réseaux de paires ; ici, l'intrication est celle des états
d'un système bipartite — matrices de densité, spectre de la transposition partielle,
distillation par opérations locales. Les deux emplois du mot sont explicitement
distingués dans le premier carnet, avec renvoi vers l'organe CHSH du dépôt
(Lean-13b/13c) pour l'inégalité de Bell calculée sur des corrélations.

## Comment lire ce README — découverte

Le principe [« Choisir sa vitesse de lecture »](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture) distingue parcours principal, approfondissements et prolongements de recherche.

- **Vous découvrez** : partez du parcours principal. Le carnet est unique et se lit de bout en bout — chaque section introduit une notion, la calcule, puis commente le nombre obtenu. Les prérequis réels sont l'algèbre linéaire (matrices densité, spectre, décomposition en valeurs singulières) et numpy ; aucun cours de physique quantique n'est supposé.
- **Vous approfondissez** : les trois exercices du §7 reprennent les organes du carnet (états de Werner en dimension 4, purification d'un Werner, balayage du seuil de rupture d'intrication). Ils s'exécutent sans erreur et attendent votre code.
- **Vous cherchez des prolongements** : la section « Approfondissements » indique où poursuivre — la revue Horodecki 2009 et ses questions ouvertes, les bornes de distillabilité, et les carnets Lean du dépôt sur l'inégalité de Bell.

## Parcours principal — ce que contient la sous-série

Le fil commun est un test : **une affirmation sur un état quantique doit devenir un nombre affiché par une cellule.** Les six sections suivent le même patron — un cadre court, le calcul, puis la lecture du résultat — si bien que chaque énoncé théorique arrive après le nombre qui le vérifie, jamais avant.

| # | Carnet | Ce qu'on y apprend | Public et prérequis | Pour approfondir |
|---|---|---|---|---|
| 01 | [InfoQuant-01 — Intrication : Werner, PPT, distillation, canaux à rupture d'intrication](InfoQuant-01-Intrication-Werner-PPT-Distillation-Python.ipynb) | Six notions de l'intrication des états mixtes, chacune portée par un calcul de matrices : états mixtes et purification (décomposition spectrale puis vecteur de Schmidt par SVD) ; état de Werner à deux qubits avec les valeurs propres de Peres (éq. 7) retrouvées à $10^{-6}$ près ; critère PPT avec l'exemple de Peres (éq. 15), inséparable pour tout $x > 0$, et le rappel que PPT suffit en $2 \times 2$ et $2 \times 3$ mais pas au-delà ; distillabilité — le seuil 1-distillable des Werner $d \otimes d$ dérivé en forme fermée $(3-5\lambda)/12$ pour $d = 3$, qui s'annule exactement au seuil théorique $\lambda = 3/5$ de Dür et al., et la monotonie de $\lambda_N$ vers $1/2$ ; canaux à rupture d'intrication — seuil de Choi $p \geq d/(d+1)$ vérifié en $d = 2$ et $d = 3$, indice $n(\Delta_\lambda)$ coïncidant avec la formule de Lami (éq. 34) | Algèbre linéaire (matrices densité, spectre, SVD) et numpy ; aucune théorie quantique préalable. Les notions physiques sont introduites sur place, y compris la différence entre les deux sens du mot « intrication ». | Les questions ouvertes n° 2 (tout état NPT est-il distillable ?) et n° 38 (indice PPT) de la revue Horodecki *et al.* 2009 ; l'inégalité de Bell comme témoin opérationnel, démontrée formellement dans `SymbolicAI/Lean/Lean-13b-CHSH-Tsirelson-Native.ipynb` et `Lean-13c-CHSH-Landau-Saturation.ipynb` |

## Approfondissements — lectures avancées

Les approfondissements vivent dans les carnets cités par la dernière colonne du parcours principal : la revue Horodecki *et al.* 2009 pour les deux questions ouvertes, et les carnets Lean du dépôt pour l'inégalité de Bell, que ce carnet cite sans la réimplémenter.

Deux prolongements naturels, non traités ici. D'abord la **borne 37/80** et le **seuil à trois copies en $d = 3, 4$** : mentionnés dans l'issue d'ouverture de la sous-série, ils n'ont pas été retrouvés dans les copies archivées et sont donc exclus de l'exposé plutôt que cités de mémoire. Ensuite l'**enchevêtrement lié** (*bound entanglement*) : le carnet le nomme et en donne le mécanisme (PPT $\Rightarrow$ non distillable), sans en construire d'exemple explicite — c'est le sujet du prolongement.

## Positionnement épistémique

Comme pour le fil Chaînes, chaque affirmation porte son statut : **calculé** (le carnet
produit le nombre), **démontré dans la source** (le théorème est cité avec sa référence
archivée) ou **non établi** (écarté). Le carnet ne démontre pas les théorèmes — la
suffisance de PPT en $2 \times 2$/$2 \times 3$, la non-distillabilité des états PPT,
le théorème de rupture d'intrication de Holevo-Shirokov — il les met en œuvre sur des
exemples et en vérifie les conséquences numériques. Les seuils présentés sont ceux
établis par les sources ; deux nombres mentionnés dans l'issue d'ouverture
n'ont pas été retrouvés dans les copies archivées et sont exclus de l'exposé.

Les sources sont archivées au gisement
`G:\Mon Drive\MyIA\IA\Bibliographie IA\Physics\` avant écriture, citées avec
attribution dans le carnet et sa bibliographie.

## Installation — pratique, tous niveaux

Le carnet n'utilise que `numpy`. Depuis la racine du dépôt :

```bash
python -m venv .venv
source .venv/bin/activate     # ou .venv\Scripts\activate sous Windows
pip install numpy jupyter
jupyter notebook MyIA.AI.Notebooks/Physique/InformationQuantique/
```

Le noyau attendu est `python3`, et les sorties committées (règle C.2) ont été produites sous Python 3.13. Aucun GPU n'est requis ; le carnet complet s'exécute en quelques secondes.

## Ressources

- [↑ Physique](../index.qmd) — la série mère : sous-séries, prérequis et parcours.
- [Catalogue du dépôt](../../../COURSE_CATALOG.generated.md) — inventaire exhaustif avec noyaux, besoins matériels et statuts.
- [Chaînes](../Chaines/Chaines-01-Axiome-Intrication-Constante-Structure-Fine-Python.ipynb) — l'autre emploi du mot « intrication », axiome combinatoire sur des réseaux de paires.
- [SymbolicAI](../../SymbolicAI/README.md) — la branche Lean du dépôt, dont les carnets CHSH donnent le témoin opérationnel de l'intrication.