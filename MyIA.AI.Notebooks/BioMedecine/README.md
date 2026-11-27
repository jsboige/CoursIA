---
pagetitle: "Bio & Médecine — les mathématiques et les algorithmes du vivant"
---

[↑ Parcours de notebooks](../README.md)

Comment savoir si un modèle du vivant dit quelque chose de vrai ? Un système biologique n'a pas de solution exacte écrite d'avance comme une équation de physique : il faut la construire. Cette série fait le même geste que [Physique](../Physique/README.md) — poser une question, bâtir le calcul qui y répond, puis le soumettre à une voie indépendante — sur les objets du vivant : populations, épidémies, séquences, arbres d'évolution, réseaux de gènes, neurones, structures moléculaires, mesures médicales indirectes.

Le parcours s'adresse aux étudiants en biologie, médecine, mathématiques appliquées et informatique scientifique, ainsi qu'aux enseignants qui cherchent des expériences calculables sur des données simulées à vérité connue. Python et les bases du calcul différentiel suffisent pour la première sous-série ; les autres plis indiquent leurs prérequis propres.

## Comment lire ce README — Découverte

Le principe [« Choisir sa vitesse de lecture »](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture) distingue entrée dans le sujet, approfondissements et recherche.

- **Vous découvrez** : choisissez une question dans la table du parcours principal. [Dynamiques](Dynamiques/README.md) offre la première expérience concrète — trois modèles classiques, trois contrôles indépendants, un contre-témoin qui doit échouer.
- **Vous approfondissez** : la section « Sous-séries » dit ce que contient chaque dossier et ce qui reste à écrire. Les plis sont indépendants ; les numéros des carnets décrivent une progression à l'intérieur d'un pli.
- **Vous explorez des fondements** : chaque carnet sépare par écrit ce qui est **mesuré** dans le carnet, ce qui est **cité** d'une source et ce qui reste **ouvert**. Cette séparation est le cœur de la méthode, plus encore que les résultats.

Aucune séquence n'est imposée entre les plis. Chaque README local porte la table complète de son pli et ses exercices.

## Méthode — le contrat des cinq points

Chaque carnet suit le même contrat, hérité de la série Physique :

1. **Modèle** — il énonce le modèle et ses hypothèses.
2. **Calcul** — il implémente l'algorithme, souvent à partir de zéro, pour qu'on voie ce qu'il fait.
3. **Contrôle indépendant** — il compare le résultat à une voie qui ne partage pas son code : solution analytique, invariant conservé, équation transcendante résolue séparément, bibliothèque de référence, valeur publiée.
4. **Contre-témoin** — il construit un cas où le contrôle doit échouer, pour montrer que ce contrôle sait échouer.
5. **Statut** — il distingue ce qui est **mesuré**, ce qui est **cité** et ce qui reste **ouvert**.

Deux règles s'y ajoutent :

- **Organe d'abord.** Quand le dépôt possède déjà le moteur d'une opération, le carnet l'appelle au lieu de le réécrire ; il ne recopie un moteur existant que sous la forme d'une copie pédagogique déclarée.
- **Données simulées d'abord**, à paramètres connus, pour vérifier qu'on retrouve la vérité. Les données réelles ne viennent qu'avec une provenance et une licence établies, chargées à l'exécution et jamais recopiées dans le dépôt. Aucune donnée de patient non publique.

## Parcours principal — choisir une question, de la Licence à la Recherche

| Question | Pli et premier carnet | Ce qu'on y apprend | Prérequis et public | Pour approfondir |
|---|---|---|---|---|
| Comment une population ou une épidémie évolue-t-elle ? | [Dynamiques](Dynamiques/README.md) → [Populations et épidémies](Dynamiques/Dynamiques-01-Populations-et-Epidemies-Python.ipynb) | Croissance logistique et solution exacte, Lotka-Volterra et son intégrale première, SIR avec $R_0$ et taille finale ; ordre de convergence mesuré. | Licence : Python, équations différentielles ordinaires. | L'épidémie sur réseau de contacts ([Dynamiques-02](Dynamiques/Dynamiques-02-Epidemies-sur-Reseau-Python.ipynb)), puis l'inférence des paramètres avec `Probas/PyMC/`. |
| Comment comparer et lire des séquences d'ADN ou de protéines ? | Séquences — à venir | Alignements de Needleman-Wunsch et Smith-Waterman par programmation dynamique, matrices de substitution, pénalités de brèche, matrices de poids positionnelles. | Licence : algorithmique de base, probabilités. | Les HMM de profil et l'inférence du motif planté avec `Probas/Infer/`. |
| Comment l'évolution se calcule-t-elle ? | Évolution — à venir | Hardy-Weinberg, Wright-Fisher et Moran, probabilité de fixation, coalescent, reconstruction phylogénétique, jeux évolutionnaires. | Licence : probabilités, génétique de population élémentaire. | La dynamique des réplicateurs de `GameTheory/Dynamics/`, qui est la même mécanique. |
| Comment un réseau de gènes produit-il un comportement ? | Réseaux du vivant — à venir | Action de masse, Michaelis-Menten, Hill, interrupteur bistable, répressilateur, motifs de Turing. | Licence avancée : cinétique chimique, équations différentielles. | Les motifs de réaction-diffusion de `IIT/ICT-Series/`. |
| Comment un neurone émet-il un potentiel d'action ? | Neurones — à venir | Hodgkin-Huxley, FitzHugh-Nagumo, intègre-et-tire, plan de phase et excitabilité. | Licence avancée : équations différentielles, analyse qualitative. | La réduction de FitzHugh-Nagumo confrontée au modèle complet. |
| Comment une molécule se replie-t-elle ? | Structures — à venir | Repliement d'ARN par Nussinov puis par énergie minimale, modèle HP de protéines sur réseau. | Licence avancée : algorithmique, optimisation combinatoire. | Les solveurs de contraintes de `Search/` et de `SymbolicAI/`. |
| Comment reconstruit-on une image ou une grandeur à partir de mesures indirectes ? | Mesure médicale — à venir | Transformée de Radon et rétroprojection filtrée, espace $k$ de l'IRM, pharmacocinétique compartimentaire, tests diagnostiques imparfaits, analyse de survie. | Master : algèbre linéaire, probabilités, statistique. | L'inférence bayésienne de `Probas/Infer/` pour l'état caché. |

Les plis marqués « à venir » sont décrits dans l'Epic de la série et se déploient une feuille à la fois. Ils n'apparaissent ici que pour situer la première sous-série dans un ensemble plus large ; aucun carnet n'est annoncé avant d'exister.

## Sous-séries — ce que contient chaque dossier

### Dynamiques — Licence

[Dynamiques](Dynamiques/README.md) mesure ce que trois modèles classiques du vivant disent réellement. [Dynamiques-01](Dynamiques/Dynamiques-01-Populations-et-Epidemies-Python.ipynb) traite la croissance logistique, le système proie-prédateur de Lotka-Volterra et le modèle SIR. Chacun reçoit un contrôle qui ne partage pas son code : la solution exacte de l'équation logistique, l'intégrale première conservée de Lotka-Volterra, la taille finale de l'épidémie obtenue par dichotomie sur une équation transcendante. Trois contre-témoins montrent que ces contrôles savent échouer — notamment un schéma d'Euler explicite trop grossier, qui viole l'invariant de Lotka-Volterra et sort même du domaine positif.

[Dynamiques-02](Dynamiques/Dynamiques-02-Epidemies-sur-Reseau-Python.ipynb) quitte la population homogène : le SIR y court sur un graphe de contacts, simulé par une file d'événements et jugé par la percolation statique. Le carnet mesure l'écart entre les deux voies, l'attribue au partage de l'horloge de guérison, et construit un anneau où la formule de seuil elle-même se trompe.

La sous-série s'étendra à la simulation stochastique de Gillespie comparée à l'équation déterministe, et à l'inférence des paramètres d'un modèle mécaniste.

### Les six autres plis

Séquences, Évolution, Réseaux du vivant, Neurones, Structures et Mesure médicale sont décrits dans la table du parcours principal. Leurs carnets ne sont pas encore écrits ; leurs dossiers apparaîtront avec leur première feuille, et non avant.

## Liens avec les autres séries

- **Physique** reste une série autonome, et c'est délibéré. Les deux séries se répondent par la méthode plus que par le contenu : certaines équations aux dérivées partielles de la biologie — réaction-diffusion, câble neuronal — réutilisent les schémas que [Physique/Numerique](../Physique/Numerique/README.md) mesure déjà.
- **GameTheory/Dynamics** porte la dynamique des réplicateurs, qui est la mécanique de sélection de l'évolution ; le pli Évolution y renverra plutôt que de la réécrire.
- **Probas** porte l'inférence bayésienne (`Probas/PyMC/`, `Probas/Infer/`), dont les plis Dynamiques, Séquences et Mesure médicale ont besoin.
- **IIT/ICT-Series** porte la réaction-diffusion de Gray-Scott, organe du pli Réseaux du vivant.
- **NLP** porte un HMM-Viterbi, dont le pli Séquences est proche.

## Installation — pratique, tous niveaux

Les carnets de Dynamiques tournent sur le noyau `python3`, sans GPU, et sont livrés avec leurs sorties. Dynamiques-01 demande NumPy, SciPy et Matplotlib ; Dynamiques-02 se contente de NumPy et de la bibliothèque standard (`heapq`), aucune bibliothèque de graphes n'étant employée à dessein.

Depuis la racine du dépôt :

```bash
python -m venv .venv-biomedecine
source .venv-biomedecine/bin/activate
python -m pip install jupyterlab ipykernel numpy scipy matplotlib
python -m ipykernel install --user --name coursia-biomedecine --display-name "Python — Bio & Médecine"
jupyter lab MyIA.AI.Notebooks/BioMedecine/Dynamiques/Dynamiques-01-Populations-et-Epidemies-Python.ipynb
jupyter lab MyIA.AI.Notebooks/BioMedecine/Dynamiques/Dynamiques-02-Epidemies-sur-Reseau-Python.ipynb
```

Sous Windows, activer l'environnement avec `.\.venv-biomedecine\Scripts\Activate.ps1`. Sélectionner le noyau « Python — Bio & Médecine », puis exécuter les cellules dans l'ordre. Les [commandes communes](../../docs/reference/common-commands.md) complètent l'aide à l'environnement.

Les plis à venir ajouteront leurs dépendances : `biopython` pour les alignements de référence, `networkx` pour les réseaux, `scikit-survival` pour l'analyse de survie. Aucun GPU n'est requis.

## Statut et gouvernance

- Un carnet ne se déclare livré qu'exécuté de bout en bout, avec ses sorties réelles committées.
- Les totaux de la série et du dépôt appartiennent à la régénération automatique du catalogue ; ce README ne les recopie pas.
- Les applications cliniques et les métiers du soin ne relèvent pas de cette série : elle enseigne les modèles et les algorithmes du vivant, pas un parcours métier, et ne formule aucune recommandation clinique.

[Retour aux notebooks](../README.md) · [Catalogue du dépôt](../../COURSE_CATALOG.generated.md) · [Licence](../../LICENSE)
