---
pagetitle: "Calcul scientifique — forme close, mesure, preuve"
---

[↑ Parcours de notebooks](../README.md)

Un problème de calcul se traite rarement par une seule voie. Une équation peut avoir une **forme close**, obtenue et contrôlée symboliquement ; la même équation peut être **résolue numériquement**, et l'écart à la forme close mesuré ; et la question de savoir si la solution est unique, ou si elle reste nulle quand elle part de zéro, peut être **démontrée** — ailleurs, dans un assistant de preuve. Ces trois voies ne répondent pas à la même question, et les confondre est la faute la plus courante.

Cette série prend un problème par carnet et le traite par les trois voies quand elles existent. Elle est **additive** : elle n'absorbe aucune série existante, elle ouvre un axe que les séries de physique et de mathématiques appliquées laissent implicite — la frontière entre ce qui est calculé, ce qui est mesuré et ce qui est prouvé.

## Objectifs d'apprentissage

1. Obtenir une forme close par un calcul symbolique, puis la **contrôler par substitution** au lieu de la croire.
2. Mesurer l'erreur d'un solveur numérique contre cette forme close sur plusieurs tolérances, et reconnaître le réglage grossier qui ne suffit pas.
3. Distinguer ce qu'un pas de temps garantit (**stabilité**) de ce qu'il ne garantit pas (**précision**).
4. Lire un énoncé formel qui répond à la même question, et nommer ce qu'il certifie au-delà de toute tolérance.
5. Écrire, lacune par lacune, ce qu'un carnet établit et ce qu'il ne fait que vérifier sur des cas.

## Comment lire ce README — Découverte

Le principe [« Choisir sa vitesse de lecture »](https://github.com/jsboige/CoursIA#choisir-sa-vitesse-de-lecture) distingue entrée dans le sujet, approfondissements et recherche.

- **Vous découvrez** : le carnet du parcours principal se lit avec le calcul différentiel du secondaire et Python de base. Il part d'une équation d'une ligne, en donne la solution exacte, puis mesure.
- **Vous approfondissez** : la partie sur les tolérances et celle sur la preuve formelle demandent de distinguer trois statuts d'affirmation ; les exercices font manipuler les paramètres.
- **Vous explorez des fondements** : la question « le solveur a-t-il trouvé *la* solution ou *une* solution ? » est posée en fin de carnet, et elle ne se règle pas en raffinant un maillage.

Aucune séquence n'est imposée avec les autres séries. Les carnets de physique numérique et de calcul symbolique du dépôt restent les voies d'approfondissement naturelles.

## Parcours principal — du symbole au nombre, puis à la preuve

| # | Notebook | Ce qu'on y apprend | Public | Pour approfondir |
|---|---|---|---|---|
| 1 | [Équation différentielle linéaire](Calcul-01-Equation-Differentielle-Lineaire-Python.ipynb) | Forme close obtenue avec SymPy, contrôle par substitution et témoin négatif, erreur de SciPy mesurée sur cinq tolérances, seuil de stabilité d'un schéma explicite, énoncé Lean sur la même équation | Licence | Les carnets de [Physique/Numerique](../Physique/Numerique/README.md) pour la discrétisation d'équations aux dérivées partielles |

## Approfondissements

Le pilote de la série est seul : il n'y a pas encore de branche à relier. Les approfondissements s'ouvriront quand la série couvrira d'autres problèmes — systèmes linéaires, quadrature, optimisation — et seront listés ici avec leurs liens vers les séries voisines.

En attendant, deux lectures complètent le carnet :

- la sous-série [Physique/Numerique](../Physique/Numerique/README.md) traite la discrétisation d'équations aux dérivées partielles et la mesure d'un ordre de convergence ;
- la série [ML/learning_theory_lean](../ML/learning_theory_lean/README.md) porte les énoncés formels du dépôt, dont celui que la dernière partie du carnet cite ; la sous-série [SymbolicAI/Lean](../SymbolicAI/Lean/README.md) apprend à les lire et à en écrire.

## Pas de capstone

Pas de capstone : la série ne compte qu'un carnet, un carnet de synthèse n'aurait rien à consommer.

## Installation — pratique, tous niveaux

Depuis la racine du dépôt :

```bash
python -m venv .venv-calcul
source .venv-calcul/bin/activate
python -m pip install jupyterlab ipykernel numpy scipy sympy matplotlib
python -m ipykernel install --user --name coursia-calcul --display-name "Python — Calcul scientifique"
jupyter lab MyIA.AI.Notebooks/CalculScientifique/Calcul-01-Equation-Differentielle-Lineaire-Python.ipynb
```

Sous Windows, activer l'environnement avec `.\.venv-calcul\Scripts\Activate.ps1`. Le carnet tourne sur le noyau `python3`, sans GPU, et il est livré avec ses sorties. Aucun tirage aléatoire n'y entre : deux exécutions rejouent les mêmes nombres.

## Pour aller plus loin — Recherche

Deux questions restent ouvertes après le carnet, et elles sont de nature différente. La première est numérique : à partir de quel rapport entre le pas et le coefficient de perte un schéma explicite cesse-t-il d'être utilisable, et comment un solveur adaptatif paie-t-il ce coût ? La seconde est formelle : l'énoncé Lean cité certifie une conséquence qualitative de l'équation ; la forme close, elle, n'est pas dérivée dans l'assistant de preuve. Écrire cette dérivation — ou montrer qu'elle n'apporte rien — est un grain à part entière.

Les carnets de [Physique](../Physique/README.md) montrent la même séparation sur d'autres objets : identités symboliques d'un côté, mesures de convergence de l'autre.

## Ressources

- Documentation SymPy : `sympy.dsolve` pour la résolution, `sympy.simplify` pour le contrôle par substitution.
- Documentation SciPy : `scipy.integrate.solve_ivp`, contrôle d'erreur par `rtol` et `atol`, et les méthodes à pas fixe.
- Le fichier Lean cité dans la dernière partie : [EffectiveTheory/GrokkingLemmas.lean](../ML/learning_theory_lean/EffectiveTheory/GrokkingLemmas.lean).

[↑ Parcours de notebooks](../README.md) · [Catalogue du dépôt](../../COURSE_CATALOG.generated.md)
