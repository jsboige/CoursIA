# GOL — Le Jeu de la Vie comme modèle de calcul

Sous-série de la série Lean (SymbolicAI) consacrée au Jeu de la Vie de Conway,
dans la filière « automates cellulaires et calcul » de l'EPIC #1647 (hommages à Conway).
Elle regroupe les carnets qui étaient numérotés `Lean-16b` à `Lean-16j` avant la
réorganisation #20204, puis les deux carnets Life de la série GameTheory (`20d`, `20e` —
Loi II et perplexité structurelle), en une marche d'escalier autonome entre `Lean-16` (l'homme
et l'œuvre) et les ponts vers le libre arbitre et la théorie des nœuds ; FRACTRAN,
l'autre invention computationnelle de Conway, amène la marche à GOL-10, et la
face **mesurée** de l'émergence (« vie dans la vie ») la prolonge en GOL-11.

**Le geste de la sous-série** : faire gravir au Jeu de la Vie « l'échelle des
témoins » — de la règle elle-même jusqu'à la correction d'un algorithme Hashlife
prouvée en Lean — en gardant chaque barreau exécutable : un carnet, un moteur réel
(kernel natif Lean, Golly, RLE, hashlife Python), zéro substitution dégradée.

## Parcours principal

| # | Notebook | Ce qu'on y apprend | Outil |
|---|----------|----------------|-------|
| GOL-01 | [GOL-01-Regles-Vie-Lean](GOL-01-Regles-Vie-Lean.ipynb) | La règle B3/S23 comme fonction de la grille, puis sa preuve en Lean — la source unique de vérité de la sous-série | `python3-lean` |
| GOL-02 | [GOL-02-Golly](GOL-02-Golly.ipynb) | Les trois piliers de Conway en images : formats RLE et explorations, avec Golly comme compagnon (HashLife présenté, non exécuté) | `python3` + Golly |
| GOL-03 | [GOL-03-Vie-Native](GOL-03-Vie-Native.ipynb) | Le Jeu de la Vie **calculé par le noyau Lean** : représentation de la grille, règle, moteur d'évolution, configurations stables et oscillateurs | `lean4-wsl` |
| GOL-04 | [GOL-04-Canons](GOL-04-Canons.ipynb) | Reconnaître un motif par sa période et son transitoire, puis le générer par recherche bornée — le canon comme témoin vérifié | `python3` |
| GOL-05 | [GOL-05-Pattern-Tour](GOL-05-Pattern-Tour.ipynb) | La tournée des motifs : parcourir les déclarations du lake `conway_lean` et les interroger une à une | `lean4-wsl` |
| GOL-06 | [GOL-06-Translateur-Life](GOL-06-Translateur-Life.ipynb) | Synthétiser un translateur de Life sur grille bornée — la construction elle-même, sans son certificat | `python3-lean` |
| GOL-07 | [GOL-07-Hashlife-Correctness](GOL-07-Hashlife-Correctness.ipynb) | La correction de Hashlife **comme théorème Lean** : l'algorithme et sa preuve dans le même carnet | `lean4-wsl` |
| GOL-08 | [GOL-08-Loi-II-Translateur-Life](GOL-08-Loi-II-Translateur-Life.ipynb) | La Loi II sur substrat Life : synthétiser un translateur, et scopé son certificat d'impossibilité — [approfondissement GOL-08b](#approfondissements) | `python3` |
| GOL-09 | [GOL-09-Perplexite-Structurelle-Hashlife](GOL-09-Perplexite-Structurelle-Hashlife.ipynb) | La perplexité structurelle Hashlife, mesure de la taille comprimée des trajectoires et du coût en temps (exposant α HashLife) | `python3` |
| GOL-10 | [GOL-10-Fractran](GOL-10-Fractran.ipynb) | Calculer avec des fractions : registres premiers, Fibonacci, Collatz et compilation de machines de Minsky | `python3` |
| GOL-11 | [GOL-11-Vie-dans-la-vie](GOL-11-Vie-dans-la-vie.ipynb) | L'émergence **mesurée** : la chute du bruit d'un champ aléatoire vers un régime vivant persistant et reproductible | `python3` |

## Comment lire ce README

La marche est une **échelle des témoins** : GOL-01 pose la règle, GOL-02 et GOL-03 la font tourner (en images d'un côté, au noyau Lean de l'autre), GOL-04 à GOL-06 montrent ce que l'on sait reconnaître, générer et translater, GOL-07 monte d'un cran en prouvant la correction de l'algorithme, GOL-08 et son approfondissement scellent l'impossibilité, GOL-09 mesure le coût, GOL-10 change de formalisme (FRACTRAN), GOL-11 mesure l'émergence.

Trois portes d'entrée :

- **l'image** — GOL-02 seul, avec Golly, pour voir les trois piliers ;
- **le noyau** — GOL-03 puis GOL-05, pour qui veut la règle et les motifs *résolus* par Lean ;
- **la preuve d'algorithme** — GOL-07 (correction de Hashlife) est le sommet de l'échelle, et se lit après GOL-01 et GOL-03.

GOL-08 s'adresse à qui veut la Loi II ; son prolongement GOL-08b (le certificat d'impossibilité en théorèmes du lac) est listé plus bas, sous « Approfondissements ».

Les voisins hors sous-série : [Lean-16](../Lean-16-Conway-Homme-et-Oeuvre-Lean-Python.ipynb)
(l'homme et l'œuvre, en amont), [Lean-16b](../Lean-16b-Conway-FRACTRAN-Lean-Native.ipynb)
(FRACTRAN sur kernel Lean natif, dont GOL-10 est le compagnon Python) et [Lean-13e](../Lean-13e-Conway-Theoreme-Libre-Arbitre-Lean-Python.ipynb) (libre arbitre),
puis [Lean-17](../Lean-17-Conway-Bridge-to-Knots-Python.ipynb) (pont vers les nœuds).
Côté GameTheory, le chemin minimal (escalier Metajeux) précède GOL-08 :
[Metajeux-04](../../../GameTheory/Metajeux/Metajeux-04-Chemin-Minimal-Robinson-Goforth-Python.ipynb).
Le carnet d'escalier qui survole la sous-série est
[Lean-39-Capstone-GOL](../Lean-39-Capstone-GOL.ipynb).

## Approfondissements

### Autour de GOL-08 — formaliser le certificat

| Extension | Notebook | Ce qu'elle ajoute | Prérequis en plus | Outil |
|-----------|----------|------------------|-------------------|-------|
| GOL-08b | [GOL-08b-Certificat-Translateur-Lean](GOL-08b-Certificat-Translateur-Lean.ipynb) | Le variant `-b` annoncé par GOL-08 : témoin, impossibilité et frontière de famille en théorèmes du lake (`Conway.Life.Translateur`) | [GOL-08](GOL-08-Loi-II-Translateur-Life.ipynb) : synthèse Python et certificat d'impossibilité scopé à une famille finie | `lean4-wsl` |

## Conventions

- Documentation primaire en **français** ; code en français ou en anglais.
- Chaque carnet porte **au moins trois exercices** non résolus, stubs sans erreur
  volontaire (règle C.1, #2161) : `pass`, `return None` ou message — jamais
  `raise NotImplementedError`.
- Les carnets sont committés **avec leurs sorties** (règle C.2) : une cellule
  modifiée est re-exécutée avant commit.
- Le versant preuves vit dans le lake [`conway_lean`](conway_lean/) — les
  carnets invoquent ses modules, ils ne les réimplémentent pas.
