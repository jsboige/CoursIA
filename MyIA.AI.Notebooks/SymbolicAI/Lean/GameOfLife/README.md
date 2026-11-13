# GOL — Le Jeu de la Vie comme modèle de calcul

Sous-série de la série Lean (SymbolicAI) consacrée au Jeu de la Vie de Conway,
dans la filière « automates cellulaires et calcul » de l'EPIC #1647 (hommages à Conway).
Elle regroupe les carnets qui étaient numérotés `Lean-16b` à `Lean-16j` avant la
réorganisation #20204, puis les deux carnets Life de la série GameTheory (`20d`, `20e` —
Loi II et perplexité structurelle), en une marche d'escalier autonome entre `Lean-16` (l'homme
et l'œuvre) et les ponts vers le libre arbitre et la théorie des nœuds ; FRACTRAN,
l'autre invention computationnelle de Conway, clôt la marche en GOL-10.

**Le geste de la sous-série** : faire gravir au Jeu de la Vie « l'échelle des
témoins » — de la règle elle-même jusqu'à la correction d'un algorithme Hashlife
prouvée en Lean — en gardant chaque barreau exécutable : un carnet, un moteur réel
(kernel natif Lean, Golly, RLE, hashlife Python), zéro substitution dégradée.

## Les carnets

| # | Notebook | Ce qu'il ouvre | Outil |
|---|----------|----------------|-------|
| GOL-01 | [GOL-01-Regles-Vie-Lean](GOL-01-Regles-Vie-Lean.ipynb) | La règle B3/S23 formalisée et prouvée en Lean | `python3-lean` |
| GOL-02 | [GOL-02-Golly](GOL-02-Golly.ipynb) | Compagnon Golly : formats RLE et explorations | `python3` + Golly |
| GOL-03 | [GOL-03-Vie-Native](GOL-03-Vie-Native.ipynb) | Le Jeu de la vie calculé par le noyau Lean | `lean4-wsl` |
| GOL-04 | [GOL-04-Canons](GOL-04-Canons.ipynb) | Canons : le barreau 2 de l'échelle des témoins Life | `python3` |
| GOL-05 | [GOL-05-Pattern-Tour](GOL-05-Pattern-Tour.ipynb) | Tournée des motifs du lake `conway_lean` | `lean4-wsl` |
| GOL-06 | [GOL-06-Translateur-Life](GOL-06-Translateur-Life.ipynb) | Le translateur : de Life vers le calcul universel | `python3-lean` |
| GOL-07 | [GOL-07-Hashlife-Correctness](GOL-07-Hashlife-Correctness.ipynb) | La correction de Hashlife comme théorème Lean | `lean4-wsl` |
| GOL-08 | [GOL-08-Loi-II-Translateur-Life](GOL-08-Loi-II-Translateur-Life.ipynb) | La Loi II sur substrat Life : synthèse d'un translateur, certificat d'impossibilité scopé — [approfondissement GOL-08b](#approfondissements) | `python3` |
| GOL-09 | [GOL-09-Perplexite-Structurelle-Hashlife](GOL-09-Perplexite-Structurelle-Hashlife.ipynb) | Capstone perplexité T12 : la taille comprimée des trajectoires et le coût en temps (exposant α HashLife) comme mesures | `python3` |
| GOL-10 | [GOL-10-Fractran](GOL-10-Fractran.ipynb) | FRACTRAN en Python : registres premiers, Fibonacci, Collatz, compilation de machines de Minsky — compagnon exécutable de Lean-16b | `python3` |

## Approfondissements

### Autour de GOL-08 — formaliser le certificat

| Extension | Notebook | Ce qu'elle ajoute | Prérequis en plus | Outil |
|-----------|----------|------------------|-------------------|-------|
| GOL-08b | [GOL-08b-Certificat-Translateur-Lean](GOL-08b-Certificat-Translateur-Lean.ipynb) | Le variant `-b` annoncé par GOL-08 : témoin, impossibilité et frontière de famille en théorèmes du lake (`Conway.Life.Translateur`) | [GOL-08](GOL-08-Loi-II-Translateur-Life.ipynb) : synthèse Python et certificat d'impossibilité scopé à une famille finie | `lean4-wsl` |

Les voisins hors sous-série : [Lean-16](../Lean-16-Conway-Homme-et-Oeuvre-Lean-Python.ipynb)
(l'homme et l'œuvre, en amont), [Lean-16b](../Lean-16b-Conway-FRACTRAN-Lean-Native.ipynb)
(FRACTRAN sur kernel Lean natif, dont GOL-10 est le compagnon Python) et [Lean-13e](../Lean-13e-Conway-Theoreme-Libre-Arbitre-Lean-Python.ipynb) (libre arbitre),
puis [Lean-17](../Lean-17-Conway-Bridge-to-Knots-Python.ipynb) (pont vers les nœuds).
Côté GameTheory, le chemin minimal (escalier Metajeux) précède GOL-08 :
[Metajeux-04](../../../GameTheory/Metajeux/Metajeux-04-Chemin-Minimal-Robinson-Goforth-Python.ipynb).
Le carnet d'escalier qui survole la sous-série est
[Lean-39-Capstone-GOL](../Lean-39-Capstone-GOL.ipynb).

## Conventions

- Documentation primaire en **français** ; code en français ou en anglais.
- Chaque carnet porte **au moins trois exercices** non résolus, stubs sans erreur
  volontaire (règle C.1, #2161) : `pass`, `return None` ou message — jamais
  `raise NotImplementedError`.
- Les carnets sont committés **avec leurs sorties** (règle C.2) : une cellule
  modifiée est re-exécutée avant commit.
- Le versant preuves vit dans le lake [`conway_lean`](conway_lean/) — les
  carnets invoquent ses modules, ils ne les réimplémentent pas.
