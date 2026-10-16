# geometry_lean — companion Lean de la série Geometry

Lac companion de la série [`SymbolicAI/Lean/Geometry/`](../) : chaque notebook
Python de concept reçoit un module Lean qui formalise ce que l'algorithme
Python calcule. Le lac ne remplace pas sympy — il en formalise la sémantique.
C'est le volet B de l'EPIC #18601 ; la première marche réalise la position 05
du programme gradué #17544 (« que garantit "prouvé par Gröbner" ? »).

## Modules

| Module | Contenu | Notebook Python doublé |
|---|---|---|
| `Geometry.MidpointHypotenuse` | Théorème du milieu de l'hypoténuse : équidistance du milieu aux trois sommets, rayon = hypoténuse/2 | `Geometry-01-From-Figure-To-Equation.ipynb` (fil rouge) |
| `Geometry.FromFigureToEquation` | La traduction figure → équations : encodage 6 variables, `C₂ ≡ 0`, famille paramétrique des triangles rectangles, témoin négatif (`C′ + AC² − H = 0`), tirage biaisé, instance de Schwartz–Zippel (`4s+1` zéros, borne `d/\|S\|`) | `Geometry-01-From-Figure-To-Equation.ipynb` (protocole numérique) |
| `Geometry.WuMethod` | Ce que le test de Wu garantit : certificat idéal T1 (milieu de l'hypoténuse, `MvPolynomial`), théorème de Ceva T3 par identité maîtresse (deux directions), témoin négatif et piège des rapports dirigés réfutés | `Geometry-03-Wu-Method-Python.ipynb` |

L'escalier d'entrée de la sous-série — [`Lean-38-Capstone-Geometry-Lean-Python.ipynb`](../../Lean-38-Capstone-Geometry-Lean-Python.ipynb), carnet de la série parente — est le consommateur pédagogique de ce premier module : il part de la figure du 01, calcule avec `sympy`, puis monte jusqu'à la preuve formelle ci-dessus.

## Construire

```bash
lake exe cache get   # oleans Mathlib pré-compilées (toolchain v4.33.0)
lake build           # 0 sorry — le lac est intégralement prouvé
```

La CI
([`lean-ci-matrix.yml`](https://github.com/jsboige/CoursIA/blob/main/.github/workflows/lean-ci-matrix.yml),
entrée `geometry` du manifeste `scripts/lean/ci_lakes.json` depuis la
consolidation #13751) rejoue le build et le gate proof-integrity (axiomes)
sur chaque PR touchant le lac.

## Feuille de route

- Companion du 02 (bases de Gröbner) : interroger ce que Mathlib sait des
  idéaux et de l'appartenance (`Ideal` membership) — c'est précisément la
  question pédagogique de la position 05.
- Notebook escalier d'entrée (volet C de #18601) : figure du 01 → calcul
  sympy → montée Lean pas à pas jusqu'au premier théorème du lac.
