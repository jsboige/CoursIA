# Carte de l'écosystème Rust — correspondance bibliothèques → crates, série par série

> REFERENCE — vivante — dernière révision 2026-11-14
>
> **Provenance** : [Epic #26510](https://github.com/jsboige/CoursIA/issues/26510) (Parité Rust), **Pli 1** [#26513](https://github.com/jsboige/CoursIA/issues/26513). Ce document est la table de correspondance que le pli 1 doit livrer. Il rend possibles le choix des carnets (pli 2) et le gabarit de portage (pli 3).

## Ce que ce document établit

Une fois les bibliothèques cibles choisies et les écueils de traduction connus, porter un carnet coûte nettement moins que l'écrire la première fois (leçon des marathons de parité Python/C# #4956, #26070). Rust s'ajoute à ce geste. Cette table met en regard, **série par série** :

- les bibliothèques Python et C# que les carnets **utilisent vraiment** (mesurées dans les carnets, jamais supposées) ;
- le crate Rust cible ;
- le verdict : **natif** / **pont** (pyo3, j4rs, autre) / **implémentation brute** / **hors périmètre** ;
- la qualification de licence et les écueils de traduction.

## Méthode — partir du dépôt, pas de l'écosystème

On cherche d'abord quelles bibliothèques les carnets utilisent **vraiment** (imports Python, `#r "nuget:"` C#), puis leur équivalent Rust. Un comptage par série se fait **par commande, citée ici** :

```bash
python scripts/notebook_tools/rust_ecosystem_census.py            # tout le corpus
python scripts/notebook_tools/rust_ecosystem_census.py --series <Série>
python scripts/notebook_tools/rust_ecosystem_census.py --json     # sortie machine
```

L'organe [rust_ecosystem_census.py](../../scripts/notebook_tools/rust_ecosystem_census.py) :

- prend le corpus des carnets **suivis par git** sous `MyIA.AI.Notebooks/`, hors sorties `_output` et jumeaux de traduction `_en` (la même base que l'inventaire de l'Epic : 1 795 carnets) ;
- extrait, par cellule de code, les modules Python de niveau supérieur importés (`import X`, `from X import …`) et les paquets NuGet chargés (`#r "nuget: Paquet"`);
- **sépae les imports en quatre bacs** : stdlib (via `sys.stdlib_module_names`, la liste du langage), **tiers** (ce qui a un équivalent crate à envisager), **helpers du dépôt** (tiges des `.py`/`.lean` suivis par git — jamais une liste en dur), et **imports Lean** (`Mathlib` et modules de série dans les carnets Python/Lean mixtes) ;
- compte **par carnet distinct** (un module compté une fois par carnet, même importé dans plusieurs cellules), **par série** (répertoire de premier niveau).

> **Reserve de lecture** : la séparation tiers / local est structurelle. Un package PyPI qui porterait le **même nom** qu'un module local du dépôt serait compté local (faux négatif tiers). C'est le seul angle mort connu de l'organe ; il est négligeable au corpus (aucun tel conflit mesuré sur les bibliothèques significatives) et se verifie série par serie au pli 2.

## Le recensement mesuré

Synthèse par série (corpus du 2026-11-14, `origin/main` = `24e8257832c`). Les « Top » sont les trois bibliothèques les plus répandues. Le détail complet par série est produit par l'organe ci-dessus.

| Série | Carnets | Py (3e partie) | C# (nuget) | Top Python | Top C# |
|---|---:|---:|---:|---|---|
| SymbolicAI | 411 | 241 | 47 | `matplotlib`(82), `numpy`(65), `jpype`(27) | `IKVM`(19), `IKVM.Image`(17), `dotNetRDF`(15) |
| GenAI | 310 | 252 | 14 | `numpy`(140), `dotenv`(132), `matplotlib`(120) | `Microsoft.SemanticKernel`(3), `OpenTelemetry`(2) |
| QuantConnect | 237 | 230 | 0 | `numpy`(214), `pandas`(192), `matplotlib`(166) | — |
| Search | 171 | 88 | 56 | `numpy`(69), `matplotlib`(68), `ortools`(33) | `Google.OrTools`(20), `pythonnet`(11), `SkiaSharp`(11) |
| ML | 143 | 120 | 13 | `numpy`(106), `matplotlib`(81), `sklearn`(56) | `Microsoft.ML`(11), `PythonNet`(3), `MathNet.Numerics`(2) |
| GameTheory | 142 | 84 | 12 | `numpy`(71), `matplotlib`(48), `scipy`(17) | `pythonnet`(6), `MathNet.Numerics`(2), `QuikGraph`(2) |
| IIT | 114 | 109 | 0 | `numpy`(102), `ict`(96), `matplotlib`(77) | — |
| Probas | 93 | 59 | 29 | `numpy`(58), `matplotlib`(49), `pymc`(32) | `Microsoft.ML.Probabilistic`(28) |
| RL | 40 | 38 | 0 | `numpy`(35), `matplotlib`(30), `torch`(23) | — |
| Sudoku | 39 | 19 | 12 | `numpy`(12), `matplotlib`(8), `mealpy`(2) | `GeneticSharp`(3), `pythonnet`(2), `Google.OrTools`(2) |
| Complexity | 27 | 17 | 0 | `numpy`(13), `matplotlib`(9), `pandas`(1) | — |
| NLP | 13 | 11 | 1 | `matplotlib`(8), `numpy`(7), `pandas`(3) | `pythonnet`(1) |
| Physique | 12 | 12 | 0 | `numpy`(9), `matplotlib`(6), `mpmath`(5) | — |
| Compression | 11 | 7 | 0 | `matplotlib`(7), `numpy`(3), `lz4`(1) | — |
| CaseStudies | 6 | 6 | 0 | `numpy`(6), `pandas`(4), `seaborn`(4) | — |

## Table de correspondance, série par série

**Statut du pli (honnête).** La colonne « bibliothèque en usage » est **mesurée** par l'organe (ci-dessus). Les colonnes « crate Rust », « verdict » et, dans la suite, « version / date / licence / maturité » sont des **verdicts provisoires** issus du relevé préliminaire de l'Epic (14/11, crates.io / docs.rs / dépôts amont) : ils **orientent** le travail, ils ne le remplacent pas. Chaque ligne se **revérifie à la source** (version + date de publication + licence lues au jour du relevé) **famille par famille, au pli 2** — c'est le travail de suivi de cette table, et la raison pour laquelle elle part en plusieurs PRs (une par grande famille).

Le noyau commun à tous les carnets Rust : **evcxr** v0.22.0 (publié 2025-08-18, MIT/Apache-2.0) — le seul noyau Jupyter Rust maintenu. `:dep crate = "x.y"` en tête de carnet (un `:dep` ajouté plus bas recompile tout et efface les variables typées). Affichage riche via `evcxr_display` (HTML/SVG) ; `plotters` a une feature `evcxr`. **Papermill n'a pas de traducteur Rust** (pli 0 tranche le paramétrage).

### Search

| Bibliothèque en usage | Lang. | Crate Rust candidat | Verdict provisoire |
|---|---|---|---|
| `numpy` (69) | Py | `ndarray`, `nalgebra` | natif |
| `matplotlib` (68) | Py | `plotters` (feature `evcxr`) | natif |
| `pandas` (25) | Py | `polars` | natif |
| `ortools` (33), `Google.OrTools` (20) | Py/C# | `highs` (MILP), `cp_sat` (CP-SAT) | natif partiel / implémentation brute |
| `networkx` (10) | Py | `petgraph` | natif |
| `mealpy` (10) | Py | `genetic_algorithm` | natif |
| `z3` (3), `Microsoft.Z3` (2) | Py/C# | `z3` | **natif — le point le plus fort** |
| `pychoco`, `constraint`, `pysat` (CP/SAT) | Py | `cp_sat`, `rustsat` | natif |
| `cvxpy` (3) | Py | — | implémentation brute |
| `GeneticSharp` (3) | C# | `genetic_algorithm` | natif |
| `QuikGraph` (5) | C# | `petgraph` | natif |
| `open_spiel` / `pyspiel` (2) | Py | — | hors périmètre (cf. GameTheory) |

### Sudoku

| Bibliothèque en usage | Lang. | Crate Rust candidat | Verdict provisoire |
|---|---|---|---|
| `numpy` (12), `matplotlib` (8) | Py | `ndarray`, `plotters` | natif |
| `mealpy` (2), `pygad` (1), `simanneal` (1) | Py | `genetic_algorithm` | natif |
| `ortools` (2), `z3` (2), `Google.OrTools` (2), `Microsoft.Z3` (1) | Py/C# | `highs`, `z3` | natif |
| `jax` (1), `numpyro` (1), `torch` (1) | Py | `burn`, `candle`, `tch` | natif |
| `GeneticSharp` (3) | C# | `genetic_algorithm` | natif |
| `DlxLib` (1) | C# | `dlx` | natif |

### Complexity

| Bibliothèque en usage | Lang. | Crate Rust candidat | Verdict provisoire |
|---|---|---|---|
| `numpy` (13), `matplotlib` (9) | Py | `ndarray`, `plotters` | natif |
| automates / hiérarchies (cœur de la série) | Py | — | **implémentation brute** (la valeur pédagogique de Rust : preuve de terminaison, sûreté mémoire) |

### SymbolicAI

| Bibliothèque en usage | Lang. | Crate Rust candidat | Verdict provisoire |
|---|---|---|---|
| `jpype` (27) — Tweety par JPype | Py | `j4rs` (pont JVM vers Tweety) | **pont, avec réserves** |
| `z3` (27), `Microsoft.Z3` (6) | Py/C# | `z3` | **natif — le point le plus fort** |
| `rdflib` (18), `owlready2` (4), `owlrl` (4), `pyshacl` (4), `SPARQLWrapper` (1), `dotNetRDF` (15) | Py/C# | `oxigraph`, `sophia`, `horned-owl` (**LGPL-3.0**) | natif (licence LGPL à juger au cas par cas) |
| `clingo` (3), `pysat` (3), `unified_planning` (12) | Py | `rustsat`, `pddl`, `miniplan` (**EUPL-1.2**) | natif avec réserves (EUPL) |
| `argumentation_lib` (18) | Py | `argumentation` (Dung, ASPIC+ — jeune) | natif avec réserves |
| `web3` (16), `solcx` (16), `eth_*` | Py | — | **hors périmètre initial** (blockchain) |
| `IKVM` (19) | C# | `j4rs` (pont JVM) | pont |
| `Mathlib` (9, Lean) | Lean | — | hors périmètre Rust (le Lean reste Lean) |

### Probas

| Bibliothèque en usage | Lang. | Crate Rust candidat | Verdict provisoire |
|---|---|---|---|
| `pymc` (32), `pytensor` (17), `arviz` (32), `pyro` (1) | Py | `statrs`, `rv` ; **aucun PPL mûr** | **pont ou implémentation brute** |
| `Microsoft.ML.Probabilistic` (28, Infer.NET) | C# | — (aucun équivalent) | **implémentation brute** |
| `dowhy` (8) | Py | — | hors périmètre |

### ML

| Bibliothèque en usage | Lang. | Crate Rust candidat | Verdict provisoire |
|---|---|---|---|
| `numpy` (106), `matplotlib` (81) | Py | `ndarray`, `plotters` | natif |
| `sklearn` (56) | Py | `linfa`, `smartcore` | natif (sur une sélection de sujets) |
| `torch` (47), `torchvision` (19) | Py | `burn`, `candle`, `tch` | natif |
| `ultralytics` (5), `cv2` (4) | Py | `image`, `candle` | natif partiel |
| `xgboost` (2) | Py | — | implémentation brute |
| `Microsoft.ML` (11) | C# | — | hors périmètre (ML.NET) |
| `MathNet.Numerics` (2) | C# | `nalgebra` | natif |

### GameTheory

| Bibliothèque en usage | Lang. | Crate Rust candidat | Verdict provisoire |
|---|---|---|---|
| `nashpy` (10) | Py | `mccfr` ; **pas d'équivalent de nashpy** | **implémentation brute / pont** |
| `pyspiel` (6), `open_spiel` (3) | Py | — | hors périmètre |
| `z3` (6) | Py | `z3` | natif |
| `networkx` (6), `QuikGraph` (2) | Py/C# | `petgraph` | natif |

### Hors périmètre initial (motivé par le recensement)

| Série | Pourquoi Rust n'apporte rien ici |
|---|---|
| **QuantConnect** (237, 100 % Python : `numpy` 214, `pandas` 192) | plateforme C#/Python uniquement ; pas de crate de la plateforme |
| **GenAI** (310, écosystème Python : `openai`, `semantic_kernel`, `langchain_*`) | écosystème Python ; seuls les **clients LLM** ont un natif (`async-openai`, `rig-core`, `llama-cpp-2`) |
| **IIT** (114, `ict`/`pyphi` 96) | rien de trouvé en Rust pour la théorie de l'information intégrée |
| **RL** (40, `torch` 23) | aucune bibliothèque RL mûre en Rust |
| **PPL bayésien** (Probas) | aucun PPL mûr — voir plus haut |

## Qualification de licence

Règle du pli 1 (reprise du mandat) : **MIT et Apache-2.0 passent**. **LGPL, MPL et EUPL se jugent au cas par cas**, selon l'usage (dépendance d'un carnet vs outil de la flotte). **Toute clause additionnelle** à une licence standard se lit **en entier** avant adoption et se recopie dans la table.

Crates candidats touchés par une licence non libre sous cette règle :

| Crate | Licence | Conséquence |
|---|---|---|
| `horned-owl` (OWL) | LGPL-3.0 | à juger au cas par cas |
| `miniplan` (PDDL) | EUPL-1.2 | à juger au cas par cas |
| dépôts `franken_numpy` / `frankenscipy` / `franken_networkx` (J. Emanuel) | MIT + **clause additionnelle** | **adoption suspendue** — la clause se lit en entier avant adoption, arbitrage mainteneur |

**Un crate sous une clause additionnelle (ou LGPL/MPL/EUPL non jugé) reste « adoption suspendue » et part au registre des questions user** : cette lane n'arbitre pas l'adoption de licence.

## Ponts

Pour chaque domaine sans crate mûr, dire si un pont tient et si une implémentation brute est raisonnable :

- **pyo3** (pont Python) : **fragile dans evcxr** — un import de module Python a déjà échoué depuis une cellule evcxr alors qu'il passait sous `cargo run` ([pyo3#2000](https://github.com/PyO3/pyo3/issues/2000), ticket fermé depuis). **Re tester le pont pyo3 dans evcxr avant de le recommander** (pli 0 / pli 2).
- **j4rs** (pont JVM) : pour Tweety (`jpype`/`IKVM` → Tweety en Rust). C'est le seul chemin vers Tweety sans réécrire.
- **z3 natif** : `z3` en Rust est l'organe natif — pas de pont.

## Écueils de traduction par domaine

Ce qui change entre Python, C# et Rust, et que le carnet **doit enseigner, pas cacher** (matière des interprétations des jumeaux Rust, d'après l'expérience de portage de Khaja Hussain) :

- **propriété et emprunts** dans les structures de graphe (`petgraph`) — l'état partagé devient explicite (`Arc<Mutex<HashMap>>`) ; la lutte avec le vérificateur d'emprunts dure quelques semaines, puis laisse un meilleur modèle mental ;
- **génériques numériques** sans surcharge d'opérateurs implicite — les opérateurs numériques ne sont pas surchargés par défaut en Rust ;
- **graines aléatoires et reproductibilité** — l'aléatoire est un type (`StdRng`), la graine se gère explicitement, graine par graine ;
- **`Result` à la place des exceptions** — `Result` interdit l'exception d'arrière-plan avalée en silence.

## Sources consultées

- **L'organe** : [rust_ecosystem_census.py](../../scripts/notebook_tools/rust_ecosystem_census.py) — le recensement est reproducible par la commande citée en tête (corpus du 2026-11-14, `origin/main` = `24e8257832c`).
- **Le relevé préliminaire par domaine** : body de l'[Epic #26510](https://github.com/jsboige/CoursIA/issues/26510) (crates.io, docs.rs, dépôts amont, relevé du 14/11).
- **J. Emanuel (Dicklesworthstone)** — [github.com/Dicklesworthstone](https://github.com/Dicklesworthstone) : `franken_numpy`, `frankenscipy`, `franken_networkx` (harnais de conformité différentielle — la forme que doit prendre la garde de parité à trois langues, pli 3).
- **Khaja Hussain**, *What Switching From C# to Rust Actually Taught Me* (dev.to, 2026-07-11) — copie archivée : `G:\Mon Drive\MyIA\IA\Bibliographie IA\Teaching Materials\2026 - Khaja Hussain - What Switching From C# to Rust Actually Taught Me.html`.
- **pyo3#2000** — [github.com/PyO3/pyo3/issues/2000](https://github.com/PyO3/pyo3/issues/2000) (fragilité du pont dans evcxr).

## Ce qui reste (suivi du pli 1, par famille)

Cette première tranche livre le **socle mesuré** (le recensement, ci-dessus) et la **table de correspondance orientée** (crates candidats + verdicts provisoires). Il reste, **famille par famille** et porteur par l'issue du pli 2 :

1. **revérifier chaque crate à la source** — version, date de publication, licence, maturité (production / utilisable / expérimental / abandonné) lues au jour du relevé, pour chaque ligne de la table ;
2. **compléter les verbatims de licence** des crates sous LGPL/MPL/EUPL ou clause additionnelle ;
3. **re tester les ponts** (pyo3 dans evcxr, j4rs) et qualifier le natif `z3` ;
4. **lister les sources consultées par famille** avec URL et date.

🤖 Generated with [Claude Code](https://claude.com/claude-code)
