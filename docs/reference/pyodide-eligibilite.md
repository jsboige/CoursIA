# Eligibilite Pyodide (JupyterLite) des carnets Python

<!-- Genere par scripts/notebook_tools/pyodide_eligibility.py -- ne pas editer a la main. -->

Perimetre : carnets Python suivis par git, hors `_output`, `_en` et `_archive`.
La famille Python se lit sur la langue declaree (`language_info.name`), le nom du
noyau ne servant que de repli : un carnet sans langue ni noyau Python n'est pas
compte -- le census ne suppose pas Python par defaut. Le compte d'une serie peut
donc etre inferieur au nombre de fichiers `.ipynb` qu'elle contient.
Census : **1488** carnets Python, **588** eligibles, **900** refuses.

Source de verite des paquets : `pyodide-lock.json` (ABI 2026_0, Python 3.14.2, wasm32, emscripten_5_0_3 ; 357 paquets),
commite avec le rapport (`docs/reference/pyodide-lock.json`), ainsi que le cache des sondes
PyPI (`docs/reference/pyodide-wheel-cache.json`) : la regeneration ci-dessous est entierement hors
reseau. Un import absent du lock et absent de la bibliotheque standard est
refuse, sauf si le cache (ou une sonde `--probe-pypi`, acces reseau explicite)
a constate une roue pure ; sans l'un ni l'autre, le refus est rendu tel quel.

Le lock commite provient du canal `dev` de Pyodide, qui avance : le bump du lock
est un geste delibere (regenerer puis committer lock, cache et rapport ensemble),
et un ecart de census entre deux regenerations s'explique d'abord par la
difference de lock, pas par le critere.

Regeneration (hors reseau, deterministe) :

```bash
python scripts/notebook_tools/pyodide_eligibility.py --format md \
  --out docs/reference/pyodide-eligibilite.md \
  --refus-out docs/reference/pyodide-refus.tsv \
  --pyodide-lock docs/reference/pyodide-lock.json \
  --wheel-cache docs/reference/pyodide-wheel-cache.json
```

## Critere d'eligibilite

Un carnet est **eligible** si et seulement si les quatre conditions suivantes sont reunies.
Ce paragraphe est la source de verite : la regenereation du site s'appuie sur ce critere,
jamais sur une liste maintenue a la main.

1. **Aucun GPU** : aucun import de `torch`, `tensorflow`, `jax`, `cupy`, `onnxruntime`,
   ni usage explicite de `torch.cuda` ou de `nvidia-smi`.
2. **Aucune cle d'API** : aucune variable d'environnement dont le nom ressemble a une
   cle (`*KEY*`, `*TOKEN*`, `*SECRET*`, `*PASSWORD*`, `*CREDENTIAL*`), ni saisie
   interactive de secret. Seuls les **noms** sont collectes, jamais les valeurs.
3. **Aucun service reseau** : aucun appel a un hote distant (`http(s)://`), aucun port
   local de service, aucun module client reseau (`requests`, `httpx`, `socket`, ...).
4. **Tous les imports satisfaits par le bundle** : chaque import est soit dans la
   bibliotheque standard, soit un paquet present dans `pyodide-lock.json`, soit
   installe par le carnet lui-meme (`micropip`, `%pip`, `!pip`), soit fourni par un
   module de la **serie** du carnet livre avec lui (helper du carnet, **paquet
   inclus** : un dossier porteur d'un `__init__.py` compte comme un module local)
   dont les propres dependances sont satisfaites. Le bundle publie des fichiers
   et n'installe rien : une roue pure que le carnet n'installe pas n'est pas
   fournie, et un module d'une autre serie n'est pas livre.

Le refus porte toujours un motif : `gpu`, `cle`, `reseau`, `import_absent` ou
`suffisance` (une dependance que le bundle ne pourra pas fournir).

Lock de reference : `pyodide-lock.json` (ABI 2026_0, Python 3.14.2, wasm32, emscripten_5_0_3, 357 paquets).

Les **noms** des variables d'environnement ne sont pas publies : un nom qui ressemble
a une cle (`*_API_KEY`) fait echouer le scanner de secrets du depot, alors que le nom
seul n'est pas un secret. Le detail des refus (`pyodide-refus.tsv`) publie donc le
**nombre** de variables detectees (`cle=N`), pas leurs noms ; les noms restent
accessibles en local avec `--detail-cle` (sortie a ne pas committer).

## Table par serie

| Serie | Carnets Python | Eligibles | Refuses | dont GPU | dont cle | dont reseau | dont import absent | dont suffisance |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| 00-GenAI-Environment | 7 | 0 | 7 | 1 | 4 | 7 | 1 | 6 |
| 3D | 10 | 3 | 7 | 7 | 0 | 1 | 0 | 2 |
| AgentSystems | 2 | 2 | 0 | 0 | 0 | 0 | 0 | 0 |
| Applications | 10 | 9 | 1 | 1 | 0 | 0 | 1 | 0 |
| ArgumentAnalysis | 40 | 18 | 22 | 1 | 7 | 8 | 11 | 16 |
| Audio | 51 | 1 | 50 | 29 | 21 | 18 | 20 | 48 |
| Automata | 2 | 2 | 0 | 0 | 0 | 0 | 0 | 0 |
| CaseStudies | 4 | 0 | 4 | 0 | 4 | 0 | 0 | 4 |
| Causalite | 12 | 2 | 10 | 1 | 0 | 1 | 0 | 9 |
| Chaines | 16 | 16 | 0 | 0 | 0 | 0 | 0 | 0 |
| Coalitions | 4 | 2 | 2 | 0 | 0 | 0 | 2 | 1 |
| Complexity | 29 | 25 | 4 | 0 | 0 | 0 | 1 | 3 |
| Compression | 13 | 10 | 3 | 1 | 0 | 0 | 0 | 2 |
| Constructeur | 1 | 1 | 0 | 0 | 0 | 0 | 0 | 0 |
| DataScienceWithAgents | 110 | 40 | 70 | 45 | 5 | 3 | 26 | 28 |
| DecisionTheory | 15 | 2 | 13 | 0 | 0 | 0 | 0 | 13 |
| Diagnostic-Medical | 2 | 0 | 2 | 0 | 0 | 0 | 2 | 2 |
| Dynamics | 11 | 10 | 1 | 0 | 1 | 1 | 0 | 0 |
| Dynamiques | 1 | 1 | 0 | 0 | 0 | 0 | 0 | 0 |
| FallacyDetection | 5 | 2 | 3 | 0 | 0 | 1 | 1 | 1 |
| FineTuning | 11 | 0 | 11 | 11 | 0 | 0 | 4 | 8 |
| Fondations | 2 | 2 | 0 | 0 | 0 | 0 | 0 | 0 |
| HumorDetection | 1 | 1 | 0 | 0 | 0 | 0 | 0 | 0 |
| ICT-Series | 103 | 82 | 21 | 9 | 1 | 3 | 0 | 16 |
| Image | 33 | 5 | 28 | 7 | 21 | 22 | 4 | 24 |
| Infer | 1 | 1 | 0 | 0 | 0 | 0 | 0 | 0 |
| InformationQuantique | 2 | 2 | 0 | 0 | 0 | 0 | 0 | 0 |
| InformationTheory | 3 | 3 | 0 | 0 | 0 | 0 | 0 | 0 |
| Integrales | 4 | 4 | 0 | 0 | 0 | 0 | 0 | 0 |
| Jauge | 5 | 4 | 1 | 1 | 0 | 0 | 0 | 0 |
| Lean | 135 | 108 | 27 | 1 | 5 | 4 | 11 | 18 |
| ML-Training-Pipeline | 18 | 11 | 7 | 0 | 0 | 0 | 1 | 7 |
| ML.Net | 15 | 12 | 3 | 1 | 0 | 0 | 2 | 2 |
| Metajeux | 7 | 5 | 2 | 1 | 0 | 0 | 1 | 0 |
| MyIA.AI.Notebooks/GameTheory | 70 | 48 | 22 | 2 | 3 | 3 | 8 | 11 |
| MyIA.AI.Notebooks/IIT | 6 | 1 | 5 | 0 | 0 | 0 | 0 | 5 |
| MyIA.AI.Notebooks/NLP | 11 | 8 | 3 | 0 | 0 | 0 | 3 | 1 |
| MyIA.AI.Notebooks/Probas | 1 | 0 | 1 | 0 | 0 | 0 | 0 | 1 |
| MyIA.AI.Notebooks/RL | 28 | 10 | 18 | 12 | 0 | 0 | 0 | 15 |
| MyIA.AI.Notebooks/Sudoku | 21 | 8 | 13 | 2 | 1 | 1 | 5 | 7 |
| NotionsInteractives | 1 | 0 | 1 | 0 | 0 | 0 | 0 | 1 |
| Numerique | 2 | 2 | 0 | 0 | 0 | 0 | 0 | 0 |
| Part1-Foundations | 29 | 18 | 11 | 0 | 1 | 1 | 7 | 5 |
| Part2-CSP | 10 | 1 | 9 | 0 | 1 | 0 | 9 | 0 |
| Part3-Cas-pratiques | 30 | 6 | 24 | 0 | 0 | 0 | 20 | 7 |
| Part4-Metaheuristics | 2 | 2 | 0 | 0 | 0 | 0 | 0 | 0 |
| Part5-Frontieres | 13 | 3 | 10 | 0 | 0 | 0 | 10 | 0 |
| Planification-Oncologie | 2 | 0 | 2 | 2 | 0 | 0 | 2 | 2 |
| Planners | 16 | 2 | 14 | 1 | 2 | 3 | 4 | 12 |
| Plateformes-Conversationnelles | 28 | 8 | 20 | 0 | 19 | 18 | 2 | 17 |
| PostTraining | 37 | 4 | 33 | 29 | 2 | 1 | 12 | 20 |
| PyMC | 20 | 0 | 20 | 0 | 0 | 0 | 1 | 20 |
| Python | 68 | 15 | 53 | 13 | 4 | 4 | 40 | 28 |
| RAG-et-Memoire-Semantique | 14 | 0 | 14 | 4 | 4 | 5 | 3 | 14 |
| Reseau-Electrique-Intelligent | 2 | 1 | 1 | 0 | 0 | 0 | 1 | 0 |
| SMT | 25 | 0 | 25 | 0 | 0 | 0 | 24 | 2 |
| Security | 11 | 4 | 7 | 3 | 3 | 4 | 0 | 1 |
| SemanticKernel | 18 | 2 | 16 | 0 | 11 | 8 | 3 | 16 |
| SemanticWeb | 15 | 1 | 14 | 0 | 1 | 5 | 3 | 13 |
| SignalProcessing | 4 | 4 | 0 | 0 | 0 | 0 | 0 | 0 |
| SmartContracts | 31 | 10 | 21 | 0 | 3 | 17 | 19 | 17 |
| SocialChoice | 12 | 6 | 6 | 0 | 0 | 0 | 5 | 1 |
| Structures | 1 | 1 | 0 | 0 | 0 | 0 | 0 | 0 |
| SymbolicLearning | 20 | 7 | 13 | 7 | 2 | 2 | 6 | 6 |
| Texte | 49 | 3 | 46 | 19 | 22 | 27 | 5 | 35 |
| Tweety | 19 | 1 | 18 | 0 | 0 | 2 | 18 | 6 |
| Vibe-Coding | 6 | 5 | 1 | 0 | 0 | 0 | 0 | 1 |
| Video | 23 | 3 | 20 | 16 | 11 | 14 | 6 | 19 |
| _research | 1 | 0 | 1 | 1 | 1 | 1 | 0 | 1 |
| docker-configurations/notebook-runner | 2 | 2 | 0 | 0 | 0 | 0 | 0 | 0 |
| gateway | 2 | 0 | 2 | 0 | 0 | 0 | 1 | 1 |
| kelly_lean | 5 | 5 | 0 | 0 | 0 | 0 | 0 | 0 |
| partner-course-quant-trading | 7 | 0 | 7 | 0 | 0 | 0 | 5 | 4 |
| projects | 114 | 5 | 109 | 10 | 0 | 3 | 66 | 54 |
| research | 26 | 5 | 21 | 4 | 0 | 0 | 4 | 17 |
| scripts/notebook_tools | 1 | 1 | 0 | 0 | 0 | 0 | 0 | 0 |

## Classes d'ecart de suffisance

Le bundle publie des fichiers et n'installe rien : un import n'est fourni que s'il
est dans la distribution, s'il est installe par le carnet, ou s'il vient d'un module
de la serie livre avec le carnet. Trois classes d'ecart separent alors le critere de
ce que le bundle livre -- chacune compte des **carnets**, un carnet compte une fois
par classe :

| Classe | Ce qu'elle dit | Carnets |
|---|---|---:|
| `dependance_locale` | un module de la serie a une dependance absente de la distribution | 18 |
| `hors_serie` | le carnet importe un module d'une autre serie, non livre par le bundle | 23 |
| `absent_distribution` | l'import est une roue pure que le carnet n'installe pas lui-meme | 174 |

Ces trois classes sont mesurees sur la population que le critere acceptait
**avant** l'alignement -- un carnet deja refuse pour un GPU ou une cle n'y
figure pas : son ecart de suffisance ne changeait rien a ce que le critere
disait. Le comptage avant/apres est donc sur la meme population :

| Mesure | Avant | Apres |
|---|---:|---:|
| Carnets eligibles | 795 | 588 |

Le detail des dependances est dans le fichier `pyodide-refus.tsv` (colonne `suffisance`).

## Carnets eligibles

| Carnet | Serie | Noyau | Imports Pyodide | Roues pures |
|---|---|---|---|---|
| `MyIA.AI.Notebooks/GenAI/3D/10-SIG-3D-Tiles-Python.ipynb` | 3D | python3 | matplotlib==3.10.8, numpy==2.4.6, pillow==12.2.0 | - |
| `MyIA.AI.Notebooks/GenAI/3D/3D-09-Photogrammetrie-MNT-Python.ipynb` | 3D | python3 | matplotlib==3.10.8, numpy==2.4.6, rasterio==1.5.0 | - |
| `MyIA.AI.Notebooks/GenAI/3D/3D-11-Qualifier-un-MNT-SIG-Python.ipynb` | 3D | python3 | numpy==2.4.6, rasterio==1.5.0 | - |
| `MyIA.AI.Notebooks/cross-series/AgentSystems/AgentSystems-01-Perception-Vers-Action-Python.ipynb` | AgentSystems | python3 | - | - |
| `MyIA.AI.Notebooks/cross-series/AgentSystems/AgentSystems-02-Perception-Active-Valeur-Information-Python.ipynb` | AgentSystems | python3 | - | - |
| `MyIA.AI.Notebooks/Probas/Applications/Marches-01-Retour-Polya-Watson-Python.ipynb` | Applications | python3 | mpmath==1.4.1, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/Probas/Applications/Percolation/Percolation-01-Supercritique-Python.ipynb` | Applications | python3 | matplotlib==3.10.8, networkx==3.6.1, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/Probas/Applications/Percolation/Percolation-03-Critique-Python.ipynb` | Applications | python3 | matplotlib==3.10.8, networkx==3.6.1, numpy==2.4.6, scipy==1.18.0 | - |
| `MyIA.AI.Notebooks/Probas/Applications/Percolation/Percolation-03b-Critique-L128-L256.ipynb` | Applications | python3 | matplotlib==3.10.8, networkx==3.6.1, numpy==2.4.6, scipy==1.18.0 | - |
| `MyIA.AI.Notebooks/Probas/Applications/Percolation/Percolation-03c-Critique-L512.ipynb` | Applications | python3 | matplotlib==3.10.8, networkx==3.6.1, numpy==2.4.6, scipy==1.18.0 | - |
| `MyIA.AI.Notebooks/Probas/Applications/Percolation/Percolation-04-Sharpness-Python.ipynb` | Applications | python3 | matplotlib==3.10.8, networkx==3.6.1, numpy==2.4.6, scipy==1.18.0 | - |
| `MyIA.AI.Notebooks/Probas/Applications/Percolation/Percolation-05-Dimension-Fractale-Effondrement-Python.ipynb` | Applications | python3 | matplotlib==3.10.8, numpy==2.4.6, scipy==1.18.0 | - |
| `MyIA.AI.Notebooks/Probas/Applications/Probas-KLS-Concentration.ipynb` | Applications | python3 | matplotlib==3.10.8, numpy==2.4.6, scipy==1.18.0 | - |
| `MyIA.AI.Notebooks/Probas/Applications/Quotients-Fibres-Recollement-Python.ipynb` | Applications | python3 | numpy==2.4.6, scipy==1.18.0 | - |
| `MyIA.AI.Notebooks/SymbolicAI/ArgumentAnalysis/Argument_Analysis_Gouvernance_Multi_Agents.ipynb` | ArgumentAnalysis | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/SymbolicAI/ArgumentAnalysis/Argumentation-01-Toulmin-Model-Python.ipynb` | ArgumentAnalysis | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/ArgumentAnalysis/Argumentation-01b-Schemes-Walton-Python.ipynb` | ArgumentAnalysis | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/ArgumentAnalysis/Argumentation-02b-Argumentum-Cards-Python.ipynb` | ArgumentAnalysis | python3 | matplotlib==3.10.8 | - |
| `MyIA.AI.Notebooks/SymbolicAI/ArgumentAnalysis/Argumentation-03-Dung-AF-Semantics-Python.ipynb` | ArgumentAnalysis | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/ArgumentAnalysis/Argumentation-03b-Value-Based-AF-Python.ipynb` | ArgumentAnalysis | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/ArgumentAnalysis/Argumentation-03c-Ranking-Semantics-Python.ipynb` | ArgumentAnalysis | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/ArgumentAnalysis/Argumentation-04-Dialogues-Protocolises-Python.ipynb` | ArgumentAnalysis | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/ArgumentAnalysis/Argumentation-04b-Knowledge-Base-Python.ipynb` | ArgumentAnalysis | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/ArgumentAnalysis/Argumentation-05c-Formal-Richness-Matrix-Python.ipynb` | ArgumentAnalysis | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/ArgumentAnalysis/Argumentation-06-JTMS-Python.ipynb` | ArgumentAnalysis | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/ArgumentAnalysis/Argumentation-06b-ATMS-Conflits-Python.ipynb` | ArgumentAnalysis | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/ArgumentAnalysis/Argumentation-07b-Communication-Channels-Python.ipynb` | ArgumentAnalysis | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/ArgumentAnalysis/Argumentation-07c-Orchestration-Modes-Python.ipynb` | ArgumentAnalysis | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/ArgumentAnalysis/Argumentation-08e-Argument-Profile-Python.ipynb` | ArgumentAnalysis | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/ArgumentAnalysis/Argumentation-09-Guardrails-AI-Shield-Python.ipynb` | ArgumentAnalysis | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/ArgumentAnalysis/Argumentation-10-Privacy-Export-Python.ipynb` | ArgumentAnalysis | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/ArgumentAnalysis/Argumentation-Onto-02-CrossLinks-CSV-Python.ipynb` | ArgumentAnalysis | python3 | matplotlib==3.10.8, numpy==2.4.6, pandas==3.0.2 | - |
| `MyIA.AI.Notebooks/GenAI/Audio/06-Diffusion-SOTA/Audio-06-3-AudioDiffusion-Comparison-A-vs-B-Python.ipynb` | Audio | python3 | - | - |
| `MyIA.AI.Notebooks/InformationCalcul/Automata/Automata-01-AutomatesFinis-Python.ipynb` | Automata | python3 | - | - |
| `MyIA.AI.Notebooks/InformationCalcul/Automata/Automata-02-ExpressionsRegulieres-Python.ipynb` | Automata | python3 | - | - |
| `MyIA.AI.Notebooks/Probas/Causalite/Causalite-00-Echelle-de-Pearl-Intro-Python.ipynb` | Causalite | python3 | matplotlib==3.10.8, networkx==3.6.1, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/Probas/Causalite/Causalite-07-Quasi-Experimentales-Python.ipynb` | Causalite | coursia-ml-training | matplotlib==3.10.8, numpy==2.4.6, pandas==3.0.2, scikit-learn==1.8.0, scipy==1.18.0, statsmodels==0.14.6 | - |
| `MyIA.AI.Notebooks/Physique/Chaines/Chaines-01-Axiome-Intrication-Constante-Structure-Fine-Python.ipynb` | Chaines | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/Physique/Chaines/Chaines-02-Born-Unitarite-Incertitude-Python.ipynb` | Chaines | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/Physique/Chaines/Chaines-03-Mesure-Lavage-POVM-Python.ipynb` | Chaines | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/Physique/Chaines/Chaines-04-Indiscernabilite-Spin-Statistique-Python.ipynb` | Chaines | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/Physique/Chaines/Chaines-05-Energie-Hamiltonien-Premiere-Puissance-Python.ipynb` | Chaines | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/Physique/Chaines/Chaines-06-Integrale-Chemin-Somme-Finie-Enregistrements-Python.ipynb` | Chaines | python3 | - | - |
| `MyIA.AI.Notebooks/Physique/Chaines/Chaines-07-Fonction-Wigner-Signe-N-Corps-Python.ipynb` | Chaines | python3 | - | - |
| `MyIA.AI.Notebooks/Physique/Chaines/Chaines-08-Corollaires-Quantique-Racines-Python.ipynb` | Chaines | python3 | - | - |
| `MyIA.AI.Notebooks/Physique/Chaines/Chaines-09-Coordonnee-Ordre-Chaine-Serie-Python.ipynb` | Chaines | python3 | - | - |
| `MyIA.AI.Notebooks/Physique/Chaines/Chaines-10-Groupe-Rotations-Automorphismes-Directions-Python.ipynb` | Chaines | python3 | - | - |
| `MyIA.AI.Notebooks/Physique/Chaines/Chaines-11-Groupe-Lorentz-Signature-Un-Contre-Trois-Python.ipynb` | Chaines | python3 | - | - |
| `MyIA.AI.Notebooks/Physique/Chaines/Chaines-12-Boosts-Et-L-Unite-Une-Python.ipynb` | Chaines | python3 | - | - |
| `MyIA.AI.Notebooks/Physique/Chaines/Chaines-13-Spin-Helicite-Groupe-Spin-C-Python.ipynb` | Chaines | python3 | matplotlib==3.10.8 | - |
| `MyIA.AI.Notebooks/Physique/Chaines/Chaines-14-P-C-T-Et-CPT-Python.ipynb` | Chaines | python3 | matplotlib==3.10.8 | - |
| `MyIA.AI.Notebooks/Physique/Chaines/Chaines-15-Theoreme-D-Ordre-Python.ipynb` | Chaines | python3 | matplotlib==3.10.8 | - |
| `MyIA.AI.Notebooks/Physique/Chaines/Chaines-16-Invariance-Jauge-Groupe-Face-Python.ipynb` | Chaines | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/GameTheory/Coalitions/Coalitions-02-Assistance-Games-Python.ipynb` | Coalitions | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/GameTheory/Coalitions/Coalitions-04-Munkres-Affectation-Python.ipynb` | Coalitions | python3 | numpy==2.4.6, scipy==1.18.0 | - |
| `MyIA.AI.Notebooks/InformationCalcul/Complexity/Complexity-01-StepCounting-Python.ipynb` | Complexity | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/InformationCalcul/Complexity/Complexity-02-P-NP-Reduction-Python.ipynb` | Complexity | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/InformationCalcul/Complexity/Complexity-02b-SAT-PhaseTransition-Python.ipynb` | Complexity | python3 | matplotlib==3.10.8 | - |
| `MyIA.AI.Notebooks/InformationCalcul/Complexity/Complexity-02c-XOR-SAT-Phase-Transition-Python.ipynb` | Complexity | coursia-py313 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/InformationCalcul/Complexity/Complexity-03-HierarchieTemporelle-Python.ipynb` | Complexity | python3 | - | - |
| `MyIA.AI.Notebooks/InformationCalcul/Complexity/Complexity-03b-HartmanisStearns-HierarchieTemporelle-Python.ipynb` | Complexity | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/InformationCalcul/Complexity/Complexity-03c-ComplexityZoo-Navigation-Python.ipynb` | Complexity | python3 | - | - |
| `MyIA.AI.Notebooks/InformationCalcul/Complexity/Complexity-03d-ETH-Refutation-Annoncee-Lean-Python.ipynb` | Complexity | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/InformationCalcul/Complexity/Complexity-03e-Barrieres-Exposants-WordRAM-Python.ipynb` | Complexity | python3 | - | - |
| `MyIA.AI.Notebooks/InformationCalcul/Complexity/Complexity-03f-ReductionsTriangle-Lopsided-Python.ipynb` | Complexity | python3 | - | - |
| `MyIA.AI.Notebooks/InformationCalcul/Complexity/Complexity-03h-ExposantProduitMatriciel-NineQuarts-Python.ipynb` | Complexity | python3 | - | - |
| `MyIA.AI.Notebooks/InformationCalcul/Complexity/Complexity-04-OnlineAlgorithms-Python.ipynb` | Complexity | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/InformationCalcul/Complexity/Complexity-04b-OnlineConjectures-Secretary-KServer-Python.ipynb` | Complexity | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/InformationCalcul/Complexity/Complexity-04c-KServer-WorkFunction-Python.ipynb` | Complexity | python3 | matplotlib==3.10.8 | - |
| `MyIA.AI.Notebooks/InformationCalcul/Complexity/Complexity-04d-Secretaire-Matroidal-Python.ipynb` | Complexity | python3 | matplotlib==3.10.8 | - |
| `MyIA.AI.Notebooks/InformationCalcul/Complexity/Complexity-05-CountingHarder-Permanent-Python.ipynb` | Complexity | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/InformationCalcul/Complexity/Complexity-05b-AaronsonArkhipov-PermanenteBosonSampling-Python.ipynb` | Complexity | python3 | matplotlib==3.10.8, numpy==2.4.6, pandas==3.0.2 | - |
| `MyIA.AI.Notebooks/InformationCalcul/Complexity/Complexity-06-Simuler-Circuit-Quantique-Classiquement-Python.ipynb` | Complexity | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/InformationCalcul/Complexity/Complexity-06c-ClassicalAtHeart-Python.ipynb` | Complexity | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/InformationCalcul/Complexity/Complexity-06d-AaronsonAmbainis-VariableInfluente-Python.ipynb` | Complexity | python3 | numpy==2.4.6, scipy==1.18.0 | - |
| `MyIA.AI.Notebooks/InformationCalcul/Complexity/Complexity-07-KolmogorovBornee-Sequences-Python.ipynb` | Complexity | coursia-ml-training | matplotlib==3.10.8 | - |
| `MyIA.AI.Notebooks/InformationCalcul/Complexity/Complexity-07b-LeTourDesGrandsNombres-Python.ipynb` | Complexity | python3 | - | - |
| `MyIA.AI.Notebooks/InformationCalcul/Complexity/Complexity-07c-LeBilanMathocalypse-Python.ipynb` | Complexity | python3 | - | - |
| `MyIA.AI.Notebooks/InformationCalcul/Complexity/Complexity-08d-IndependanceProuvee-BusyBeaver-Covering-Python.ipynb` | Complexity | python3 | - | - |
| `MyIA.AI.Notebooks/InformationCalcul/Complexity/Complexity-08e-NF-MachinesCompteARebours-Python.ipynb` | Complexity | python3 | - | - |
| `MyIA.AI.Notebooks/InformationCalcul/Compression/Compression-01-ShannonFano-Prefixe-Python.ipynb` | Compression | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/InformationCalcul/Compression/Compression-02-HuffmanCanonique-Python.ipynb` | Compression | python3 | matplotlib==3.10.8 | - |
| `MyIA.AI.Notebooks/InformationCalcul/Compression/Compression-03-LZ77-Python.ipynb` | Compression | python3 | matplotlib==3.10.8 | - |
| `MyIA.AI.Notebooks/InformationCalcul/Compression/Compression-04-ANS-Python.ipynb` | Compression | python3 | matplotlib==3.10.8 | - |
| `MyIA.AI.Notebooks/InformationCalcul/Compression/Compression-04b-CodecsSOTA-Pareto-Python.ipynb` | Compression | python3 | brotli==1.2.0, lz4==4.4.5, matplotlib==3.10.8, numpy==2.4.6, zstandard==0.25.0 | - |
| `MyIA.AI.Notebooks/InformationCalcul/Compression/Compression-05b-NeuroSymbolic-Recipe-Python.ipynb` | Compression | python3 | matplotlib==3.10.8, pandas==3.0.2 | - |
| `MyIA.AI.Notebooks/InformationCalcul/Compression/Compression-06-MDL-Kolmogorov-Python.ipynb` | Compression | python3 | matplotlib==3.10.8 | - |
| `MyIA.AI.Notebooks/InformationCalcul/Compression/Compression-07-Triage-LLM-Operations-Reelles-Python.ipynb` | Compression | python3 | - | - |
| `MyIA.AI.Notebooks/InformationCalcul/Compression/Compression-08-Assemblage-Vectoriel-Python.ipynb` | Compression | python3 | lxml==6.1.3 | - |
| `MyIA.AI.Notebooks/InformationCalcul/Compression/Compression-09b-Entropie-Conditionnelle-Taux-Compression-Python.ipynb` | Compression | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/Physique/Constructeur/Constructeur-01-Lois-Comme-Taches-Python.ipynb` | Constructeur | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/01-Python-For-Data-Science/notebooks/PyDS-01-Python_pour_la_Data_Science-Python.ipynb` | DataScienceWithAgents | python3 | - | - |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/01-Python-For-Data-Science/notebooks/PyDS-02-Manipulation_de_Donnees_avec_NumPy-Python.ipynb` | DataScienceWithAgents | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/01-Python-For-Data-Science/notebooks/PyDS-03-Analyse_de_Donnees_avec_Pandas-Python.ipynb` | DataScienceWithAgents | python3 | matplotlib==3.10.8, numpy==2.4.6, pandas==3.0.2 | - |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/01-Python-For-Data-Science/notebooks/PyDS-05-Exploration_Nettoyage_Donnees_Reelles-Python.ipynb` | DataScienceWithAgents | python3 | pandas==3.0.2 | - |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/02-ML-Cours/2.1-Workflow-ML.ipynb` | DataScienceWithAgents | python3 | matplotlib==3.10.8, numpy==2.4.6, pandas==3.0.2, scikit-learn==1.8.0 | - |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/02-ML-Cours/2.11-Regularisation-Sparse-LASSO.ipynb` | DataScienceWithAgents | python3 | numpy==2.4.6, scikit-learn==1.8.0 | - |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/02-ML-Cours/2.11c-Lasso-SOTA-Comparison.ipynb` | DataScienceWithAgents | python3 | numpy==2.4.6, scikit-learn==1.8.0 | - |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/02-ML-Cours/2.13-Analyse-Erreurs.ipynb` | DataScienceWithAgents | python3 | matplotlib==3.10.8, numpy==2.4.6, pandas==3.0.2, scikit-learn==1.8.0 | - |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/02-ML-Cours/2.2-Descente-de-gradient.ipynb` | DataScienceWithAgents | python3 | matplotlib==3.10.8, numpy==2.4.6, pandas==3.0.2, scikit-learn==1.8.0 | - |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/02-ML-Cours/2.3-Regression-lineaire-logistique.ipynb` | DataScienceWithAgents | python3 | matplotlib==3.10.8, numpy==2.4.6, pandas==3.0.2, scikit-learn==1.8.0, scipy==1.18.0, statsmodels==0.14.6 | - |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/02-ML-Cours/2.3b-Naive-Bayes-Generatif.ipynb` | DataScienceWithAgents | python3 | matplotlib==3.10.8, numpy==2.4.6, scikit-learn==1.8.0, scipy==1.18.0 | - |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/02-ML-Cours/2.3c-Regression-Grande-Dimension.ipynb` | DataScienceWithAgents | python3 | matplotlib==3.10.8, numpy==2.4.6, scikit-learn==1.8.0 | - |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/02-ML-Cours/2.3d-Modele-Gaussien-LDA-QDA.ipynb` | DataScienceWithAgents | python3 | matplotlib==3.10.8, numpy==2.4.6, scikit-learn==1.8.0, scipy==1.18.0 | - |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/02-ML-Cours/2.4-Arbres-Forets-Ensembles.ipynb` | DataScienceWithAgents | python3 | matplotlib==3.10.8, numpy==2.4.6, pandas==3.0.2, scikit-learn==1.8.0 | - |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/02-ML-Cours/2.4b-AdaBoost-From-Scratch.ipynb` | DataScienceWithAgents | python3 | matplotlib==3.10.8, numpy==2.4.6, pandas==3.0.2, scikit-learn==1.8.0 | - |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/02-ML-Cours/2.5-Biais-Variance-CV-ROC.ipynb` | DataScienceWithAgents | python3 | matplotlib==3.10.8, numpy==2.4.6, pandas==3.0.2, scikit-learn==1.8.0 | - |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/02-ML-Cours/2.5b-Calibration-Probabilites.ipynb` | DataScienceWithAgents | python3 | matplotlib==3.10.8, numpy==2.4.6, pandas==3.0.2, scikit-learn==1.8.0 | - |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/02-ML-Cours/2.5c-Equite-Sous-Groupes.ipynb` | DataScienceWithAgents | python3 | matplotlib==3.10.8, numpy==2.4.6, pandas==3.0.2, scikit-learn==1.8.0 | - |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/02-ML-Cours/2.7-Modeles-Non-Parametriques.ipynb` | DataScienceWithAgents | python3 | matplotlib==3.10.8, numpy==2.4.6, scikit-learn==1.8.0 | - |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/02-ML-Cours/2.7b-SMO-From-Scratch.ipynb` | DataScienceWithAgents | python3 | matplotlib==3.10.8, numpy==2.4.6, scikit-learn==1.8.0 | - |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/02-ML-Cours/2.7c-SVM-SOTA-Comparison.ipynb` | DataScienceWithAgents | python3 | numpy==2.4.6, scikit-learn==1.8.0 | - |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/02-ML-Cours/2.8-Theorie-PAC.ipynb` | DataScienceWithAgents | python3 | matplotlib==3.10.8, numpy==2.4.6, scikit-learn==1.8.0 | - |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/02-ML-Cours/2.8c-Borne-Temoin-Concentration.ipynb` | DataScienceWithAgents | coursia-ml-training | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/03-Deep-Learning/3.0-Theorie-Information.ipynb` | DataScienceWithAgents | python3 | numpy==2.4.6, scikit-learn==1.8.0 | - |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/03-Deep-Learning/3.4d-Fourier-Features-Biais-Spectral-Python.ipynb` | DataScienceWithAgents | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/03-Deep-Learning/3.5-Phenomenes-de-Generalisation.ipynb` | DataScienceWithAgents | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/03-Deep-Learning/3.6-Modeles-Generatifs.ipynb` | DataScienceWithAgents | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/03-Deep-Learning/3.8-Representations-Contrastives.ipynb` | DataScienceWithAgents | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/06-Agents-de-Donnees/Day1-Foundations/Labs/Lab1-PythonForDataScience.ipynb` | DataScienceWithAgents | python3 | matplotlib==3.10.8, numpy==2.4.6, pandas==3.0.2, scikit-learn==1.8.0 | - |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/06-Agents-de-Donnees/Day3-Data-Agents/Labs/Lab4-DataWrangling/Lab4-DataWrangling.ipynb` | DataScienceWithAgents | python3 | pandas==3.0.2 | - |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/07-Orchestration-d-Agents/Day4-Foundations/Lab8-ADK-Introduction.ipynb` | DataScienceWithAgents | python3 | - | - |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/07-Orchestration-d-Agents/Day5-DS-Star/Lab10-File-Analyzer.ipynb` | DataScienceWithAgents | python3 | numpy==2.4.6, pandas==3.0.2 | - |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/07-Orchestration-d-Agents/Day5-DS-Star/Lab11-Planner-Coder-Loop.ipynb` | DataScienceWithAgents | python3 | numpy==2.4.6, pandas==3.0.2 | - |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/07-Orchestration-d-Agents/Day5-DS-Star/Lab12-DS-Star-Workshop.ipynb` | DataScienceWithAgents | python3 | numpy==2.4.6, pandas==3.0.2 | - |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/07-Orchestration-d-Agents/Day5-DS-Star/Lab12b-Sequential-Orchestration.ipynb` | DataScienceWithAgents | python3 | - | - |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/07-Orchestration-d-Agents/Day5-DS-Star/Lab12c-Agent-Handoff.ipynb` | DataScienceWithAgents | python3 | - | - |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/07-Orchestration-d-Agents/Day5-DS-Star/Lab12e-Session-Persistence.ipynb` | DataScienceWithAgents | python3 | - | - |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/07-Orchestration-d-Agents/Day6-MLE-Star/Lab14-Ablation-Refinement.ipynb` | DataScienceWithAgents | python3 | numpy==2.4.6, pandas==3.0.2, scikit-learn==1.8.0 | - |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/07-Orchestration-d-Agents/Day6-MLE-Star/Lab15-Kaggle-Challenge.ipynb` | DataScienceWithAgents | python3 | numpy==2.4.6, pandas==3.0.2, scikit-learn==1.8.0, xgboost==2.1.4 | - |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/07-Orchestration-d-Agents/Day7-Production/Lab17-Final-Project.ipynb` | DataScienceWithAgents | python3 | numpy==2.4.6, pandas==3.0.2 | - |
| `MyIA.AI.Notebooks/Probas/DecisionTheory/Actuariat/Actuariat-02-Freq-Sev-Hierarchique.ipynb` | DecisionTheory | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/Probas/DecisionTheory/DecPyMC/DecPyMC-08-Actuariat-Capstone.ipynb` | DecisionTheory | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/GameTheory/Dynamics/Dynamics-01-Jeux-Repetes-Folk-Theorem-Python.ipynb` | Dynamics | python3 | matplotlib==3.10.8, numpy==2.4.6, scipy==1.18.0 | - |
| `MyIA.AI.Notebooks/GameTheory/Dynamics/Dynamics-02-Jeux-Repetes-Lean-Python.ipynb` | Dynamics | python3 | - | - |
| `MyIA.AI.Notebooks/GameTheory/Dynamics/Dynamics-03-Sympathie-vs-Engagement-Python.ipynb` | Dynamics | python3 | matplotlib==3.10.8, numpy==2.4.6, scipy==1.18.0 | - |
| `MyIA.AI.Notebooks/GameTheory/Dynamics/Dynamics-04-Open-Source-Game-Theory-Python.ipynb` | Dynamics | python3 | - | - |
| `MyIA.AI.Notebooks/GameTheory/Dynamics/Dynamics-04c-Cooperation-Payorienne-Kripke-Python.ipynb` | Dynamics | python3 | - | - |
| `MyIA.AI.Notebooks/GameTheory/Dynamics/Dynamics-05-Agents-Bornes-Python.ipynb` | Dynamics | python3 | - | - |
| `MyIA.AI.Notebooks/GameTheory/Dynamics/Dynamics-06-Preuves-Bornees-Cout-du-Raisonnement-Python.ipynb` | Dynamics | python3 | - | - |
| `MyIA.AI.Notebooks/GameTheory/Dynamics/Dynamics-07-Equilibres-par-Simulation-Python.ipynb` | Dynamics | python3 | matplotlib==3.10.8, numpy==2.4.6, pandas==3.0.2 | - |
| `MyIA.AI.Notebooks/GameTheory/Dynamics/Dynamics-08-Institutions-Transparentes-Python.ipynb` | Dynamics | python3 | - | - |
| `MyIA.AI.Notebooks/GameTheory/Dynamics/Dynamics-09-Biens-Publics-N-Personnes-Python.ipynb` | Dynamics | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/BioMedecine/Dynamiques/Dynamiques-01-Populations-et-Epidemies-Python.ipynb` | Dynamiques | python3 | matplotlib==3.10.8, numpy==2.4.6, scipy==1.18.0 | - |
| `MyIA.AI.Notebooks/GenAI/FallacyDetection/01_taxonomy_intro.ipynb` | FallacyDetection | python3 | - | - |
| `MyIA.AI.Notebooks/GenAI/FallacyDetection/03_taxonomy_coverage_gap.ipynb` | FallacyDetection | python3 | - | - |
| `MyIA.AI.Notebooks/Probas/Fondations/Probas-CLT-Theoreme-Central-Limite.ipynb` | Fondations | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/Probas/Fondations/Probas-MCMC-Echantillonnage-Metropolis-Python.ipynb` | Fondations | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/GenAI/HumorDetection/01_humor_intro.ipynb` | HumorDetection | python3 | - | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-02-SelfSortingMorphogenesis/ICT-02-SelfSortingMorphogenesis-Python.ipynb` | ICT-Series | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-02-SelfSortingMorphogenesis/ICT-03-RobustnessDelayedGratification-Python.ipynb` | ICT-Series | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-02-SelfSortingMorphogenesis/ICT-04-ChimericArraysKinAggregation-Python.ipynb` | ICT-Series | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-05-CausalEmergence/ICT-06-SortingToTPM-CausalEmergence-Python.ipynb` | ICT-Series | coursia-ml-training | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-05-CausalEmergence/ICT-07-ScaleFreeSignatures-Python.ipynb` | ICT-Series | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-08-AttractorLandscapesEWS-Python.ipynb` | ICT-Series | python3 | matplotlib==3.10.8, numpy==2.4.6, scipy==1.18.0 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-09-AgencyRegeneration-Python.ipynb` | ICT-Series | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-10-CatastropheGrammar-Python.ipynb` | ICT-Series | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-10b-Turing1952-Thom-Morphogenese-Python.ipynb` | ICT-Series | python3 | matplotlib==3.10.8, numpy==2.4.6, scipy==1.18.0 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-11-CausalAgencyProfiles-Python.ipynb` | ICT-Series | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-12-ValenceFieldsAndAnimats/ICT-12-ValenceFieldsAndAnimats-Python.ipynb` | ICT-Series | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-12-ValenceFieldsAndAnimats/ICT-12b-LearnedValence-Python.ipynb` | ICT-Series | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-12-ValenceFieldsAndAnimats/ICT-12c-PregnanceAnimat-Python.ipynb` | ICT-Series | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-12-ValenceFieldsAndAnimats/ICT-12d-InhibitedActionAnimat-Python.ipynb` | ICT-Series | python3 | matplotlib==3.10.8, numpy==2.4.6, pandas==3.0.2 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-12-ValenceFieldsAndAnimats/ICT-12e-Value-of-Information-Animat-Python.ipynb` | ICT-Series | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-13-AxelrodStrategicMorphodynamics-Python.ipynb` | ICT-Series | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-13b-DecroisementDynamiqueObservable-Python.ipynb` | ICT-Series | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-14-FreeEnergySurprise-Python.ipynb` | ICT-Series | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-14b-ActiveInferenceEFE-Python.ipynb` | ICT-Series | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-15-IntegratedComplexity/ICT-15-IntegratedComplexity-Python.ipynb` | ICT-Series | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-15-IntegratedComplexity/ICT-15b-SensitivityCanonicity-Python.ipynb` | ICT-Series | python3 | matplotlib==3.10.8, numpy==2.4.6, pandas==3.0.2 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-15-IntegratedComplexity/ICT-15c-MetaProxyObstruction-Python.ipynb` | ICT-Series | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-15-IntegratedComplexity/ICT-15d-CechObstruction-Python.ipynb` | ICT-Series | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-15-IntegratedComplexity/ICT-15e-Bridge2-RecoverabilityAgency-Python.ipynb` | ICT-Series | python3 | numpy==2.4.6, pandas==3.0.2 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-15-IntegratedComplexity/ICT-15f-Bridge1bis-DecoupledFamily-Python.ipynb` | ICT-Series | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-15-IntegratedComplexity/ICT-15g-EmpiricalHuangExploitation-Python.ipynb` | ICT-Series | python3 | numpy==2.4.6, pandas==3.0.2 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-15-IntegratedComplexity/ICT-15h-Bridge1bis-AsymmetricFamily-Python.ipynb` | ICT-Series | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-15-IntegratedComplexity/ICT-15i-Bridge1bis-2DLandscape-Python.ipynb` | ICT-Series | - | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-15-IntegratedComplexity/ICT-15j-NerveDiscriminant-Python.ipynb` | ICT-Series | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-15-IntegratedComplexity/ICT-15k-RecollementMacroCells-Python.ipynb` | ICT-Series | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-15-IntegratedComplexity/ICT-15l-IndependanceGenerateur-Python.ipynb` | ICT-Series | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-16-MDLTwoPartCode-Python.ipynb` | ICT-Series | python3 | matplotlib==3.10.8, numpy==2.4.6, scipy==1.18.0 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-17-EpsilonMachine/ICT-17-EpsilonMachine-Python.ipynb` | ICT-Series | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-18-ArrowOfTimeReversibilization-Python.ipynb` | ICT-Series | pyphi-iit | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-18b-ReversibilityBudget-Python.ipynb` | ICT-Series | python3 | ipython==9.12.0, matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-19-EnjeuBattery-Python.ipynb` | ICT-Series | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-19b-EnjeuBattery-Raffinement-Python.ipynb` | ICT-Series | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-20-FeatureCatastrophes/ICT-20-FeatureCatastrophes-Python.ipynb` | ICT-Series | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-20-FeatureCatastrophes/ICT-21b-SAECalibration-Python.ipynb` | ICT-Series | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-20-FeatureCatastrophes/ICT-21c-SAECatastrophes-Python.ipynb` | ICT-Series | python3 | matplotlib==3.10.8, numpy==2.4.6, pandas==3.0.2 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-20-FeatureCatastrophes/ICT-22-LLMSubstrat-Python.ipynb` | ICT-Series | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-23-PersonaCatastrophe-Python.ipynb` | ICT-Series | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-24-WorkspaceIgnition-Python.ipynb` | ICT-Series | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-26-SignalingConvention-Python.ipynb` | ICT-Series | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-27-SymbolInvention-Python.ipynb` | ICT-Series | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-28-CollectiveAdoption-Python.ipynb` | ICT-Series | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-29-ConceptInoculation-Python.ipynb` | ICT-Series | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-30-InhibitedInvention-Python.ipynb` | ICT-Series | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-31-ContrasteTroisSubstrats-Python.ipynb` | ICT-Series | python3 | matplotlib==3.10.8, numpy==2.4.6, pandas==3.0.2 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-32-StratificationCausaleLife-Python.ipynb` | ICT-Series | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-33-SoupCollisions-Python.ipynb` | ICT-Series | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-34-BancRecollementLectures-Python.ipynb` | ICT-Series | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-35-HumorCausalProbe-Pilot-Python.ipynb` | ICT-Series | python3 | numpy==2.4.6, scikit-learn==1.8.0 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-35b-HumorCausalPairs-SAE-Python.ipynb` | ICT-Series | python3 | numpy==2.4.6, pandas==3.0.2 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-35c-HumorDepthProfile-SAE-Python.ipynb` | ICT-Series | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-35d-HumorTypologyBreakdown-SAE-Python.ipynb` | ICT-Series | python3 | numpy==2.4.6, pandas==3.0.2 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-36b-RuzsaOnFactorGeometry-Python.ipynb` | ICT-Series | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-37-FLens-BeliefState-Python.ipynb` | ICT-Series | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-39-CompositionRegards-Python.ipynb` | ICT-Series | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-40b-AnalogCognitionWaves-Python.ipynb` | ICT-Series | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-42-InoculationBifurcation-Pilot-Python.ipynb` | ICT-Series | python3 | matplotlib==3.10.8, numpy==2.4.6, pandas==3.0.2, scipy==1.18.0 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-42b-InoculationBifurcation-9B-Python.ipynb` | ICT-Series | python3 | matplotlib==3.10.8, numpy==2.4.6, pandas==3.0.2, scipy==1.18.0 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-42c-InoculationHysteresis-Python.ipynb` | ICT-Series | python3 | matplotlib==3.10.8, numpy==2.4.6, pandas==3.0.2 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-42d-InoculationMatchedPair-Python.ipynb` | ICT-Series | - | matplotlib==3.10.8, numpy==2.4.6, pandas==3.0.2 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-42e-InoculationNegativeWitness-Python.ipynb` | ICT-Series | - | matplotlib==3.10.8, numpy==2.4.6, pandas==3.0.2 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-42f-ReadingGrid-SignedArea-Sham-Python.ipynb` | ICT-Series | - | matplotlib==3.10.8, numpy==2.4.6, pandas==3.0.2 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-46-Strate7-FreeCoordinates-Python.ipynb` | ICT-Series | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-48-WolframClasses-ThermoSignature-Python.ipynb` | ICT-Series | python3 | matplotlib==3.10.8, numpy==2.4.6, pandas==3.0.2, scipy==1.18.0 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-49-JLensFideliteCrossTaille-Python.ipynb` | ICT-Series | python3 | numpy==2.4.6, pandas==3.0.2 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-Annexe-ProxyContextuality-Python.ipynb` | ICT-Series | python3 | - | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-Argumentation-BeliefTrajectories-Python.ipynb` | ICT-Series | python3 | cryptography==47.0.0, ipython==9.12.0, matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-Argumentation-QBFAcceptance-Python.ipynb` | ICT-Series | python3 | - | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-Argumentation-TruthMaintenance-Python.ipynb` | ICT-Series | python3 | - | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-Dissociation-DehaeneF2-SelfReport-Python.ipynb` | ICT-Series | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-Dissociation-PhatSelfReference-Python.ipynb` | ICT-Series | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-Dissociation-SaillancePregnance-Python.ipynb` | ICT-Series | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-Greffe2-EspaceAtteignable-Python.ipynb` | ICT-Series | python3 | - | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-Greffe4-VoteOnChain-Python.ipynb` | ICT-Series | python3 | - | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-Greffe5-AttributionCausale-Python.ipynb` | ICT-Series | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-MUH-FibreTegmark-Python.ipynb` | ICT-Series | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-SAE-JLens-TeteATete-Python.ipynb` | ICT-Series | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-Synthese-CrossSubstrat-Python.ipynb` | ICT-Series | pyphi-iit | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/GenAI/Image/02-Advanced/02-5-Bonsai-Image-Ternary.ipynb` | Image | python3 | ipython==9.12.0, matplotlib==3.10.8, numpy==2.4.6, pandas==3.0.2 | - |
| `MyIA.AI.Notebooks/GenAI/Image/05-History/05-0b-Demoscene-Intros-Procedurales-Python.ipynb` | Image | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/GenAI/Image/05-History/05-0c-Low-Complexity-Art-Python.ipynb` | Image | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/GenAI/Image/05-History/05-0d-Groupes-De-Frise-Python.ipynb` | Image | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/GenAI/Image/05-History/05-0e-MDL-Mesure-Unique-Python.ipynb` | Image | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/Probas/Infer/Infer-07b-TrueSkill-Formules-Fermees-Python.ipynb` | Infer | python3 | - | - |
| `MyIA.AI.Notebooks/Physique/InformationQuantique/InfoQuant-01-Intrication-Werner-PPT-Distillation-Python.ipynb` | InformationQuantique | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/Physique/InformationQuantique/InfoQuant-02-Trois-Copies-Werner-Distillabilite-Python.ipynb` | InformationQuantique | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/InformationCalcul/InformationTheory/InformationTheory-01-Entropie-Et-Information-Mutuelle.ipynb` | InformationTheory | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/InformationCalcul/InformationTheory/InformationTheory-03-Code-de-Hamming-Et-Decodage-Par-Syndrome.ipynb` | InformationTheory | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/InformationCalcul/InformationTheory/InformationTheory-08-Theorie-De-L-Information-Des-Reseaux.ipynb` | InformationTheory | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/Physique/Integrales/Integrales-01-Triangle-Scalaire-Python.ipynb` | Integrales | python3 | matplotlib==3.10.8, mpmath==1.4.1, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/Physique/Integrales/Integrales-02-Sunrise-Masses-Egales-Python.ipynb` | Integrales | python3 | mpmath==1.4.1 | - |
| `MyIA.AI.Notebooks/Physique/Integrales/Integrales-03-Bulle-Premiere-Divergence-Python.ipynb` | Integrales | python3 | mpmath==1.4.1, pandas==3.0.2 | - |
| `MyIA.AI.Notebooks/Physique/Integrales/Integrales-04-Sunrise-Courbe-Elliptique-Python.ipynb` | Integrales | python3 | mpmath==1.4.1 | - |
| `MyIA.AI.Notebooks/Physique/Jauge/Jauge-01-Theoreme-Noether-Python.ipynb` | Jauge | python3 | matplotlib==3.10.8, numpy==2.4.6, scipy==1.18.0, sympy==1.14.0 | - |
| `MyIA.AI.Notebooks/Physique/Jauge/Jauge-02-Invariance-Jauge-U1-SU2-Python.ipynb` | Jauge | python3 | numpy==2.4.6, sympy==1.14.0 | - |
| `MyIA.AI.Notebooks/Physique/Jauge/Jauge-03-Action-Wilson-Confinement-Python.ipynb` | Jauge | python3 | matplotlib==3.10.8, mpmath==1.4.1, numpy==2.4.6, pandas==3.0.2, sympy==1.14.0 | - |
| `MyIA.AI.Notebooks/Physique/Jauge/Jauge-05-Twisteurs-Euclidiens-Modele-Standard-Python.ipynb` | Jauge | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Analyse/ANALYSE-02b-Entropie-Shannon-Python.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Analyse/ANALYSE-04-PFR-Primitives-Python.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Analyse/ANALYSE-05-KLS-Lean-Python.ipynb` | Lean | python3 | ipython==9.12.0, matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Analyse/ANALYSE-05b-KLS-Song-Zhang-O1.ipynb` | Lean | python3 | matplotlib==3.10.8, numpy==2.4.6, scipy==1.18.0 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Analyse/ANALYSE-06-Sensibilite-2026-Lean-Python.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Analyse/ANALYSE-08-Ramsey-VdW.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Analyse/ANALYSE-09-Tuilage-Aperiodique.ipynb` | Lean | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Analyse/ANALYSE-10-Reflexion-Thurston-Python.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Analyse/ANALYSE-11-Synthese-Transverse-Digestions-Python.ipynb` | Lean | python3 | matplotlib==3.10.8, networkx==3.6.1, numpy==2.4.6, pandas==3.0.2 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Analyse/ANALYSE-12-Comptage-Matching-Lean-Python.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Analyse/ANALYSE-13-Smoothing-Local-Kakeya.ipynb` | Lean | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Analyse/ANALYSE-14-Euler-Navier-Stokes-Python.ipynb` | Lean | python3 | ipython==9.12.0, matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Geometry/Geometry-01-From-Figure-To-Equation.ipynb` | Lean | python3 | matplotlib==3.10.8, numpy==2.4.6, sympy==1.14.0 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Geometry/Geometry-03-Wu-Method-Python.ipynb` | Lean | python3 | sympy==1.14.0 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Geometry/Geometry-03b-Ritt-Decomposition-Python.ipynb` | Lean | python3 | sympy==1.14.0 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Geometry/Geometry-04-DD-AR-Python.ipynb` | Lean | python3 | sympy==1.14.0 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Geometry/Geometry-04b-IMO-AG-30-Python.ipynb` | Lean | python3 | numpy==2.4.6, sympy==1.14.0 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Geometry/Geometry-05-Pont-Formel-Python.ipynb` | Lean | python3 | sympy==1.14.0 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Grothendieck/GROTH-05b-GelfandKirillov-Python.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/JeuDeLaVie/GOL-06-Translateur-Life.ipynb` | Lean | python3-lean | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/JeuDeLaVie/GOL-08-Loi-II-Translateur-Life.ipynb` | Lean | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/JeuDeLaVie/GOL-09-Perplexite-Structurelle-Hashlife.ipynb` | Lean | python3 | pandas==3.0.2 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/JeuDeLaVie/GOL-10-Fractran.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/JeuDeLaVie/GOL-11-Vie-dans-la-vie.ipynb` | Lean | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Langlands/01-formes-modulaires-sl2z-hecke.ipynb` | Lean | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Langlands/02-monstrous-moonshine-invariant-j.ipynb` | Lean | python3 | matplotlib==3.10.8, mpmath==1.4.1, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Langlands/03-chaine-de-modularite-vers-fermat.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Langlands/04-umbral-moonshine-reseaux-niemeier.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Langlands/05-szpiro-pasten-2026.ipynb` | Lean | python3 | sympy==1.14.0 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Langlands/07-chabauty-kim-iwasawa-python.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-12-Sensitivity-Theorem.ipynb` | Lean | python3-lean | matplotlib==3.10.8, networkx==3.6.1, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-13e-Conway-Theoreme-Libre-Arbitre-Lean-Python.ipynb` | Lean | python3-lean | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-13f-Correlation-Bell-Vide-Lean-Python.ipynb` | Lean | python3-lean | matplotlib==3.10.8, numpy==2.4.6, scipy==1.18.0 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-13g-CGLMP-Mesures-Optimales-Lean-Python.ipynb` | Lean | python3-lean | matplotlib==3.10.8, mpmath==1.4.1, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-13h-Maps-PPT-Borne-Lean-Python.ipynb` | Lean | python3-lean | matplotlib==3.10.8, numpy==2.4.6, scipy==1.18.0 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-14-Finiteness-Derivatives.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-15d-Lean-Grothendieck-Visuel-Python.ipynb` | Lean | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-15e-Monodromie-Groupe-Fondamental-Lean-Python.ipynb` | Lean | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-19-Detection-MIMO-Index-Python.ipynb` | Lean | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-19b-Borne-Chernoff-Python.ipynb` | Lean | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-19c-Borne-Bernstein-Python.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-19d-Inference-Bayesian-Beta-Binomial-Python.ipynb` | Lean | python3 | numpy==2.4.6, scipy==1.18.0 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-20-Capstone-Digestions-Tao-Python.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-28-Complex-Structure-S6.ipynb` | Lean | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-37-Capstone-Serre100.ipynb` | Lean | python3-lean | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-38-Capstone-Geometry-Lean-Python.ipynb` | Lean | python3 | numpy==2.4.6, sympy==1.14.0 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-40-Capstone-Langlands-Python.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-41-Capstone-MIMO-Python.ipynb` | Lean | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-42-Independance-Arithmetique-BusyBeaver-Lean.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/MIMO/MIMO-01-Descente-Budget-Lean-Python.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/MIMO/MIMO-04-Capstone-Digestion-Python.ipynb` | Lean | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Noeuds/KNOTS-01-Conway-Proofs-Lean-Python.ipynb` | Lean | python3-lean | matplotlib==3.10.8, numpy==2.4.6, pandas==3.0.2 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Noeuds/KNOTS-03-Companion-Formel-Lean-Python.ipynb` | Lean | python3 | pandas==3.0.2 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Noeuds/KNOTS-05-Dynamique-Tresses-Python.ipynb` | Lean | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Noeuds/KNOTS-06-Empilements-Cercles-Python.ipynb` | Lean | python3 | matplotlib==3.10.8 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Noeuds/KNOTS-07-Feuilletages-Godbillon-Vey-Python.ipynb` | Lean | python3 | matplotlib==3.10.8, numpy==2.4.6, scipy==1.18.0, sympy==1.14.0 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Riemann200/01-zeta-1859.ipynb` | Lean | python3 | matplotlib==3.10.8, mpmath==1.4.1, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Riemann200/02-formule-explicite.ipynb` | Lean | python3 | matplotlib==3.10.8, mpmath==1.4.1 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Riemann200/03-series-rearrangement.ipynb` | Lean | python3 | matplotlib==3.10.8 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Riemann200/04-integrale-riemann.ipynb` | Lean | python3 | matplotlib==3.10.8 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Riemann200/05-sphere-mobius.ipynb` | Lean | python3 | matplotlib==3.10.8 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Riemann200/06-surface-riemann.ipynb` | Lean | python3 | matplotlib==3.10.8 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Riemann200/07-geometrie-riemannienne.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Riemann200/08-riemann-mapping.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Riemann200/09-riemann-lebesgue-fourier.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Riemann200/10-ondes-riemann.ipynb` | Lean | python3 | matplotlib==3.10.8 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Riemann200/11-riemann-roch.ipynb` | Lean | python3 | matplotlib==3.10.8 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Riemann200/12-zeros-simples-ligne-critique.ipynb` | Lean | python3 | mpmath==1.4.1 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Riemann200/12b-grh-ce-quon-peut-calculer.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Riemann200/13-bernoulli-zeta-negatifs-todd.ipynb` | Lean | python3 | matplotlib==3.10.8, mpmath==1.4.1 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Riemann200/14-deux-annonces-grh-meme-jour.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Riemann200/15-espace-tangent-par-les-courbes.ipynb` | Lean | python3 | matplotlib==3.10.8 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100/01-corps-finis-borne-hasse.ipynb` | Lean | python3 | matplotlib==3.10.8 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100/01b-chevalley-warning-divisibilite-solutions.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100/02-valeurs-zeta-multiples-finies.ipynb` | Lean | python3 | matplotlib==3.10.8 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100/03-cohomologie-cech-espaces-finis.ipynb` | Lean | python3 | matplotlib==3.10.8 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100/04-lemme-yoneda-categories-finies.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100/05-table-de-caracteres.ipynb` | Lean | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100/06-bulles-minkowski.ipynb` | Lean | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100/07-zeros-fonctions-l-gaps-gue.ipynb` | Lean | python3 | matplotlib==3.10.8 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100/09-congruences-tau-lacunarite-delta.ipynb` | Lean | python3 | matplotlib==3.10.8 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100/10-empilements-borne-lp-cohn-elkies.ipynb` | Lean | python3 | matplotlib==3.10.8, numpy==2.4.6, scipy==1.18.0 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100/11-corps-quadratiques-reciprocite-quadratique.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100/12-formes-quadratiques-binaires-nombre-classes.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100/13-jacobi-kronecker-reciprocite-II.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100/14-formes-quadratiques-composition-gauss.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100/15-quatre-carres-lagrange.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100/16-fonctions-l-dirichlet-progression-premiers.ipynb` | Lean | python3 | matplotlib==3.10.8 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100/17-chebotarev-frobenius-types-cycles.ipynb` | Lean | python3 | matplotlib==3.10.8 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100/18-discriminant-ramification-critere-dedekind.ipynb` | Lean | python3 | matplotlib==3.10.8 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100/19-arbres-ping-pong-sl2.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100/20-sylow-p-sous-groupes.ipynb` | Lean | python3 | matplotlib==3.10.8 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100/20b-groupes-abeliens-finis.ipynb` | Lean | python3 | matplotlib==3.10.8 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100/20c-cohomologie-groupe-calculee.ipynb` | Lean | python3 | matplotlib==3.10.8 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100/21-operateurs-hecke-formes-modulaires.ipynb` | Lean | python3 | matplotlib==3.10.8 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100/22-vecteurs-witt-frobenius.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100/23-e8-viazovska.ipynb` | Lean | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100/24-hasse-minkowski-principe-local-global.ipynb` | Lean | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100/25-groupe-galois-calcule.ipynb` | Lean | py311-po2028 | matplotlib==3.10.8 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100/26-trois-carres-legendre.ipynb` | Lean | python3 | matplotlib==3.10.8 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100/27-pell-fermat.ipynb` | Lean | python3 | matplotlib==3.10.8 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100/28-inversion-mobius-phi-euler.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100/29-reciprocite-quadratique-legendre.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100/30-fonction-partition-nombres-pentagonaux.ipynb` | Lean | python3 | matplotlib==3.10.8 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100/31-squelette-soule-sl3.ipynb` | Lean | python3 | matplotlib==3.10.8 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/VERIF/VERIF-02-ERC20-Invariant-Companion.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/VERIF/VERIF-05-Coherence-et-Temoin.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/VERIF/VERIF-07-FairBot-Loeb.ipynb` | Lean | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/hmm_alpha_dm_research.ipynb` | ML-Training-Pipeline | python3 | numpy==2.4.6, pandas==3.0.2 | - |
| `MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/m11e_ensemble_research.ipynb` | ML-Training-Pipeline | python3 | matplotlib==3.10.8, numpy==2.4.6, pandas==3.0.2 | - |
| `MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/m12_har_rv_j_research.ipynb` | ML-Training-Pipeline | python3 | matplotlib==3.10.8, numpy==2.4.6, pandas==3.0.2 | - |
| `MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/m15_lstm_rv_research.ipynb` | ML-Training-Pipeline | python3 | matplotlib==3.10.8, numpy==2.4.6, pandas==3.0.2 | - |
| `MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/m3_har_asymmetric_semivariance.ipynb` | ML-Training-Pipeline | python3 | numpy==2.4.6, pandas==3.0.2 | - |
| `MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/m4_dlinear_vol_research.ipynb` | ML-Training-Pipeline | python3 | matplotlib==3.10.8, numpy==2.4.6, pandas==3.0.2 | - |
| `MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/m5_hmm_regime_research.ipynb` | ML-Training-Pipeline | python3 | matplotlib==3.10.8, numpy==2.4.6, pandas==3.0.2 | - |
| `MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/m9_tft_vol_research.ipynb` | ML-Training-Pipeline | python3 | matplotlib==3.10.8, numpy==2.4.6, pandas==3.0.2 | - |
| `MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/research_l4_decision_transformer.ipynb` | ML-Training-Pipeline | python3 | matplotlib==3.10.8, numpy==2.4.6, pandas==3.0.2 | - |
| `MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/research_what_dl_can_predict.ipynb` | ML-Training-Pipeline | python3 | ipython==9.12.0, numpy==2.4.6, pandas==3.0.2 | - |
| `MyIA.AI.Notebooks/QuantConnect/ML-Training-Pipeline/xrp_dt_foldwise_research.ipynb` | ML-Training-Pipeline | python3 | matplotlib==3.10.8, numpy==2.4.6, pandas==3.0.2 | - |
| `MyIA.AI.Notebooks/ML/ML.Net/ML-01-Introduction-Python.ipynb` | ML.Net | python3 | matplotlib==3.10.8, numpy==2.4.6, scikit-learn==1.8.0 | - |
| `MyIA.AI.Notebooks/ML/ML.Net/ML-02-Data-Features-Python.ipynb` | ML.Net | python3 | numpy==2.4.6, pandas==3.0.2, scikit-learn==1.8.0 | - |
| `MyIA.AI.Notebooks/ML/ML.Net/ML-03-Entrainement-AutoML-Python.ipynb` | ML.Net | python3 | matplotlib==3.10.8, numpy==2.4.6, scikit-learn==1.8.0 | - |
| `MyIA.AI.Notebooks/ML/ML.Net/ML-04b-ModelComparison-Validity-Python.ipynb` | ML.Net | python3 | numpy==2.4.6, pandas==3.0.2, scikit-learn==1.8.0, scipy==1.18.0 | - |
| `MyIA.AI.Notebooks/ML/ML.Net/ML-05-TimeSeries-Python.ipynb` | ML.Net | python3 | matplotlib==3.10.8, numpy==2.4.6, pandas==3.0.2, statsmodels==0.14.6 | - |
| `MyIA.AI.Notebooks/ML/ML.Net/ML-05b-Series-Temporelles-Classiques-Python.ipynb` | ML.Net | python3 | matplotlib==3.10.8, numpy==2.4.6, pandas==3.0.2, statsmodels==0.14.6 | - |
| `MyIA.AI.Notebooks/ML/ML.Net/ML-07-Recommendation-Python.ipynb` | ML.Net | python3 | numpy==2.4.6, pandas==3.0.2, scikit-learn==1.8.0 | - |
| `MyIA.AI.Notebooks/ML/ML.Net/ML-07b-SemanticIDs-Recommandation-Python.ipynb` | ML.Net | python3 | numpy==2.4.6, pandas==3.0.2, scikit-learn==1.8.0, scipy==1.18.0 | - |
| `MyIA.AI.Notebooks/ML/ML.Net/ML-07c-Sona-Recommandeur-Generatif-Python.ipynb` | ML.Net | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/ML/ML.Net/ML-08-Clustering-Python.ipynb` | ML.Net | python3 | matplotlib==3.10.8, numpy==2.4.6, scikit-learn==1.8.0 | - |
| `MyIA.AI.Notebooks/ML/ML.Net/ML-09-Anomaly-Detection-Python.ipynb` | ML.Net | python3 | matplotlib==3.10.8, numpy==2.4.6, scikit-learn==1.8.0 | - |
| `MyIA.AI.Notebooks/ML/ML.Net/ML-09b-TSAD-Benchmark-Flaws-Python.ipynb` | ML.Net | python3 | matplotlib==3.10.8, scikit-learn==1.8.0 | - |
| `MyIA.AI.Notebooks/GameTheory/Metajeux/Metajeux-01-Open-Games-Lentilles-Python.ipynb` | Metajeux | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/GameTheory/Metajeux/Metajeux-02-Casser-la-Composition-Python.ipynb` | Metajeux | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/GameTheory/Metajeux/Metajeux-04-Chemin-Minimal-Robinson-Goforth-Python.ipynb` | Metajeux | python3 | - | - |
| `MyIA.AI.Notebooks/GameTheory/Metajeux/Metajeux-05-Temoins-Impossibilite-Python.ipynb` | Metajeux | python3 | - | - |
| `MyIA.AI.Notebooks/GameTheory/Metajeux/Metajeux-06-Chemin-Minimal-3x2-Ordinal-Python.ipynb` | Metajeux | python3 | - | - |
| `MyIA.AI.Notebooks/GameTheory/GameTheory-02c-Travelers-Dilemma-Python.ipynb` | MyIA.AI.Notebooks/GameTheory | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/GameTheory/GameTheory-02d-Epistemique-Connaissance-Commune-Python.ipynb` | MyIA.AI.Notebooks/GameTheory | python3 | - | - |
| `MyIA.AI.Notebooks/GameTheory/GameTheory-02e-IESDS-Rationalisation-Python.ipynb` | MyIA.AI.Notebooks/GameTheory | python3 | numpy==2.4.6, scipy==1.18.0 | - |
| `MyIA.AI.Notebooks/GameTheory/GameTheory-03-Topology2x2-Python.ipynb` | MyIA.AI.Notebooks/GameTheory | python3 | matplotlib==3.10.8, networkx==3.6.1, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/GameTheory/GameTheory-03b-Chambres-Murs-Chemins-Lean-Python.ipynb` | MyIA.AI.Notebooks/GameTheory | python3 | - | - |
| `MyIA.AI.Notebooks/GameTheory/GameTheory-03d-Deux-Especes-de-Fleches-Python.ipynb` | MyIA.AI.Notebooks/GameTheory | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/GameTheory/GameTheory-03e-Meta-Actions-Tarifees-Python.ipynb` | MyIA.AI.Notebooks/GameTheory | python3 | - | - |
| `MyIA.AI.Notebooks/GameTheory/GameTheory-04c-NashExistence-Python.ipynb` | MyIA.AI.Notebooks/GameTheory | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/GameTheory/GameTheory-04d-Marchandage-Asymetrique-Python.ipynb` | MyIA.AI.Notebooks/GameTheory | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/GameTheory/GameTheory-04g-Supermodularite-Python.ipynb` | MyIA.AI.Notebooks/GameTheory | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/GameTheory/GameTheory-04h-Routing-PriceOfAnarchy-Python.ipynb` | MyIA.AI.Notebooks/GameTheory | python3 | - | - |
| `MyIA.AI.Notebooks/GameTheory/GameTheory-04k-Equilibre-Correle-Python.ipynb` | MyIA.AI.Notebooks/GameTheory | python3 | numpy==2.4.6, scipy==1.18.0 | - |
| `MyIA.AI.Notebooks/GameTheory/GameTheory-05c-KKT-Dualite-Lagrangienne-Python.ipynb` | MyIA.AI.Notebooks/GameTheory | python3 | matplotlib==3.10.8, numpy==2.4.6, scipy==1.18.0, sympy==1.14.0 | - |
| `MyIA.AI.Notebooks/GameTheory/GameTheory-06i-Ensembles-Limites-Poincare-Bendixson-Python.ipynb` | MyIA.AI.Notebooks/GameTheory | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/GameTheory/GameTheory-08-CombinatorialGames-Python.ipynb` | MyIA.AI.Notebooks/GameTheory | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/GameTheory/GameTheory-08c-CombinatorialGames-Python.ipynb` | MyIA.AI.Notebooks/GameTheory | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/GameTheory/GameTheory-09b-Commitment-Stackelberg-Python.ipynb` | MyIA.AI.Notebooks/GameTheory | python3 | - | - |
| `MyIA.AI.Notebooks/GameTheory/GameTheory-10-ForwardInduction-SPE-Python.ipynb` | MyIA.AI.Notebooks/GameTheory | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/GameTheory/GameTheory-11c-Global-Games-Python.ipynb` | MyIA.AI.Notebooks/GameTheory | python3 | matplotlib==3.10.8, numpy==2.4.6, scipy==1.18.0 | - |
| `MyIA.AI.Notebooks/GameTheory/GameTheory-11d-Raffinements-Sequentiels-Python.ipynb` | MyIA.AI.Notebooks/GameTheory | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/GameTheory/GameTheory-11e-Global-Games-Python.ipynb` | MyIA.AI.Notebooks/GameTheory | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/GameTheory/GameTheory-11f-Jeux-Globaux-Selection-Equilibre-Python.ipynb` | MyIA.AI.Notebooks/GameTheory | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/GameTheory/GameTheory-12-ReputationGames-Python.ipynb` | MyIA.AI.Notebooks/GameTheory | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/GameTheory/GameTheory-13b-Safe-Subgame-Solving-Python.ipynb` | MyIA.AI.Notebooks/GameTheory | coursia-ml-training | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/GameTheory/GameTheory-13g-Ataraxos-Organe-Natif.ipynb` | MyIA.AI.Notebooks/GameTheory | python3 | matplotlib==3.10.8, pandas==3.0.2 | - |
| `MyIA.AI.Notebooks/GameTheory/GameTheory-13h-Ataraxos-DynamicDamping-Python.ipynb` | MyIA.AI.Notebooks/GameTheory | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/GameTheory/GameTheory-14-DifferentialGames-Python.ipynb` | MyIA.AI.Notebooks/GameTheory | python3 | matplotlib==3.10.8, numpy==2.4.6, scipy==1.18.0 | - |
| `MyIA.AI.Notebooks/GameTheory/GameTheory-14b-Jeux-Repetes-Tournoi-Axelrod-Python.ipynb` | MyIA.AI.Notebooks/GameTheory | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/GameTheory/GameTheory-14c-Jeux-Spatiaux-Cooperation-Python.ipynb` | MyIA.AI.Notebooks/GameTheory | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/GameTheory/GameTheory-15-CooperativeGames-Python.ipynb` | MyIA.AI.Notebooks/GameTheory | python3 | matplotlib==3.10.8, numpy==2.4.6, pandas==3.0.2, scipy==1.18.0 | - |
| `MyIA.AI.Notebooks/GameTheory/GameTheory-15c-CooperativeGames-Python.ipynb` | MyIA.AI.Notebooks/GameTheory | coursia-ml-training | matplotlib==3.10.8, numpy==2.4.6, scipy==1.18.0 | - |
| `MyIA.AI.Notebooks/GameTheory/GameTheory-15d-Shapley-Groupes-Python.ipynb` | MyIA.AI.Notebooks/GameTheory | python3 | matplotlib==3.10.8, networkx==3.6.1, numpy==2.4.6, scipy==1.18.0 | - |
| `MyIA.AI.Notebooks/GameTheory/GameTheory-16-MechanismDesign-Python.ipynb` | MyIA.AI.Notebooks/GameTheory | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/GameTheory/GameTheory-16b-Automated-Mechanism-Design-Python.ipynb` | MyIA.AI.Notebooks/GameTheory | python3 | - | - |
| `MyIA.AI.Notebooks/GameTheory/GameTheory-16c-Extraction-de-Revenu-DSIC-IR-Python.ipynb` | MyIA.AI.Notebooks/GameTheory | python3 | - | - |
| `MyIA.AI.Notebooks/GameTheory/GameTheory-16h-Cooperation-LLM-Python.ipynb` | MyIA.AI.Notebooks/GameTheory | python3 | - | - |
| `MyIA.AI.Notebooks/GameTheory/GameTheory-16i-Appariage-Stable-Gale-Shapley-Python.ipynb` | MyIA.AI.Notebooks/GameTheory | python3 | - | - |
| `MyIA.AI.Notebooks/GameTheory/GameTheory-16j-Screening-Loyer-Information-Python.ipynb` | MyIA.AI.Notebooks/GameTheory | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/GameTheory/GameTheory-16k-Theorie-des-Encheres-Myerson-Python.ipynb` | MyIA.AI.Notebooks/GameTheory | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/GameTheory/GameTheory-17b-Asymmetric-Information-Python.ipynb` | MyIA.AI.Notebooks/GameTheory | python3 | matplotlib==3.10.8, numpy==2.4.6, pandas==3.0.2 | - |
| `MyIA.AI.Notebooks/GameTheory/GameTheory-17e-Bayesian-Persuasion-Python.ipynb` | MyIA.AI.Notebooks/GameTheory | python3 | matplotlib==3.10.8, numpy==2.4.6, scipy==1.18.0 | - |
| `MyIA.AI.Notebooks/GameTheory/GameTheory-17f-Market-to-Balance-Sheet-Python.ipynb` | MyIA.AI.Notebooks/GameTheory | python3 | matplotlib==3.10.8, numpy==2.4.6, pandas==3.0.2 | - |
| `MyIA.AI.Notebooks/GameTheory/GameTheory-18-Capstone-Metajeux-Python.ipynb` | MyIA.AI.Notebooks/GameTheory | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/GameTheory/GameTheory-19-Capstone-Dynamics-Python.ipynb` | MyIA.AI.Notebooks/GameTheory | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/GameTheory/GameTheory-20-Capstone-Coalitions-Python.ipynb` | MyIA.AI.Notebooks/GameTheory | python3 | networkx==3.6.1, numpy==2.4.6, pandas==3.0.2 | - |
| `MyIA.AI.Notebooks/GameTheory/GameTheory-21-Capstone-Choix-Social-Python.ipynb` | MyIA.AI.Notebooks/GameTheory | python3 | - | - |
| `MyIA.AI.Notebooks/GameTheory/GameTheory-22-Jeux-Stochastiques-Shapley-Python.ipynb` | MyIA.AI.Notebooks/GameTheory | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/GameTheory/GameTheory-23-Loopholes-Fiscaux-Python-Lean.ipynb` | MyIA.AI.Notebooks/GameTheory | python3 | - | - |
| `MyIA.AI.Notebooks/IIT/IIT-05-Lentilles-et-Dissociations-Python.ipynb` | MyIA.AI.Notebooks/IIT | pyphi | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/NLP/02_NGrammes_Modeles_De_Langue.ipynb` | MyIA.AI.Notebooks/NLP | coursia-ml-training | matplotlib==3.10.8, nltk==3.9.4 | - |
| `MyIA.AI.Notebooks/NLP/04_PCFG_CYK_Parsing.ipynb` | MyIA.AI.Notebooks/NLP | coursia-ml-training | matplotlib==3.10.8, nltk==3.9.4, pandas==3.0.2 | - |
| `MyIA.AI.Notebooks/NLP/06-Recherche-Information-TFIDF-BM25.ipynb` | MyIA.AI.Notebooks/NLP | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/NLP/07-Vecteurs-de-Mots-Coocc-PPMI-SVD.ipynb` | MyIA.AI.Notebooks/NLP | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/NLP/08-Word2Vec-CBOW-SkipGram.ipynb` | MyIA.AI.Notebooks/NLP | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/NLP/09-FastText-Subword-Vectors.ipynb` | MyIA.AI.Notebooks/NLP | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/NLP/10-Classement-Texte-NaiveBayes-FromScratch.ipynb` | MyIA.AI.Notebooks/NLP | python3 | scikit-learn==1.8.0 | - |
| `MyIA.AI.Notebooks/NLP/11-Classement-Texte-RegressionLogistique-FromScratch.ipynb` | MyIA.AI.Notebooks/NLP | python3 | numpy==2.4.6, scikit-learn==1.8.0 | - |
| `MyIA.AI.Notebooks/RL/RL-04-Bandits-Manchots-Python.ipynb` | MyIA.AI.Notebooks/RL | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/RL/RL-07b-Sur-Generalisation-Climbing-Game-Python.ipynb` | MyIA.AI.Notebooks/RL | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/RL/RL-08-Dyna-Q-Planification-Python.ipynb` | MyIA.AI.Notebooks/RL | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/RL/RL-09-RL-Offline-Behavior-Cloning-Python.ipynb` | MyIA.AI.Notebooks/RL | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/RL/RL-10-Reward-Shaping-Curriculum-Python.ipynb` | MyIA.AI.Notebooks/RL | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/RL/RL-11-POMDP-Croyances-Python.ipynb` | MyIA.AI.Notebooks/RL | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/RL/RL-14-RL-Hierarchique-Options-Python.ipynb` | MyIA.AI.Notebooks/RL | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/RL/RL-16-Dream-RSI-Python.ipynb` | MyIA.AI.Notebooks/RL | python3 | matplotlib==3.10.8 | - |
| `MyIA.AI.Notebooks/RL/RL-17-Reward-Tampering-Python.ipynb` | MyIA.AI.Notebooks/RL | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/RL/RL-20-Capstone-PostTraining-Python.ipynb` | MyIA.AI.Notebooks/RL | python3 | - | - |
| `MyIA.AI.Notebooks/Sudoku/Sudoku-01-Backtracking-Python.ipynb` | MyIA.AI.Notebooks/Sudoku | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/Sudoku/Sudoku-02-DancingLinks-Python.ipynb` | MyIA.AI.Notebooks/Sudoku | python3 | - | - |
| `MyIA.AI.Notebooks/Sudoku/Sudoku-06-AIMA-CSP-Python.ipynb` | MyIA.AI.Notebooks/Sudoku | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/Sudoku/Sudoku-07-Norvig-Python.ipynb` | MyIA.AI.Notebooks/Sudoku | python3 | - | - |
| `MyIA.AI.Notebooks/Sudoku/Sudoku-08-HumanStrategies-Python.ipynb` | MyIA.AI.Notebooks/Sudoku | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/Sudoku/Sudoku-09-GraphColoring-Python.ipynb` | MyIA.AI.Notebooks/Sudoku | python3 | networkx==3.6.1 | - |
| `MyIA.AI.Notebooks/Sudoku/Sudoku-14-BDD-Python.ipynb` | MyIA.AI.Notebooks/Sudoku | python3 | - | - |
| `MyIA.AI.Notebooks/Sudoku/Sudoku-18b-Statistical-Comparison-Python.ipynb` | MyIA.AI.Notebooks/Sudoku | python3 | matplotlib==3.10.8, numpy==2.4.6, scipy==1.18.0 | - |
| `MyIA.AI.Notebooks/Physique/Numerique/Numerique-01-Burgers-Volumes-Finis-Python.ipynb` | Numerique | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/Physique/Numerique/Numerique-02-Maxwell-Relativiste-Volumes-Finis-C.ipynb` | Numerique | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/Search/Part1-Foundations/Search-01-StateSpace.ipynb` | Part1-Foundations | python3 | matplotlib==3.10.8, networkx==3.6.1, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/Search/Part1-Foundations/Search-02-Uninformed.ipynb` | Part1-Foundations | python3 | matplotlib==3.10.8, networkx==3.6.1, numpy==2.4.6, pandas==3.0.2 | - |
| `MyIA.AI.Notebooks/Search/Part1-Foundations/Search-02b-NetworkX.ipynb` | Part1-Foundations | python3 | matplotlib==3.10.8, networkx==3.6.1, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/Search/Part1-Foundations/Search-02d-RRT-Recherche-Continue.ipynb` | Part1-Foundations | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/Search/Part1-Foundations/Search-03-Informed.ipynb` | Part1-Foundations | python3 | matplotlib==3.10.8, networkx==3.6.1, numpy==2.4.6, pandas==3.0.2 | - |
| `MyIA.AI.Notebooks/Search/Part1-Foundations/Search-03b-PatternDatabases.ipynb` | Part1-Foundations | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/Search/Part1-Foundations/Search-03c-LimitedDiscrepancySearch.ipynb` | Part1-Foundations | python3 | - | - |
| `MyIA.AI.Notebooks/Search/Part1-Foundations/Search-03d-WeightedAstar.ipynb` | Part1-Foundations | python3 | - | - |
| `MyIA.AI.Notebooks/Search/Part1-Foundations/Search-03f-Reparer-Localement-Sous-Garantie-Python.ipynb` | Part1-Foundations | python3 | - | - |
| `MyIA.AI.Notebooks/Search/Part1-Foundations/Search-04-LocalSearch.ipynb` | Part1-Foundations | python3 | matplotlib==3.10.8, numpy==2.4.6, pandas==3.0.2 | - |
| `MyIA.AI.Notebooks/Search/Part1-Foundations/Search-06-AdversarialSearch.ipynb` | Part1-Foundations | python3 | matplotlib==3.10.8, numpy==2.4.6, pandas==3.0.2 | - |
| `MyIA.AI.Notebooks/Search/Part1-Foundations/Search-08-DancingLinks.ipynb` | Part1-Foundations | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/Search/Part1-Foundations/Search-09d-BeckFiala-Lean-Python.ipynb` | Part1-Foundations | python3 | matplotlib==3.10.8 | - |
| `MyIA.AI.Notebooks/Search/Part1-Foundations/Search-11d-Descente-Sous-Budget.ipynb` | Part1-Foundations | python3 | - | - |
| `MyIA.AI.Notebooks/Search/Part1-Foundations/Search-12-BranchAndBound-Borne-LP-Python.ipynb` | Part1-Foundations | python3 | matplotlib==3.10.8, numpy==2.4.6, scipy==1.18.0 | - |
| `MyIA.AI.Notebooks/Search/Part1-Foundations/Search-12a-Composer-Regards.ipynb` | Part1-Foundations | python3 | matplotlib==3.10.8, numpy==2.4.6, pandas==3.0.2 | - |
| `MyIA.AI.Notebooks/Search/Part1-Foundations/Search-13-AutomaticGroups-WordProblem.ipynb` | Part1-Foundations | python3 | - | - |
| `MyIA.AI.Notebooks/Search/Part1-Foundations/Search-13a-Traverser-Murs-Certifies.ipynb` | Part1-Foundations | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/Search/Part2-CSP/CSP-09-Distributed-Python.ipynb` | Part2-CSP | python3 | matplotlib==3.10.8, networkx==3.6.1, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/Search/Part3-Cas-pratiques/App-07-Wordle-Python.ipynb` | Part3-Cas-pratiques | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/Search/Part3-Cas-pratiques/App-12-ConnectFour-Python.ipynb` | Part3-Cas-pratiques | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/Search/Part3-Cas-pratiques/App-14-ConnectFour-Adversarial-Python.ipynb` | Part3-Cas-pratiques | python3 | matplotlib==3.10.8, numpy==2.4.6, pandas==3.0.2 | - |
| `MyIA.AI.Notebooks/Search/Part3-Cas-pratiques/App-22-AlgorithmSelection-Python.ipynb` | Part3-Cas-pratiques | python3 | matplotlib==3.10.8, numpy==2.4.6, pandas==3.0.2 | - |
| `MyIA.AI.Notebooks/Search/Part3-Cas-pratiques/App-33-RushHour-Admissible-Astar-Python.ipynb` | Part3-Cas-pratiques | python3 | - | - |
| `MyIA.AI.Notebooks/Search/Part3-Cas-pratiques/App-34-15Puzzle-Admissible-Astar-Python.ipynb` | Part3-Cas-pratiques | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/Search/Part4-Metaheuristics/MGS-17b-Empirical-Algorithm-Selection.ipynb` | Part4-Metaheuristics | python3 | numpy==2.4.6, pandas==3.0.2 | - |
| `MyIA.AI.Notebooks/Search/Part4-Metaheuristics/MGS-20-Langage-de-Composition.ipynb` | Part4-Metaheuristics | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/Search/Part5-Frontieres/Frontieres-06-LearningToBranch-Generalization-Audit-Python.ipynb` | Part5-Frontieres | python3 | numpy==2.4.6, pandas==3.0.2, scikit-learn==1.8.0 | - |
| `MyIA.AI.Notebooks/Search/Part5-Frontieres/Frontieres-11-Abstraction-Dette-ShortestPath-Python.ipynb` | Part5-Frontieres | python3 | matplotlib==3.10.8 | - |
| `MyIA.AI.Notebooks/Search/Part5-Frontieres/Frontieres-12-WordProblem-Automata-Python.ipynb` | Part5-Frontieres | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/SymbolicAI/Planners/02-Classical/Planners-05c-Differentiel-Atteignabilite-Python.ipynb` | Planners | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Planners/04-NeuroSymbolic/Planners-11-Unified-Planning-Python.ipynb` | Planners | python3 | - | unified_planning |
| `MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles/AI-Engine-WordPress/03-Functional/03-2-Forms/auditer-un-formulaire-conditionnel.ipynb` | Plateformes-Conversationnelles | python3 | - | - |
| `MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles/Open-WebUI/Playwright-OWUI/00-Parcours-QA-OWUI.ipynb` | Plateformes-Conversationnelles | python3 | - | - |
| `MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles/Open-WebUI/Playwright-OWUI/01-decouverte/01-Decouverte-QA-OWUI.ipynb` | Plateformes-Conversationnelles | python3 | - | - |
| `MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles/Open-WebUI/Playwright-OWUI/02-navigation-authentification/02-Navigation-Auth-QA-OWUI.ipynb` | Plateformes-Conversationnelles | python3 | - | - |
| `MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles/Open-WebUI/Playwright-OWUI/03-chat-streaming/03-Chat-Streaming-QA-OWUI.ipynb` | Plateformes-Conversationnelles | python3 | - | - |
| `MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles/Open-WebUI/Playwright-OWUI/04-rag-tools-avances/04-RAG-Tools-QA-OWUI.ipynb` | Plateformes-Conversationnelles | python3 | - | - |
| `MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles/Open-WebUI/Playwright-OWUI/05-multi-tenant-ci/05-Multi-Tenant-CI-QA-OWUI.ipynb` | Plateformes-Conversationnelles | python3 | - | - |
| `MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles/Open-WebUI/Playwright-OWUI/06-nouveautes-v0.10/06-Nouveautes-v0.10-QA-OWUI.ipynb` | Plateformes-Conversationnelles | python3 | - | - |
| `MyIA.AI.Notebooks/GenAI/PostTraining/PT_01_intro_post_training.ipynb` | PostTraining | python3 | matplotlib==3.10.8, numpy==2.4.6, pandas==3.0.2 | - |
| `MyIA.AI.Notebooks/GenAI/PostTraining/PT_06_eval_comparative.ipynb` | PostTraining | coursia-ml-training | matplotlib==3.10.8, numpy==2.4.6, pandas==3.0.2 | - |
| `MyIA.AI.Notebooks/GenAI/PostTraining/PT_18_laya_ablation_distillation.ipynb` | PostTraining | python3 | numpy==2.4.6, pandas==3.0.2, scipy==1.18.0 | - |
| `MyIA.AI.Notebooks/GenAI/PostTraining/PT_19_stratification_inter_tailles.ipynb` | PostTraining | python3 | numpy==2.4.6, pandas==3.0.2 | - |
| `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-06b-Derivatives-Valuation-From-Scratch.ipynb` | Python | python3 | matplotlib==3.10.8, numpy==2.4.6, scipy==1.18.0 | - |
| `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-12b-Backtest-Validity.ipynb` | Python | python3 | matplotlib==3.10.8, numpy==2.4.6, scipy==1.18.0 | - |
| `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-29-Derivatives-Valuation.ipynb` | Python | python3 | numpy==2.4.6, scipy==1.18.0 | - |
| `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-35-RL-Portfolio-Construction.ipynb` | Python | python3 | matplotlib==3.10.8, numpy==2.4.6, pandas==3.0.2 | - |
| `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-Cloud-03b-RiskParity-Composite.ipynb` | Python | python3 | - | - |
| `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-Cloud-04-MeanReversion.ipynb` | Python | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-Cloud-06-PCA-StatArb.ipynb` | Python | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-Cloud-07-TemporalCNN.ipynb` | Python | python3 | numpy==2.4.6, scipy==1.18.0 | - |
| `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-Cloud-08-ValueFactor-ZScore.ipynb` | Python | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-Cloud-09-OptionWheel.ipynb` | Python | python3 | - | - |
| `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-Cloud-11-RegimeSwitching.ipynb` | Python | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-Cloud-12-SectorRotation-Momentum.ipynb` | Python | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-Cloud-13-VolTargeting.ipynb` | Python | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-Cloud-14-DualMomentum.ipynb` | Python | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-Dataset-Workflow.ipynb` | Python | python3 | matplotlib==3.10.8, pandas==3.0.2 | - |
| `MyIA.AI.Notebooks/CaseStudies/Reseau-Electrique-Intelligent/student/Reseau-Electrique-Intelligent-Python.ipynb` | Reseau-Electrique-Intelligent | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/GenAI/Security/Oversight/Backdoor-Code-From-Scratch.ipynb` | Security | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/GenAI/Security/Oversight/Oversight-Scaling-Laws-Analytics.ipynb` | Security | python3 | numpy==2.4.6, scipy==1.18.0 | - |
| `MyIA.AI.Notebooks/GenAI/Security/Oversight/Oversight-Scaling-Laws-Statistics.ipynb` | Security | python3 | matplotlib==3.10.8, numpy==2.4.6, scipy==1.18.0 | - |
| `MyIA.AI.Notebooks/GenAI/Security/Oversight/Oversight-Scaling-Laws-Wargames.ipynb` | Security | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/GenAI/SemanticKernel/Notebook-Template.ipynb` | SemanticKernel | python3 | - | - |
| `MyIA.AI.Notebooks/GenAI/SemanticKernel/Workbook-Template-Python.ipynb` | SemanticKernel | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/SemanticWeb/SW-16-ProofCarryingOntologies-Python.ipynb` | SemanticWeb | python3 | - | - |
| `MyIA.AI.Notebooks/InformationCalcul/SignalProcessing/SignalProcessing-01-Le-Signal-Dans-Le-Domaine-Frequentiel.ipynb` | SignalProcessing | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/InformationCalcul/SignalProcessing/SignalProcessing-02-Convolution-Et-Filtrage-Python.ipynb` | SignalProcessing | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/InformationCalcul/SignalProcessing/SignalProcessing-03-Quantification-Python.ipynb` | SignalProcessing | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/InformationCalcul/SignalProcessing/SignalProcessing-04-Le-Signal-Dans-Le-Canal-Python.ipynb` | SignalProcessing | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/SymbolicAI/SmartContracts/00-Foundations/SC-00-Cypherpunk-Origins-Python.ipynb` | SmartContracts | python3 | pycryptodome==3.23.0 | - |
| `MyIA.AI.Notebooks/SymbolicAI/SmartContracts/00-Foundations/SC-01-Setup-Foundry-Python.ipynb` | SmartContracts | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/SmartContracts/02-Solidity-Advanced/SC-08b-MEV-LP-Python.ipynb` | SmartContracts | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/SymbolicAI/SmartContracts/02-Solidity-Advanced/SC-7b-ERC20-Lean-Verification-Companion.ipynb` | SmartContracts | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/SmartContracts/03-Foundry-Testing/SC-12-Foundry-Testing-Python.ipynb` | SmartContracts | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/SmartContracts/03-Foundry-Testing/SC-13-Fuzz-Invariants-Python.ipynb` | SmartContracts | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/SmartContracts/04-Privacy-Cryptography/SC-15-Zero-Knowledge-Proofs-Python.ipynb` | SmartContracts | python3 | pycryptodome==3.23.0 | - |
| `MyIA.AI.Notebooks/SymbolicAI/SmartContracts/05-Alternative-Chains/SC-21-Move-Sui-Python.ipynb` | SmartContracts | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/SmartContracts/05-Alternative-Chains/SC-22-Solana-Anchor-Python.ipynb` | SmartContracts | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/SmartContracts/06-Real-World/SC-23-Cross-Chain-Python.ipynb` | SmartContracts | python3 | - | - |
| `MyIA.AI.Notebooks/GameTheory/SocialChoice/ChoixSocial-01c-Paradoxe-NonParticipation-NoShow-Python.ipynb` | SocialChoice | python3 | matplotlib==3.10.8 | - |
| `MyIA.AI.Notebooks/GameTheory/SocialChoice/ChoixSocial-02-Stable-Marriage-Gale-Shapley-Python.ipynb` | SocialChoice | python3 | - | - |
| `MyIA.AI.Notebooks/GameTheory/SocialChoice/ChoixSocial-03-Voting-Methods-Python.ipynb` | SocialChoice | python3 | matplotlib==3.10.8, networkx==3.6.1, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/GameTheory/SocialChoice/ChoixSocial-05-Gibbard-Satterthwaite-Python.ipynb` | SocialChoice | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/GameTheory/SocialChoice/ChoixSocial-06-Mobius-Aggregation-Pouvoir-Manipulation-Python.ipynb` | SocialChoice | python3 | - | - |
| `MyIA.AI.Notebooks/GameTheory/SocialChoice/ChoixSocial-07-Committees-Core-Python.ipynb` | SocialChoice | python3 | matplotlib==3.10.8, numpy==2.4.6, scipy==1.18.0 | - |
| `MyIA.AI.Notebooks/BioMedecine/Structures/Structures-01-Liaisons-Hydrogene-Squelette-Proteique-Python.ipynb` | Structures | python3 | matplotlib==3.10.8, numpy==2.4.6, scipy==1.18.0 | - |
| `MyIA.AI.Notebooks/SymbolicAI/SymbolicLearning/SL-01-LogicalLearning-Python.ipynb` | SymbolicLearning | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/SymbolicLearning/SL-02-KnowledgeBasedLearning-Python.ipynb` | SymbolicLearning | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/SymbolicLearning/SL-03-RelevanceLearning-Python.ipynb` | SymbolicLearning | python3 | numpy==2.4.6, scikit-learn==1.8.0 | - |
| `MyIA.AI.Notebooks/SymbolicAI/SymbolicLearning/SL-10-ActiveAutomataLearning-Python.ipynb` | SymbolicLearning | python3 | matplotlib==3.10.8 | - |
| `MyIA.AI.Notebooks/SymbolicAI/SymbolicLearning/SL-12b-SpectralLogicSynthesis-Python.ipynb` | SymbolicLearning | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/SymbolicAI/SymbolicLearning/SL-12c-PavlovDLS-Reproduction-Python.ipynb` | SymbolicLearning | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/SymbolicAI/SymbolicLearning/SL-12c-PavlovDLS-Reproduction-output-Python.ipynb` | SymbolicLearning | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/GenAI/Texte/10g_Speculative_Decoding.ipynb` | Texte | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/GenAI/Texte/10h_Roofline_Memory_Bandwidth.ipynb` | Texte | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/GenAI/Texte/14b_Paginated_Memory-Python.ipynb` | Texte | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Tweety/Tweety-02f-Modal-Zoo-Lean-Python.ipynb` | Tweety | python3 | matplotlib==3.10.8 | - |
| `MyIA.AI.Notebooks/GenAI/Vibe-Coding/Claude-Code/notebooks/01-Claude-CLI-Bases.ipynb` | Vibe-Coding | python3 | - | - |
| `MyIA.AI.Notebooks/GenAI/Vibe-Coding/Claude-Code/notebooks/02-Claude-CLI-Sessions.ipynb` | Vibe-Coding | python3 | - | - |
| `MyIA.AI.Notebooks/GenAI/Vibe-Coding/Claude-Code/notebooks/03-Claude-CLI-References.ipynb` | Vibe-Coding | python3 | - | - |
| `MyIA.AI.Notebooks/GenAI/Vibe-Coding/Claude-Code/notebooks/04-Claude-CLI-Agents.ipynb` | Vibe-Coding | python3 | - | - |
| `MyIA.AI.Notebooks/GenAI/Vibe-Coding/Claude-Code/notebooks/05-Claude-CLI-Automatisation.ipynb` | Vibe-Coding | python3 | - | - |
| `MyIA.AI.Notebooks/GenAI/Video/01-Foundation/01-1b-Video-Slideshow-Bonus.ipynb` | Video | python3 | imageio==2.37.3, matplotlib==3.10.8, numpy==2.4.6, pillow==12.2.0 | - |
| `MyIA.AI.Notebooks/GenAI/Video/02-Advanced/02-6-Video-Architecture-Licensing.ipynb` | Video | python3 | - | - |
| `MyIA.AI.Notebooks/GenAI/Video/02-Advanced/02-8-PAN2-Modele-du-Monde-GLP.ipynb` | Video | python3 | - | - |
| `docker-configurations/notebook-runner/witness/witness-global-313.ipynb` | docker-configurations/notebook-runner | global-3.13 | - | - |
| `docker-configurations/notebook-runner/witness/witness-python3.ipynb` | docker-configurations/notebook-runner | python3 | numpy==2.4.6, pandas==3.0.2 | - |
| `MyIA.AI.Notebooks/QuantConnect/kelly_lean/Kelly_companion-Cotes-Dynamiques-Python.ipynb` | kelly_lean | - | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/QuantConnect/kelly_lean/Kelly_companion-Fractional-Python.ipynb` | kelly_lean | - | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/QuantConnect/kelly_lean/Kelly_companion-Multi-Issue-Python.ipynb` | kelly_lean | - | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/QuantConnect/kelly_lean/Kelly_companion-Optimist-Bias-Python.ipynb` | kelly_lean | - | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/QuantConnect/kelly_lean/Kelly_companion-Python.ipynb` | kelly_lean | python3 | matplotlib==3.10.8, numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/Congress-Trades-Copy/research.ipynb` | projects | python3 | - | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/Framework_Composite_TrendWeather/quantbook.ipynb` | projects | python3 | numpy==2.4.6, pandas==3.0.2 | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/Research-Executor/research.ipynb` | projects | python3 | - | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/Research-Executor/runner.ipynb` | projects | python3 | - | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/_docs/qc_top4_oos_extension.ipynb` | projects | python3 | pandas==3.0.2 | - |
| `MyIA.AI.Notebooks/QuantConnect/research/intraday_volume_periodicity.ipynb` | research | python3 | numpy==2.4.6 | - |
| `MyIA.AI.Notebooks/QuantConnect/research/research_idio_vol_anomaly.ipynb` | research | python3 | numpy==2.4.6, pandas==3.0.2, statsmodels==0.14.6 | - |
| `MyIA.AI.Notebooks/QuantConnect/research/research_quality_lowvol.ipynb` | research | python3 | numpy==2.4.6, pandas==3.0.2 | - |
| `MyIA.AI.Notebooks/QuantConnect/research/research_rl_intro.ipynb` | research | python3 | matplotlib==3.10.8, numpy==2.4.6, pandas==3.0.2 | - |
| `MyIA.AI.Notebooks/QuantConnect/research/research_rl_ppo.ipynb` | research | python3 | matplotlib==3.10.8, numpy==2.4.6, pandas==3.0.2 | - |
| `scripts/notebook_tools/verify_runtime_smoke.ipynb` | scripts/notebook_tools | python3 | - | - |

## Refuses : motifs par serie

Le detail **carnet par carnet** des refus (motif et element declencheur) est dans le
fichier `pyodide-refus.tsv`, une ligne par carnet refuse.

| Serie | Motifs rencontres | Imports absents (les plus frequents) |
|---|---|---|
| 00-GenAI-Environment | cle, gpu, import_absent, reseau, suffisance | psutil (1) |
| 3D | gpu, reseau, suffisance | - |
| Applications | gpu, import_absent | pyro (1), pyro.distributions (1), pyro.distributions.util (1), pyro.infer.abstract_infer (1), pyro.poutine (1) |
| ArgumentAnalysis | cle, gpu, import_absent, reseau, suffisance | jpype (6), java.util (2), spacy (2), argumentation_analysis.plugins.fallacy_workflow_plugin (1), org.tweetyproject.arg.aspic.ruleformulagenerator (1), org.tweetyproject.arg.aspic.syntax (1) |
| Audio | cle, gpu, import_absent, reseau, suffisance | torchaudio (9), audiocraft.models (3), chatterbox.tts (2), MIDI (1), TTS.api (1), acestep.pipeline_ace_step (1) |
| CaseStudies | cle, suffisance | - |
| Causalite | gpu, reseau, suffisance | - |
| Coalitions | import_absent, suffisance | pulp (1), z3 (1) |
| Complexity | import_absent, suffisance | stim (1) |
| Compression | gpu, suffisance | - |
| DataScienceWithAgents | cle, gpu, import_absent, reseau, suffisance | torchvision (14), cvxpy (4), torchvision.datasets (4), pywt (3), lime.lime_tabular (2), shap (2) |
| DecisionTheory | suffisance | - |
| Diagnostic-Medical | import_absent, suffisance | z3 (2) |
| Dynamics | cle, reseau | - |
| FallacyDetection | import_absent, reseau, suffisance | fallacy_detection (1) |
| FineTuning | gpu, import_absent, suffisance | torchvision (4), bitsandbytes (1) |
| ICT-Series | cle, gpu, reseau, suffisance | - |
| Image | cle, gpu, import_absent, reseau, suffisance | CLIP_.clip (1), calculate_metrics (1), clip (1), dnnlib (1), generate_images (1), guided_diffusion.script_util (1) |
| Jauge | gpu | - |
| Lean | cle, gpu, import_absent, reseau, suffisance | snappy (3), Analysis.Section_9_7 (1), Converse (1), Conway.Angel (1), Conway.Life (1), Conway.Life.Oscillators (1) |
| ML-Training-Pipeline | import_absent, suffisance | hmmlearn (1) |
| ML.Net | gpu, import_absent, suffisance | onnx (1), shap (1) |
| Metajeux | gpu, import_absent | Abstraction (1) |
| MyIA.AI.Notebooks/GameTheory | cle, gpu, import_absent, reseau, suffisance | pyspiel (5), open_spiel.python (2), open_spiel.python.algorithms (2), humour_banc.organ (1), pulp (1), z3 (1) |
| MyIA.AI.Notebooks/IIT | suffisance | - |
| MyIA.AI.Notebooks/NLP | import_absent, suffisance | hmmlearn (1), hmmlearn.hmm (1), seqeval.metrics (1), spacy (1) |
| MyIA.AI.Notebooks/Probas | suffisance | - |
| MyIA.AI.Notebooks/RL | gpu, suffisance | - |
| MyIA.AI.Notebooks/Sudoku | cle, gpu, import_absent, reseau, suffisance | ortools.sat.python (2), z3 (2), dd.autoref (1), jpype (1), jpype.imports (1), jpype.types (1) |
| NotionsInteractives | suffisance | - |
| Part1-Foundations | cle, import_absent, reseau, suffisance | cvxpy (2), ortools.sat.python (2), z3 (2), automata.fa.dfa (1), automata.fa.nfa (1), open_spiel.python.algorithms (1) |
| Part2-CSP | cle, import_absent | ortools.sat.python (6), pychoco (4), constraint (2), z3 (1) |
| Part3-Cas-pratiques | import_absent, suffisance | ortools.sat.python (14), ortools.constraint_solver (3), __main__ (1), constraint (1), cvxpy (1), ortools (1) |
| Part5-Frontieres | import_absent | ortools.sat.python (9), ortools (3), pulp (2), ortools.linear_solver (1) |
| Planification-Oncologie | gpu, import_absent, suffisance | ortools.sat.python (2), pyro (2), pyro.distributions (2), pyro.infer (2), pyro.optim (2) |
| Planners | cle, gpu, import_absent, reseau, suffisance | ortools.sat.python (3), ortools.constraint_solver (1), ortools.sat.python.cp_model (1), up_fast_downward (1) |
| Plateformes-Conversationnelles | cle, import_absent, reseau, suffisance | playwright.sync_api (2) |
| PostTraining | cle, gpu, import_absent, reseau, suffisance | z3 (8), rewardspy (5), rewardspy.integrations (4), tokenizers (2), rewardspy.store (1) |
| PyMC | import_absent, suffisance | opentelemetry (1), opentelemetry.sdk (1), opentelemetry.sdk.trace (1), opentelemetry.sdk.trace.export (1), opentelemetry.sdk.trace.export.in_memory_span_exporter (1) |
| Python | cle, gpu, import_absent, reseau, suffisance | AlgorithmImports (40), Portfolio.MeanVarianceOptimizationPortfolioConstructionModel (1), hmmlearn (1) |
| RAG-et-Memoire-Semantique | cle, gpu, import_absent, reseau, suffisance | faiss (1), pypdfium2 (1), tokenizers (1) |
| Reseau-Electrique-Intelligent | import_absent | ortools.sat.python (1) |
| SMT | import_absent, suffisance | z3 (24) |
| Security | cle, gpu, reseau, suffisance | - |
| SemanticKernel | cle, import_absent, reseau, suffisance | System (1), System.IO (1), System.Reflection (1), a2a (1), a2a.client (1), a2a.helpers.proto_helpers (1) |
| SemanticWeb | cle, import_absent, reseau, suffisance | owlready2 (3), jdk4py (1), reasonable (1) |
| SmartContracts | cle, import_absent, reseau, suffisance | solcx (16), xrpl (2), xrpl.models.transactions (2), xrpl.utils (2), bitcoin (1), bitcoin.core (1) |
| SocialChoice | import_absent, suffisance | z3 (4), pysat.solvers (2), pysat.formula (1) |
| SymbolicLearning | cle, gpu, import_absent, reseau, suffisance | janus_swi (3), popper (2), popper.loop (2), popper.util (2), aifeynman (1), lernd.classes (1) |
| Texte | cle, gpu, import_absent, reseau, suffisance | __main__ (1), bitsandbytes (1), jevlike (1), jevlike.data (1), jevlike.model (1), jevlike.train (1) |
| Tweety | import_absent, reseau, suffisance | jpype (16), jpype.types (14), jpype.imports (11), java.util (10), org.tweetyproject.arg.dung.syntax (8), org.tweetyproject.logics.pl.syntax (8) |
| Vibe-Coding | suffisance | - |
| Video | cle, gpu, import_absent, reseau, suffisance | basicsr.archs.rrdbnet_arch (2), bitsandbytes (2), decord (2), ffmpeg (1), imageio_ffmpeg (1) |
| _research | cle, gpu, reseau, suffisance | - |
| gateway | import_absent, suffisance | kernel_gateway (1) |
| partner-course-quant-trading | import_absent, suffisance | AlgorithmImports (5) |
| projects | gpu, import_absent, reseau, suffisance | AlgorithmImports (66) |
| research | gpu, import_absent, suffisance | AlgorithmImports (4) |

Les motifs **se cumulent** : un carnet refuse pour une cle d'API et pour un import
absent compte dans les deux colonnes de la table par serie.

