# Eligibilite Pyodide (JupyterLite) des carnets Python

<!-- Genere par scripts/notebook_tools/pyodide_eligibility.py -- ne pas editer a la main. -->

Perimetre : carnets Python suivis par git, hors `_output`, `_en` et `_archive`.
La famille Python se lit sur la langue declaree (`language_info.name`), le nom du
noyau ne servant que de repli : un carnet sans langue ni noyau Python n'est pas
compte -- le census ne suppose pas Python par defaut. Le compte d'une serie peut
donc etre inferieur au nombre de fichiers `.ipynb` qu'elle contient.
Census : **1472** carnets Python, **153** eligibles, **1319** refuses.

Source de verite des paquets : `pyodide-lock.json` (metadonnees absentes ; ? paquets),
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

Lock de reference : `None` (metadonnees absentes, ? paquets).

Les **noms** des variables d'environnement ne sont pas publies : un nom qui ressemble
a une cle (`*_API_KEY`) fait echouer le scanner de secrets du depot, alors que le nom
seul n'est pas un secret. Le detail des refus (`pyodide-refus.tsv`) publie donc le
**nombre** de variables detectees (`cle=N`), pas leurs noms ; les noms restent
accessibles en local avec `--detail-cle` (sortie a ne pas committer).

## Table par serie

| Serie | Carnets Python | Eligibles | Refuses | dont GPU | dont cle | dont reseau | dont import absent | dont suffisance |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| 00-GenAI-Environment | 7 | 0 | 7 | 1 | 4 | 7 | 6 | 4 |
| 3D | 10 | 0 | 10 | 7 | 0 | 1 | 10 | 0 |
| AgentSystems | 2 | 2 | 0 | 0 | 0 | 0 | 0 | 0 |
| Applications | 10 | 0 | 10 | 1 | 0 | 0 | 10 | 0 |
| ArgumentAnalysis | 40 | 15 | 25 | 1 | 7 | 8 | 24 | 6 |
| Audio | 51 | 1 | 50 | 29 | 21 | 18 | 50 | 31 |
| Automata | 1 | 1 | 0 | 0 | 0 | 0 | 0 | 0 |
| CaseStudies | 4 | 0 | 4 | 0 | 4 | 0 | 4 | 1 |
| Causalite | 12 | 0 | 12 | 1 | 0 | 1 | 12 | 6 |
| Chaines | 12 | 7 | 5 | 0 | 0 | 0 | 5 | 0 |
| Coalitions | 4 | 0 | 4 | 0 | 0 | 0 | 4 | 1 |
| Complexity | 28 | 8 | 20 | 0 | 0 | 0 | 19 | 3 |
| Compression | 13 | 1 | 12 | 1 | 0 | 0 | 12 | 0 |
| Constructeur | 1 | 0 | 1 | 0 | 0 | 0 | 1 | 0 |
| DataScienceWithAgents | 110 | 5 | 105 | 45 | 5 | 3 | 101 | 2 |
| DecisionTheory | 15 | 0 | 15 | 0 | 0 | 0 | 15 | 1 |
| Diagnostic-Medical | 2 | 0 | 2 | 0 | 0 | 0 | 2 | 0 |
| Dynamics | 11 | 6 | 5 | 0 | 1 | 1 | 5 | 0 |
| FallacyDetection | 5 | 2 | 3 | 0 | 0 | 1 | 3 | 1 |
| FineTuning | 11 | 0 | 11 | 11 | 0 | 0 | 10 | 0 |
| Fondations | 2 | 0 | 2 | 0 | 0 | 0 | 2 | 0 |
| HumorDetection | 1 | 1 | 0 | 0 | 0 | 0 | 0 | 0 |
| ICT-Series | 102 | 5 | 97 | 9 | 1 | 3 | 97 | 5 |
| Image | 33 | 0 | 33 | 7 | 21 | 22 | 33 | 8 |
| Infer | 1 | 1 | 0 | 0 | 0 | 0 | 0 | 0 |
| InformationQuantique | 2 | 0 | 2 | 0 | 0 | 0 | 2 | 0 |
| InformationTheory | 3 | 0 | 3 | 0 | 0 | 0 | 3 | 0 |
| Integrales | 4 | 0 | 4 | 0 | 0 | 0 | 4 | 0 |
| Jauge | 4 | 0 | 4 | 1 | 0 | 0 | 4 | 0 |
| Lean | 133 | 36 | 97 | 1 | 5 | 4 | 95 | 11 |
| ML-Training-Pipeline | 18 | 0 | 18 | 0 | 0 | 0 | 18 | 7 |
| ML.Net | 15 | 0 | 15 | 1 | 0 | 0 | 15 | 0 |
| Metajeux | 7 | 3 | 4 | 1 | 0 | 0 | 4 | 0 |
| MyIA.AI.Notebooks/GameTheory | 70 | 11 | 59 | 2 | 3 | 3 | 59 | 6 |
| MyIA.AI.Notebooks/IIT | 6 | 0 | 6 | 0 | 0 | 0 | 6 | 0 |
| MyIA.AI.Notebooks/NLP | 11 | 0 | 11 | 0 | 0 | 0 | 11 | 0 |
| MyIA.AI.Notebooks/Probas | 1 | 0 | 1 | 0 | 0 | 0 | 1 | 0 |
| MyIA.AI.Notebooks/RL | 28 | 1 | 27 | 12 | 0 | 0 | 27 | 0 |
| MyIA.AI.Notebooks/Sudoku | 21 | 3 | 18 | 2 | 1 | 1 | 18 | 2 |
| NotionsInteractives | 1 | 0 | 1 | 0 | 0 | 0 | 1 | 0 |
| Numerique | 2 | 0 | 2 | 0 | 0 | 0 | 2 | 0 |
| Part1-Foundations | 29 | 5 | 24 | 0 | 1 | 1 | 24 | 4 |
| Part2-CSP | 10 | 0 | 10 | 0 | 1 | 0 | 10 | 3 |
| Part3-Cas-pratiques | 30 | 1 | 29 | 0 | 0 | 0 | 29 | 8 |
| Part4-Metaheuristics | 2 | 0 | 2 | 0 | 0 | 0 | 2 | 0 |
| Part5-Frontieres | 13 | 0 | 13 | 0 | 0 | 0 | 13 | 0 |
| Planification-Oncologie | 2 | 0 | 2 | 2 | 0 | 0 | 2 | 0 |
| Planners | 16 | 1 | 15 | 1 | 2 | 3 | 14 | 2 |
| Plateformes-Conversationnelles | 28 | 8 | 20 | 0 | 19 | 18 | 19 | 0 |
| PostTraining | 37 | 0 | 37 | 29 | 2 | 1 | 36 | 6 |
| PyMC | 20 | 0 | 20 | 0 | 0 | 0 | 20 | 0 |
| Python | 68 | 2 | 66 | 13 | 4 | 4 | 66 | 7 |
| RAG-et-Memoire-Semantique | 14 | 0 | 14 | 4 | 4 | 5 | 14 | 0 |
| Reseau-Electrique-Intelligent | 2 | 0 | 2 | 0 | 0 | 0 | 2 | 0 |
| SMT | 25 | 0 | 25 | 0 | 0 | 0 | 25 | 1 |
| Security | 11 | 0 | 11 | 3 | 3 | 4 | 10 | 0 |
| SemanticKernel | 18 | 2 | 16 | 0 | 11 | 8 | 16 | 0 |
| SemanticWeb | 15 | 1 | 14 | 0 | 1 | 5 | 14 | 1 |
| SignalProcessing | 2 | 0 | 2 | 0 | 0 | 0 | 2 | 0 |
| SmartContracts | 31 | 7 | 24 | 0 | 3 | 17 | 24 | 0 |
| SocialChoice | 12 | 2 | 10 | 0 | 0 | 0 | 9 | 1 |
| SymbolicLearning | 20 | 2 | 18 | 7 | 2 | 2 | 18 | 2 |
| Texte | 48 | 1 | 47 | 18 | 22 | 27 | 43 | 3 |
| Tweety | 19 | 0 | 19 | 0 | 0 | 2 | 19 | 6 |
| Vibe-Coding | 6 | 5 | 1 | 0 | 0 | 0 | 0 | 1 |
| Video | 23 | 2 | 21 | 16 | 11 | 14 | 21 | 17 |
| _research | 1 | 0 | 1 | 1 | 1 | 1 | 1 | 0 |
| docker-configurations/notebook-runner | 2 | 1 | 1 | 0 | 0 | 0 | 1 | 0 |
| gateway | 2 | 0 | 2 | 0 | 0 | 0 | 1 | 1 |
| kelly_lean | 5 | 0 | 5 | 0 | 0 | 0 | 5 | 0 |
| partner-course-quant-trading | 7 | 0 | 7 | 0 | 0 | 0 | 7 | 2 |
| projects | 113 | 3 | 110 | 10 | 0 | 3 | 110 | 0 |
| research | 26 | 0 | 26 | 4 | 0 | 0 | 26 | 2 |
| scripts/notebook_tools | 1 | 1 | 0 | 0 | 0 | 0 | 0 | 0 |

## Classes d'ecart de suffisance

Le bundle publie des fichiers et n'installe rien : un import n'est fourni que s'il
est dans la distribution, s'il est installe par le carnet, ou s'il vient d'un module
de la serie livre avec le carnet. Trois classes d'ecart separent alors le critere de
ce que le bundle livre -- chacune compte des **carnets**, un carnet compte une fois
par classe :

| Classe | Ce qu'elle dit | Carnets |
|---|---|---:|
| `dependance_locale` | un module de la serie a une dependance absente de la distribution | 3 |
| `hors_serie` | le carnet importe un module d'une autre serie, non livre par le bundle | 3 |
| `absent_distribution` | l'import est une roue pure que le carnet n'installe pas lui-meme | 0 |

Ces trois classes sont mesurees sur la population que le critere acceptait
**avant** l'alignement -- un carnet deja refuse pour un GPU ou une cle n'y
figure pas : son ecart de suffisance ne changeait rien a ce que le critere
disait. Le comptage avant/apres est donc sur la meme population :

| Mesure | Avant | Apres |
|---|---:|---:|
| Carnets eligibles | 159 | 153 |

Le detail des dependances est dans le fichier `pyodide-refus.tsv` (colonne `suffisance`).

## Carnets eligibles

| Carnet | Serie | Noyau | Imports Pyodide | Roues pures |
|---|---|---|---|---|
| `MyIA.AI.Notebooks/cross-series/AgentSystems/AgentSystems-01-Perception-Vers-Action-Python.ipynb` | AgentSystems | python3 | - | - |
| `MyIA.AI.Notebooks/cross-series/AgentSystems/AgentSystems-02-Perception-Active-Valeur-Information-Python.ipynb` | AgentSystems | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/ArgumentAnalysis/Argumentation-01-Toulmin-Model-Python.ipynb` | ArgumentAnalysis | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/ArgumentAnalysis/Argumentation-01b-Schemes-Walton-Python.ipynb` | ArgumentAnalysis | python3 | - | - |
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
| `MyIA.AI.Notebooks/GenAI/Audio/06-Diffusion-SOTA/06-3-AudioDiffusion-Comparison-A-vs-B.ipynb` | Audio | python3 | - | - |
| `MyIA.AI.Notebooks/InformationCalcul/Automata/Automata-01-AutomatesFinis-Python.ipynb` | Automata | python3 | - | - |
| `MyIA.AI.Notebooks/Physique/Chaines/Chaines-06-Integrale-Chemin-Somme-Finie-Enregistrements-Python.ipynb` | Chaines | python3 | - | - |
| `MyIA.AI.Notebooks/Physique/Chaines/Chaines-07-Fonction-Wigner-Signe-N-Corps-Python.ipynb` | Chaines | python3 | - | - |
| `MyIA.AI.Notebooks/Physique/Chaines/Chaines-08-Corollaires-Quantique-Racines-Python.ipynb` | Chaines | python3 | - | - |
| `MyIA.AI.Notebooks/Physique/Chaines/Chaines-09-Coordonnee-Ordre-Chaine-Serie-Python.ipynb` | Chaines | python3 | - | - |
| `MyIA.AI.Notebooks/Physique/Chaines/Chaines-10-Groupe-Rotations-Automorphismes-Directions-Python.ipynb` | Chaines | python3 | - | - |
| `MyIA.AI.Notebooks/Physique/Chaines/Chaines-11-Groupe-Lorentz-Signature-Un-Contre-Trois-Python.ipynb` | Chaines | python3 | - | - |
| `MyIA.AI.Notebooks/Physique/Chaines/Chaines-12-Boosts-Et-L-Unite-Une-Python.ipynb` | Chaines | python3 | - | - |
| `MyIA.AI.Notebooks/InformationCalcul/Complexity/Complexity-03-HierarchieTemporelle-Python.ipynb` | Complexity | python3 | - | - |
| `MyIA.AI.Notebooks/InformationCalcul/Complexity/Complexity-03c-ComplexityZoo-Navigation-Python.ipynb` | Complexity | python3 | - | - |
| `MyIA.AI.Notebooks/InformationCalcul/Complexity/Complexity-03e-Barrieres-Exposants-WordRAM-Python.ipynb` | Complexity | python3 | - | - |
| `MyIA.AI.Notebooks/InformationCalcul/Complexity/Complexity-03f-ReductionsTriangle-Lopsided-Python.ipynb` | Complexity | python3 | - | - |
| `MyIA.AI.Notebooks/InformationCalcul/Complexity/Complexity-07b-LeTourDesGrandsNombres-Python.ipynb` | Complexity | python3 | - | - |
| `MyIA.AI.Notebooks/InformationCalcul/Complexity/Complexity-07c-LeBilanMathocalypse-Python.ipynb` | Complexity | python3 | - | - |
| `MyIA.AI.Notebooks/InformationCalcul/Complexity/Complexity-08d-IndependanceProuvee-BusyBeaver-Covering-Python.ipynb` | Complexity | python3 | - | - |
| `MyIA.AI.Notebooks/InformationCalcul/Complexity/Complexity-08e-NF-MachinesCompteARebours-Python.ipynb` | Complexity | python3 | - | - |
| `MyIA.AI.Notebooks/InformationCalcul/Compression/Compression-07-Triage-LLM-Operations-Reelles-Python.ipynb` | Compression | python3 | - | - |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/01-Python-For-Data-Science/notebooks/PyDS-01-Python_pour_la_Data_Science-Python.ipynb` | DataScienceWithAgents | python3 | - | - |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/07-Orchestration-d-Agents/Day4-Foundations/Lab8-ADK-Introduction.ipynb` | DataScienceWithAgents | python3 | - | - |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/07-Orchestration-d-Agents/Day5-DS-Star/Lab12b-Sequential-Orchestration.ipynb` | DataScienceWithAgents | python3 | - | - |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/07-Orchestration-d-Agents/Day5-DS-Star/Lab12c-Agent-Handoff.ipynb` | DataScienceWithAgents | python3 | - | - |
| `MyIA.AI.Notebooks/ML/DataScienceWithAgents/07-Orchestration-d-Agents/Day5-DS-Star/Lab12e-Session-Persistence.ipynb` | DataScienceWithAgents | python3 | - | - |
| `MyIA.AI.Notebooks/GameTheory/Dynamics/Dynamics-02-Jeux-Repetes-Lean-Python.ipynb` | Dynamics | python3 | - | - |
| `MyIA.AI.Notebooks/GameTheory/Dynamics/Dynamics-04-Open-Source-Game-Theory-Python.ipynb` | Dynamics | python3 | - | - |
| `MyIA.AI.Notebooks/GameTheory/Dynamics/Dynamics-04c-Cooperation-Payorienne-Kripke-Python.ipynb` | Dynamics | python3 | - | - |
| `MyIA.AI.Notebooks/GameTheory/Dynamics/Dynamics-05-Agents-Bornes-Python.ipynb` | Dynamics | python3 | - | - |
| `MyIA.AI.Notebooks/GameTheory/Dynamics/Dynamics-06-Preuves-Bornees-Cout-du-Raisonnement-Python.ipynb` | Dynamics | python3 | - | - |
| `MyIA.AI.Notebooks/GameTheory/Dynamics/Dynamics-08-Institutions-Transparentes-Python.ipynb` | Dynamics | python3 | - | - |
| `MyIA.AI.Notebooks/GenAI/FallacyDetection/01_taxonomy_intro.ipynb` | FallacyDetection | python3 | - | - |
| `MyIA.AI.Notebooks/GenAI/FallacyDetection/03_taxonomy_coverage_gap.ipynb` | FallacyDetection | python3 | - | - |
| `MyIA.AI.Notebooks/GenAI/HumorDetection/01_humor_intro.ipynb` | HumorDetection | python3 | - | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-Annexe-ProxyContextuality-Python.ipynb` | ICT-Series | python3 | - | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-Argumentation-QBFAcceptance-Python.ipynb` | ICT-Series | python3 | - | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-Argumentation-TruthMaintenance-Python.ipynb` | ICT-Series | python3 | - | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-Greffe2-EspaceAtteignable-Python.ipynb` | ICT-Series | python3 | - | - |
| `MyIA.AI.Notebooks/IIT/ICT-Series/ICT-Greffe4-VoteOnChain-Python.ipynb` | ICT-Series | python3 | - | - |
| `MyIA.AI.Notebooks/Probas/Infer/Infer-08b-TrueSkill-Formules-Fermees-Python.ipynb` | Infer | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Analyse/ANALYSE-02b-Entropie-Shannon-Python.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Analyse/ANALYSE-04-PFR-Primitives-Python.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Analyse/ANALYSE-06-Sensibilite-2026-Lean-Python.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Analyse/ANALYSE-08-Ramsey-VdW.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Analyse/ANALYSE-10-Reflexion-Thurston-Python.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Analyse/ANALYSE-12-Comptage-Matching-Lean-Python.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/JeuDeLaVie/GOL-10-Fractran.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Langlands/03-chaine-de-modularite-vers-fermat.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Langlands/04-umbral-moonshine-reseaux-niemeier.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Langlands/07-chabauty-kim-iwasawa-python.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-13e-Conway-Theoreme-Libre-Arbitre-Lean-Python.ipynb` | Lean | python3-lean | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-14-Finiteness-Derivatives.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-19c-Borne-Bernstein-Python.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-20-Capstone-Digestions-Tao-Python.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-37-Capstone-Serre100.ipynb` | Lean | python3-lean | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-40-Capstone-Langlands-Python.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Lean-42-Independance-Arithmetique-BusyBeaver-Lean.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/MIMO/MIMO-01-Descente-Budget-Lean-Python.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Riemann200/07-geometrie-riemannienne.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Riemann200/08-riemann-mapping.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Riemann200/09-riemann-lebesgue-fourier.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Riemann200/12b-grh-ce-quon-peut-calculer.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Riemann200/14-deux-annonces-grh-meme-jour.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100/01b-chevalley-warning-divisibilite-solutions.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100/04-lemme-yoneda-categories-finies.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100/11-corps-quadratiques-reciprocite-quadratique.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100/12-formes-quadratiques-binaires-nombre-classes.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100/13-jacobi-kronecker-reciprocite-II.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100/14-formes-quadratiques-composition-gauss.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100/15-quatre-carres-lagrange.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100/19-arbres-ping-pong-sl2.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100/22-vecteurs-witt-frobenius.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100/28-inversion-mobius-phi-euler.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/Serre100/29-reciprocite-quadratique-legendre.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/VERIF/VERIF-02-ERC20-Invariant-Companion.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Lean/VERIF/VERIF-05-Coherence-et-Temoin.ipynb` | Lean | python3 | - | - |
| `MyIA.AI.Notebooks/GameTheory/Metajeux/Metajeux-04-Chemin-Minimal-Robinson-Goforth-Python.ipynb` | Metajeux | python3 | - | - |
| `MyIA.AI.Notebooks/GameTheory/Metajeux/Metajeux-05-Temoins-Impossibilite-Python.ipynb` | Metajeux | python3 | - | - |
| `MyIA.AI.Notebooks/GameTheory/Metajeux/Metajeux-06-Chemin-Minimal-3x2-Ordinal-Python.ipynb` | Metajeux | python3 | - | - |
| `MyIA.AI.Notebooks/GameTheory/GameTheory-02d-Epistemique-Connaissance-Commune-Python.ipynb` | MyIA.AI.Notebooks/GameTheory | python3 | - | - |
| `MyIA.AI.Notebooks/GameTheory/GameTheory-03b-Chambres-Murs-Chemins-Lean-Python.ipynb` | MyIA.AI.Notebooks/GameTheory | python3 | - | - |
| `MyIA.AI.Notebooks/GameTheory/GameTheory-03e-Meta-Actions-Tarifees-Python.ipynb` | MyIA.AI.Notebooks/GameTheory | python3 | - | - |
| `MyIA.AI.Notebooks/GameTheory/GameTheory-04h-Routing-PriceOfAnarchy-Python.ipynb` | MyIA.AI.Notebooks/GameTheory | python3 | - | - |
| `MyIA.AI.Notebooks/GameTheory/GameTheory-09b-Commitment-Stackelberg-Python.ipynb` | MyIA.AI.Notebooks/GameTheory | python3 | - | - |
| `MyIA.AI.Notebooks/GameTheory/GameTheory-16b-Automated-Mechanism-Design-Python.ipynb` | MyIA.AI.Notebooks/GameTheory | python3 | - | - |
| `MyIA.AI.Notebooks/GameTheory/GameTheory-16c-Extraction-de-Revenu-DSIC-IR-Python.ipynb` | MyIA.AI.Notebooks/GameTheory | python3 | - | - |
| `MyIA.AI.Notebooks/GameTheory/GameTheory-16h-Cooperation-LLM-Python.ipynb` | MyIA.AI.Notebooks/GameTheory | python3 | - | - |
| `MyIA.AI.Notebooks/GameTheory/GameTheory-16i-Appariage-Stable-Gale-Shapley-Python.ipynb` | MyIA.AI.Notebooks/GameTheory | python3 | - | - |
| `MyIA.AI.Notebooks/GameTheory/GameTheory-21-Capstone-Choix-Social-Python.ipynb` | MyIA.AI.Notebooks/GameTheory | python3 | - | - |
| `MyIA.AI.Notebooks/GameTheory/GameTheory-23-Loopholes-Fiscaux-Python-Lean.ipynb` | MyIA.AI.Notebooks/GameTheory | python3 | - | - |
| `MyIA.AI.Notebooks/RL/RL-20-Capstone-PostTraining-Python.ipynb` | MyIA.AI.Notebooks/RL | python3 | - | - |
| `MyIA.AI.Notebooks/Sudoku/Sudoku-02-DancingLinks-Python.ipynb` | MyIA.AI.Notebooks/Sudoku | python3 | - | - |
| `MyIA.AI.Notebooks/Sudoku/Sudoku-07-Norvig-Python.ipynb` | MyIA.AI.Notebooks/Sudoku | python3 | - | - |
| `MyIA.AI.Notebooks/Sudoku/Sudoku-14-BDD-Python.ipynb` | MyIA.AI.Notebooks/Sudoku | python3 | - | - |
| `MyIA.AI.Notebooks/Search/Part1-Foundations/Search-03c-LimitedDiscrepancySearch.ipynb` | Part1-Foundations | python3 | - | - |
| `MyIA.AI.Notebooks/Search/Part1-Foundations/Search-03d-WeightedAstar.ipynb` | Part1-Foundations | python3 | - | - |
| `MyIA.AI.Notebooks/Search/Part1-Foundations/Search-03f-Reparer-Localement-Sous-Garantie-Python.ipynb` | Part1-Foundations | python3 | - | - |
| `MyIA.AI.Notebooks/Search/Part1-Foundations/Search-11d-Descente-Sous-Budget.ipynb` | Part1-Foundations | python3 | - | - |
| `MyIA.AI.Notebooks/Search/Part1-Foundations/Search-13-AutomaticGroups-WordProblem.ipynb` | Part1-Foundations | python3 | - | - |
| `MyIA.AI.Notebooks/Search/Part3-Cas-pratiques/App-25-RushHour-Admissible-Astar-Python.ipynb` | Part3-Cas-pratiques | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/Planners/02-Classical/Planners-05c-Differentiel-Atteignabilite-Python.ipynb` | Planners | python3 | - | - |
| `MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles/AI-Engine-WordPress/03-Functional/03-2-Forms/auditer-un-formulaire-conditionnel.ipynb` | Plateformes-Conversationnelles | python3 | - | - |
| `MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles/Open-WebUI/Playwright-OWUI/00-Parcours-QA-OWUI.ipynb` | Plateformes-Conversationnelles | python3 | - | - |
| `MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles/Open-WebUI/Playwright-OWUI/01-decouverte/01-Decouverte-QA-OWUI.ipynb` | Plateformes-Conversationnelles | python3 | - | - |
| `MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles/Open-WebUI/Playwright-OWUI/02-navigation-authentification/02-Navigation-Auth-QA-OWUI.ipynb` | Plateformes-Conversationnelles | python3 | - | - |
| `MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles/Open-WebUI/Playwright-OWUI/03-chat-streaming/03-Chat-Streaming-QA-OWUI.ipynb` | Plateformes-Conversationnelles | python3 | - | - |
| `MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles/Open-WebUI/Playwright-OWUI/04-rag-tools-avances/04-RAG-Tools-QA-OWUI.ipynb` | Plateformes-Conversationnelles | python3 | - | - |
| `MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles/Open-WebUI/Playwright-OWUI/05-multi-tenant-ci/05-Multi-Tenant-CI-QA-OWUI.ipynb` | Plateformes-Conversationnelles | python3 | - | - |
| `MyIA.AI.Notebooks/GenAI/Plateformes-Conversationnelles/Open-WebUI/Playwright-OWUI/06-nouveautes-v0.10/06-Nouveautes-v0.10-QA-OWUI.ipynb` | Plateformes-Conversationnelles | python3 | - | - |
| `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-Cloud-03b-RiskParity-Composite.ipynb` | Python | python3 | - | - |
| `MyIA.AI.Notebooks/QuantConnect/Python/QC-Py-Cloud-09-OptionWheel.ipynb` | Python | python3 | - | - |
| `MyIA.AI.Notebooks/GenAI/SemanticKernel/Notebook-Template.ipynb` | SemanticKernel | python3 | - | - |
| `MyIA.AI.Notebooks/GenAI/SemanticKernel/Workbook-Template-Python.ipynb` | SemanticKernel | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/SemanticWeb/SW-16-ProofCarryingOntologies-Python.ipynb` | SemanticWeb | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/SmartContracts/00-Foundations/SC-01-Setup-Foundry-Python.ipynb` | SmartContracts | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/SmartContracts/02-Solidity-Advanced/SC-7b-ERC20-Lean-Verification-Companion.ipynb` | SmartContracts | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/SmartContracts/03-Foundry-Testing/SC-12-Foundry-Testing-Python.ipynb` | SmartContracts | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/SmartContracts/03-Foundry-Testing/SC-13-Fuzz-Invariants-Python.ipynb` | SmartContracts | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/SmartContracts/05-Alternative-Chains/SC-21-Move-Sui-Python.ipynb` | SmartContracts | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/SmartContracts/05-Alternative-Chains/SC-22-Solana-Anchor-Python.ipynb` | SmartContracts | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/SmartContracts/06-Real-World/SC-23-Cross-Chain-Python.ipynb` | SmartContracts | python3 | - | - |
| `MyIA.AI.Notebooks/GameTheory/SocialChoice/ChoixSocial-02-Stable-Marriage-Gale-Shapley-Python.ipynb` | SocialChoice | python3 | - | - |
| `MyIA.AI.Notebooks/GameTheory/SocialChoice/ChoixSocial-06-Mobius-Aggregation-Pouvoir-Manipulation-Python.ipynb` | SocialChoice | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/SymbolicLearning/SL-1-LogicalLearning.ipynb` | SymbolicLearning | python3 | - | - |
| `MyIA.AI.Notebooks/SymbolicAI/SymbolicLearning/SL-2-KnowledgeBasedLearning.ipynb` | SymbolicLearning | python3 | - | - |
| `MyIA.AI.Notebooks/GenAI/Texte/14b_Paginated_Memory-Python.ipynb` | Texte | python3 | - | - |
| `MyIA.AI.Notebooks/GenAI/Vibe-Coding/Claude-Code/notebooks/01-Claude-CLI-Bases.ipynb` | Vibe-Coding | python3 | - | - |
| `MyIA.AI.Notebooks/GenAI/Vibe-Coding/Claude-Code/notebooks/02-Claude-CLI-Sessions.ipynb` | Vibe-Coding | python3 | - | - |
| `MyIA.AI.Notebooks/GenAI/Vibe-Coding/Claude-Code/notebooks/03-Claude-CLI-References.ipynb` | Vibe-Coding | python3 | - | - |
| `MyIA.AI.Notebooks/GenAI/Vibe-Coding/Claude-Code/notebooks/04-Claude-CLI-Agents.ipynb` | Vibe-Coding | python3 | - | - |
| `MyIA.AI.Notebooks/GenAI/Vibe-Coding/Claude-Code/notebooks/05-Claude-CLI-Automatisation.ipynb` | Vibe-Coding | python3 | - | - |
| `MyIA.AI.Notebooks/GenAI/Video/02-Advanced/02-6-Video-Architecture-Licensing.ipynb` | Video | python3 | - | - |
| `MyIA.AI.Notebooks/GenAI/Video/02-Advanced/02-8-PAN2-Modele-du-Monde-GLP.ipynb` | Video | python3 | - | - |
| `docker-configurations/notebook-runner/witness/witness-global-313.ipynb` | docker-configurations/notebook-runner | global-3.13 | - | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/Congress-Trades-Copy/research.ipynb` | projects | python3 | - | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/Research-Executor/research.ipynb` | projects | python3 | - | - |
| `MyIA.AI.Notebooks/QuantConnect/projects/Research-Executor/runner.ipynb` | projects | python3 | - | - |
| `scripts/notebook_tools/verify_runtime_smoke.ipynb` | scripts/notebook_tools | python3 | - | - |

## Refuses : motifs par serie

Le detail **carnet par carnet** des refus (motif et element declencheur) est dans le
fichier `pyodide-refus.tsv`, une ligne par carnet refuse.

| Serie | Motifs rencontres | Imports absents (les plus frequents) |
|---|---|---|
| 00-GenAI-Environment | cle, gpu, import_absent, reseau, suffisance | dotenv (4), requests (4), IPython.display (2), PIL (1), ipywidgets (1), matplotlib.pyplot (1) |
| 3D | gpu, import_absent, reseau | numpy (10), matplotlib.pyplot (9), gsplat (2), rasterio (2), PIL (1), numpy.testing (1) |
| Applications | gpu, import_absent | numpy (9), matplotlib.pyplot (8), scipy (6), networkx (5), scipy.interpolate (2), matplotlib (1) |
| ArgumentAnalysis | cle, gpu, import_absent, reseau, suffisance | dotenv (6), jpype (6), matplotlib.pyplot (6), pandas (6), numpy (4), openai (4) |
| Audio | cle, gpu, import_absent, reseau, suffisance | numpy (40), IPython.display (37), soundfile (30), dotenv (29), openai (18), matplotlib.pyplot (17) |
| CaseStudies | cle, import_absent, suffisance | dotenv (4), semantic_kernel (4), semantic_kernel.agents (4), semantic_kernel.connectors.ai.open_ai (4), semantic_kernel.contents (4), semantic_kernel.functions (4) |
| Causalite | gpu, import_absent, reseau, suffisance | numpy (12), pandas (11), matplotlib.pyplot (9), dowhy (6), networkx (4), sklearn.linear_model (2) |
| Chaines | import_absent | numpy (5), matplotlib (1), matplotlib.pyplot (1) |
| Coalitions | import_absent, suffisance | numpy (2), matplotlib (1), matplotlib.pyplot (1), networkx (1), pandas (1), pulp (1) |
| Complexity | import_absent, suffisance | numpy (14), matplotlib.pyplot (10), pandas (1), scipy (1), scipy.optimize (1), stim (1) |
| Compression | gpu, import_absent | matplotlib.pyplot (9), numpy (4), lxml (2), openai (2), pandas (2), semantic_kernel (2) |
| Constructeur | import_absent | numpy (1) |
| DataScienceWithAgents | cle, gpu, import_absent, reseau, suffisance | numpy (90), matplotlib.pyplot (70), pandas (31), sklearn.model_selection (29), sklearn.linear_model (27), sklearn.metrics (24) |
| DecisionTheory | import_absent, suffisance | numpy (15), matplotlib.pyplot (13), arviz (11), pymc (11), pandas (7), scipy (5) |
| Diagnostic-Medical | import_absent | matplotlib.pyplot (2), numpy (2), pandas (2), seaborn (2), z3 (2) |
| Dynamics | cle, import_absent, reseau | numpy (5), matplotlib.pyplot (4), matplotlib.patches (1), pandas (1), scipy (1), scipy.stats (1) |
| FallacyDetection | import_absent, reseau, suffisance | matplotlib.pyplot (2), numpy (2), fallacy_detection (1), matplotlib (1), matplotlib.ticker (1), pandas (1) |
| FineTuning | gpu, import_absent | peft (8), transformers (7), datasets (6), numpy (5), torchvision (4), IPython.display (2) |
| Fondations | import_absent | numpy (2), matplotlib.pyplot (1) |
| ICT-Series | cle, gpu, import_absent, reseau, suffisance | numpy (96), matplotlib.pyplot (76), pandas (20), matplotlib (18), antropy (6), scipy.stats (5) |
| Image | cle, gpu, import_absent, reseau, suffisance | matplotlib.pyplot (29), PIL (25), dotenv (21), numpy (21), requests (20), IPython.display (10) |
| InformationQuantique | import_absent | numpy (2) |
| InformationTheory | import_absent | numpy (3) |
| Integrales | import_absent | mpmath (4), matplotlib.pyplot (1), numpy (1), pandas (1) |
| Jauge | gpu, import_absent | matplotlib.pyplot (3), numpy (3), sympy (3), matplotlib (2), mpmath (1), pandas (1) |
| Lean | cle, gpu, import_absent, reseau, suffisance | matplotlib.pyplot (56), numpy (44), matplotlib (21), sympy (12), matplotlib.patches (7), mpmath (7) |
| ML-Training-Pipeline | import_absent, suffisance | numpy (18), pandas (18), matplotlib.pyplot (11), IPython.display (1), hmmlearn (1), matplotlib (1) |
| ML.Net | gpu, import_absent | numpy (14), matplotlib.pyplot (9), pandas (7), sklearn.linear_model (6), sklearn.metrics (6), sklearn.decomposition (4) |
| Metajeux | gpu, import_absent | numpy (3), Abstraction (1), matplotlib.pyplot (1) |
| MyIA.AI.Notebooks/GameTheory | cle, gpu, import_absent, reseau, suffisance | numpy (55), matplotlib.pyplot (37), scipy.optimize (10), nashpy (8), networkx (5), pandas (5) |
| MyIA.AI.Notebooks/IIT | import_absent | numpy (6), pyphi (5), matplotlib (1), matplotlib.pyplot (1), pandas (1), pyphi.actual (1) |
| MyIA.AI.Notebooks/NLP | import_absent | matplotlib.pyplot (8), numpy (7), pandas (3), nltk (2), sklearn.linear_model (2), IPython.display (1) |
| MyIA.AI.Notebooks/Probas | import_absent | arviz (1), matplotlib.pyplot (1), numpy (1), pymc (1), scipy (1) |
| MyIA.AI.Notebooks/RL | gpu, import_absent | numpy (26), matplotlib.pyplot (24), gymnasium (14), stable_baselines3 (5), stable_baselines3.common.evaluation (4), stable_baselines3.common.monitor (4) |
| MyIA.AI.Notebooks/Sudoku | cle, gpu, import_absent, reseau, suffisance | numpy (12), matplotlib.pyplot (8), matplotlib.patches (3), ortools.sat.python (2), pandas (2), z3 (2) |
| NotionsInteractives | import_absent | ipywidgets (1), matplotlib.pyplot (1), numpy (1) |
| Numerique | import_absent | matplotlib (2), matplotlib.pyplot (2), numpy (2) |
| Part1-Foundations | cle, import_absent, reseau, suffisance | numpy (21), matplotlib.pyplot (20), pandas (9), matplotlib.patches (8), networkx (4), cvxpy (2) |
| Part2-CSP | cle, import_absent, suffisance | matplotlib.pyplot (10), numpy (10), ortools.sat.python (6), pychoco (4), matplotlib.patches (3), constraint (2) |
| Part3-Cas-pratiques | import_absent, suffisance | numpy (28), matplotlib.pyplot (27), ortools.sat.python (13), matplotlib.patches (9), pandas (5), IPython.display (3) |
| Part4-Metaheuristics | import_absent | numpy (2), matplotlib.pyplot (1), pandas (1) |
| Part5-Frontieres | import_absent | matplotlib.pyplot (11), ortools.sat.python (9), pandas (9), numpy (7), matplotlib (4), ortools (3) |
| Planification-Oncologie | gpu, import_absent | matplotlib.pyplot (2), numpy (2), ortools.sat.python (2), pandas (2), pyro (2), pyro.distributions (2) |
| Planners | cle, gpu, import_absent, reseau, suffisance | unified_planning.shortcuts (11), unified_planning (8), unified_planning.engines (8), matplotlib.pyplot (5), numpy (5), unified_planning.environment (4) |
| Plateformes-Conversationnelles | cle, import_absent, reseau | dotenv (17), requests (17), numpy (4), openai (3), playwright.sync_api (2), mcp (1) |
| PostTraining | cle, gpu, import_absent, reseau, suffisance | numpy (28), matplotlib.pyplot (24), transformers (18), trl (14), datasets (13), peft (11) |
| PyMC | import_absent | arviz (20), numpy (20), pymc (20), matplotlib.pyplot (17), pytensor.tensor (13), scipy (7) |
| Python | cle, gpu, import_absent, reseau, suffisance | numpy (58), matplotlib.pyplot (42), pandas (41), AlgorithmImports (40), sklearn.preprocessing (14), sklearn.metrics (10) |
| RAG-et-Memoire-Semantique | cle, gpu, import_absent, reseau | matplotlib.pyplot (8), numpy (8), transformers (6), matplotlib (5), qdrant_client (5), pandas (4) |
| Reseau-Electrique-Intelligent | import_absent | numpy (2), ortools.sat.python (1) |
| SMT | import_absent, suffisance | z3 (24), matplotlib.pyplot (6), matplotlib (2), matplotlib.patches (1), numpy (1), truststore (1) |
| Security | cle, gpu, import_absent, reseau | numpy (9), matplotlib.pyplot (4), scipy.optimize (2), sklearn.linear_model (2), matplotlib (1), mcp (1) |
| SemanticKernel | cle, import_absent, reseau | semantic_kernel (13), dotenv (12), semantic_kernel.connectors.ai.open_ai (12), semantic_kernel.functions (10), openai (9), semantic_kernel.contents (8) |
| SemanticWeb | cle, import_absent, reseau, suffisance | rdflib (13), rdflib.namespace (10), owlrl (4), pyshacl (4), matplotlib.pyplot (3), owlready2 (3) |
| SignalProcessing | import_absent | numpy (2), matplotlib.pyplot (1) |
| SmartContracts | cle, import_absent, reseau | solcx (16), web3 (16), dotenv (3), eth_account (3), phe (3), Crypto.Hash (2) |
| SocialChoice | import_absent, suffisance | numpy (7), matplotlib.pyplot (6), z3 (4), pysat.solvers (2), matplotlib.patches (1), networkx (1) |
| SymbolicLearning | cle, gpu, import_absent, reseau, suffisance | numpy (11), matplotlib.pyplot (8), matplotlib (4), clingo (3), janus_swi (3), dotenv (2) |
| Texte | cle, gpu, import_absent, reseau, suffisance | openai (27), dotenv (25), numpy (14), matplotlib.pyplot (11), transformers (11), matplotlib (9) |
| Tweety | import_absent, reseau, suffisance | jpype (16), jpype.types (14), jpype.imports (11), java.util (10), org.tweetyproject.arg.dung.syntax (8), org.tweetyproject.logics.pl.syntax (8) |
| Vibe-Coding | suffisance | - |
| Video | cle, gpu, import_absent, reseau, suffisance | numpy (20), PIL (19), matplotlib.pyplot (19), dotenv (18), imageio (15), diffusers (10) |
| _research | cle, gpu, import_absent, reseau | IPython (1), PIL (1), anthropic (1), cv2 (1), dotenv (1), matplotlib (1) |
| docker-configurations/notebook-runner | import_absent | numpy (1), pandas (1) |
| gateway | import_absent, suffisance | kernel_gateway (1) |
| kelly_lean | import_absent | matplotlib.pyplot (5), numpy (5) |
| partner-course-quant-trading | import_absent, suffisance | matplotlib.pyplot (7), AlgorithmImports (5), numpy (4), pandas (4), deap (2), matplotlib.ticker (2) |
| projects | gpu, import_absent, reseau | pandas (106), numpy (104), matplotlib.pyplot (88), AlgorithmImports (65), yfinance (46), sklearn.preprocessing (21) |
| research | gpu, import_absent, suffisance | numpy (26), pandas (25), matplotlib.pyplot (13), yfinance (12), scipy (6), AlgorithmImports (4) |

Les motifs **se cumulent** : un carnet refuse pour une cle d'API et pour un import
absent compte dans les deux colonnes de la table par serie.

