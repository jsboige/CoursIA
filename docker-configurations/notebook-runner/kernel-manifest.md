# Manifeste des dependances par famille de noyau

Genere par `python scripts/notebook_tools/kernel_dependency_manifest.py --write` (Pli 1.1, issue #27544). Ne pas editer a la main : regenerer.

## Sources

| Source | Usage |
|---|---|
| `git ls-files` | inventaire des carnets et des fichiers de dependances |
| `COURSE_CATALOG.generated.json` | `requires_gpu`, `requires_api`, `requires_cloud`, `requires_wsl` |
| bloc `metadata.kernelspec` de chaque carnet | famille de noyau |

Aucun appel reseau. Budget d'image applique : **2000 Mo**.

## Chiffres

| Mesure | Valeur |
|---|---|
| Carnets suivis | 1939 |
| Fichiers de dependances | 37 |
| Groupes serie / sous-serie | 83 |
| Paquets distincts declares | 206 |
| Paquets retenus dans le manifeste | 200 |
| Conflits de versions | 0 |
| Empreinte estimee du manifeste | 3278 Mo |

## Familles de noyau

| Famille | Carnets | Series |
|---|---|---|
| python | 1462 | CaseStudies, Complexity, Compression, GameTheory, GenAI, IIT, InformationCalcul, ML, NLP, Physique, Probas, QuantConnect, RL, Search, Sudoku, SymbolicAI, cross-series, scripts |
| csharp | 393 | Complexity, Compression, GameTheory, GenAI, ML, MyIA.AI.Notebooks, NLP, Probas, QuantConnect, RL, Search, Sudoku, SymbolicAI, cross-series, scripts |
| lean | 73 | Compression, GameTheory, IIT, ML, Probas, QuantConnect, Search, Sudoku, SymbolicAI |
| rust | 1 | Sudoku |
| other | 10 | GenAI, IIT, QuantConnect |

Noms de kernelspec rencontres :

| Noyau | Carnets |
|---|---|
| `python3` | 1359 |
| `.net-csharp` | 393 |
| `lean4-wsl` | 68 |
| `coursia-ml-training` | 51 |
| `unknown` | 10 |
| `python3-lean` | 9 |
| `pyphi` | 6 |
| `python3-wsl` | 6 |
| `pyphi-iit` | 4 |
| `python3-coursia2` | 3 |
| `coursia-py313-argu` | 2 |
| `gametheory-wsl` | 2 |
| `gsplat310` | 2 |
| `ict-py313` | 2 |
| `lean4-wsl-perc` | 2 |
| `py310-gpu` | 2 |
| `basicpitch-t4` | 1 |
| `conda-torch` | 1 |
| `coursia-drift` | 1 |
| `coursia-py313` | 1 |
| `dia-tts` | 1 |
| `difflogic-sl12` | 1 |
| `global-3.13` | 1 |
| `lean4-wsl-conway` | 1 |
| `lean4-wsl-groth16200` | 1 |
| `leandojo-v2` | 1 |
| `mert2-gpu` | 1 |
| `pipecat-kokoro` | 1 |
| `py311-po2028` | 1 |
| `python3-sc16-concrete-wsl` | 1 |
| `rust` | 1 |
| `rvc-wsl` | 1 |
| `sheetsage2-gpu` | 1 |
| `smartcontracts` | 1 |

10 carnets ne portent aucun `kernelspec` lisible, et le catalogue les classe aussi `unknown` : leur famille est `other`. Leur noyau reste a determiner ; ils restent dans la table avec leur groupe.

## Table par serie et sous-serie

| Serie | Sous-serie | Carnets | Noyau | GPU | API | Cloud | WSL | Deps | Mo | Verdict |
|---|---|---:|---|---:|---:|---:|---:|---:|---:|---|
| CaseStudies | (racine) | 0 |  | 0 | 0 | 0 | 0 | 1 | 1082 (+1082) | inclus |
| CaseStudies | Diagnostic-Medical | 2 | python3 (2) | 0 | 0 | 0 | 0 | 1 | 1082 | inclus |
| CaseStudies | Planification-Oncologie | 2 | python3 (2) | 0 | 0 | 0 | 0 | 1 | 1082 | inclus |
| CaseStudies | Reseau-Electrique-Intelligent | 2 | python3 (2) | 0 | 0 | 0 | 0 | 1 | 1082 | inclus |
| Complexity | (racine) | 44 | .net-csharp (17), coursia-ml-training (1), coursia-py313 (1), python3 (25) | 0 | 2 | 0 | 0 | 0 | 0 | inclus |
| Compression | (racine) | 17 | .net-csharp (5), python3 (12) | 0 | 3 | 0 | 0 | 0 | 0 | inclus |
| Compression | Compression_lean | 1 | lean4-wsl (1) | 0 | 0 | 0 | 0 | 0 | 0 | inclus |
| GameTheory | (racine) | 123 | .net-csharp (43), coursia-ml-training (3), gametheory-wsl (2), lean4-wsl (10), python3 (65) | 1 | 4 | 0 | 13 | 1 | 288 (+288) | inclus |
| GameTheory | Coalitions | 5 | lean4-wsl (1), python3 (4) | 0 | 0 | 0 | 2 | 1 | 288 | inclus |
| GameTheory | Dynamics | 17 | .net-csharp (4), lean4-wsl (2), python3 (11) | 0 | 1 | 0 | 3 | 1 | 288 | inclus |
| GameTheory | Metajeux | 8 | .net-csharp (1), coursia-ml-training (1), python3 (6) | 0 | 0 | 0 | 0 | 1 | 288 | inclus |
| GameTheory | SocialChoice | 17 | .net-csharp (5), lean4-wsl (1), python3 (10), python3-wsl (1) | 0 | 0 | 0 | 2 | 1 | 288 | inclus |
| GameTheory | gateway | 1 | python3 (1) | 0 | 0 | 0 | 0 | 2 | 291 (+6) | inclus |
| GenAI | (racine) | 0 |  | 0 | 0 | 0 | 0 | 1 | 1787 (+1787) | inclus |
| GenAI | 00-GenAI-Environment | 7 | python3 (7) | 6 | 6 | 0 | 1 | 1 | 1787 | exclu (gpu) |
| GenAI | 3D | 9 | gsplat310 (2), python3 (7) | 7 | 2 | 0 | 0 | 1 | 1787 | exclu (gpu) |
| GenAI | Audio | 49 | basicpitch-t4 (1), coursia-ml-training (1), dia-tts (1), mert2-gpu (1), pipecat-kokoro (1), python3 (42), rvc-wsl (1), sheetsage2-gpu (1) | 35 | 23 | 0 | 0 | 2 | 1793 (+126) | exclu (gpu) |
| GenAI | CaseStudies | 6 | python3 (6) | 1 | 6 | 0 | 0 | 1 | 1787 | inclus |
| GenAI | FallacyDetection | 5 | python3 (5) | 0 | 1 | 0 | 0 | 1 | 1787 | inclus |
| GenAI | FineTuning | 20 | python3 (20) | 20 | 2 | 0 | 0 | 1 | 1787 | exclu (gpu) |
| GenAI | HumorDetection | 1 | python3 (1) | 0 | 0 | 0 | 0 | 1 | 1787 | inclus |
| GenAI | Image | 35 | python3 (34), unknown (1) | 16 | 25 | 0 | 0 | 1 | 1787 | inclus |
| GenAI | Integrations-DotNet | 19 | .net-csharp (19) | 2 | 8 | 0 | 0 | 1 | 1787 | inclus |
| GenAI | Plateformes-Conversationnelles | 28 | python3 (28) | 0 | 15 | 0 | 0 | 1 | 1787 | inclus |
| GenAI | PostTraining | 27 | .net-csharp (1), coursia-ml-training (14), python3 (12) | 16 | 0 | 2 | 0 | 2 | 1854 (+1335) | exclu (gpu) |
| GenAI | RAG-et-Memoire-Semantique | 19 | .net-csharp (4), coursia-ml-training (4), python3 (11) | 5 | 7 | 0 | 1 | 1 | 1787 | inclus |
| GenAI | Security | 9 | python3 (9) | 1 | 3 | 0 | 0 | 1 | 1787 | inclus |
| GenAI | SemanticKernel | 25 | .net-csharp (7), python3 (18) | 1 | 19 | 1 | 0 | 1 | 1787 | service optionnel (service) |
| GenAI | Texte | 52 | .net-csharp (4), coursia-ml-training (2), python3 (45), python3-coursia2 (1) | 13 | 34 | 0 | 0 | 2 | 1816 (+35) | inclus |
| GenAI | Vibe-Coding | 7 | .net-csharp (1), python3 (6) | 0 | 2 | 0 | 0 | 2 | 1801 (+14) | inclus |
| GenAI | Video | 23 | python3 (23) | 19 | 16 | 0 | 0 | 2 | 1793 (+373) | exclu (gpu) |
| GenAI | _research | 2 | .net-csharp (1), python3 (1) | 0 | 0 | 0 | 0 | 1 | 1787 | inclus |
| IIT | (racine) | 10 | lean4-wsl (4), pyphi (6) | 0 | 0 | 0 | 0 | 1 | 134 (+134) | inclus |
| IIT | ICT-Series | 100 | coursia-ml-training (1), ict-py313 (2), py310-gpu (1), pyphi-iit (4), python3 (87), unknown (5) | 18 | 5 | 0 | 0 | 2 | 137 (+3) | inclus |
| InformationCalcul | InformationTheory | 1 | python3 (1) | 0 | 0 | 0 | 0 | 0 | 0 | inclus |
| ML | DataScienceWithAgents | 131 | .net-csharp (15), coursia-drift (1), coursia-ml-training (12), lean4-wsl (4), py310-gpu (1), python3 (97), python3-coursia2 (1) | 32 | 10 | 0 | 0 | 4 | 1445 (+1445) | inclus |
| ML | ML.Net | 29 | .net-csharp (15), coursia-ml-training (1), python3 (13) | 0 | 0 | 0 | 0 | 0 | 0 | inclus |
| MyIA.AI.Notebooks | (racine) | 1 | .net-csharp (1) | 0 | 0 | 0 | 0 | 0 | 0 | inclus |
| NLP | (racine) | 20 | .net-csharp (9), coursia-ml-training (3), python3 (8) | 0 | 0 | 0 | 0 | 0 | 0 | inclus |
| Physique | Chaines | 11 | python3 (11) | 0 | 0 | 0 | 0 | 0 | 0 | inclus |
| Physique | Constructeur | 1 | python3 (1) | 0 | 0 | 0 | 0 | 0 | 0 | inclus |
| Physique | InformationQuantique | 1 | python3 (1) | 0 | 0 | 0 | 0 | 0 | 0 | inclus |
| Physique | Integrales | 4 | python3 (4) | 0 | 0 | 0 | 0 | 0 | 0 | inclus |
| Physique | Jauge | 4 | python3 (4) | 0 | 0 | 0 | 0 | 0 | 0 | inclus |
| Physique | Numerique | 2 | python3 (2) | 0 | 0 | 0 | 1 | 0 | 0 | inclus |
| Probas | (racine) | 1 | python3 (1) | 0 | 0 | 0 | 0 | 1 | 1206 (+1206) | inclus |
| Probas | Applications | 12 | lean4-wsl-perc (2), python3 (10) | 0 | 0 | 0 | 0 | 1 | 1206 | inclus |
| Probas | Causalite | 12 | coursia-ml-training (4), python3 (8) | 0 | 1 | 0 | 0 | 1 | 1206 | inclus |
| Probas | DecisionTheory | 26 | .net-csharp (8), lean4-wsl (3), python3 (15) | 0 | 0 | 0 | 0 | 1 | 1206 | inclus |
| Probas | Fondations | 4 | .net-csharp (2), python3 (2) | 0 | 0 | 0 | 0 | 1 | 1206 | inclus |
| Probas | Infer | 21 | .net-csharp (21) | 0 | 0 | 0 | 0 | 2 | 1235 (+29) | inclus |
| Probas | PyMC | 20 | python3 (20) | 0 | 0 | 0 | 0 | 1 | 1206 | inclus |
| QuantConnect | (racine) | 0 |  | 0 | 0 | 0 | 0 | 1 | 1397 (+1397) | inclus |
| QuantConnect | ML-Training-Pipeline | 18 | python3 (18) | 0 | 0 | 4 | 0 | 1 | 1397 | service optionnel (service) |
| QuantConnect | Python | 68 | conda-torch (1), coursia-py313-argu (1), python3 (65), python3-coursia2 (1) | 10 | 6 | 66 | 0 | 1 | 1397 | service optionnel (service) |
| QuantConnect | kelly_lean | 6 | lean4-wsl (1), python3 (1), unknown (4) | 0 | 0 | 6 | 0 | 1 | 1397 | service optionnel (service) |
| QuantConnect | partner-course-quant-trading | 12 | python3 (12) | 0 | 0 | 0 | 0 | 1 | 1397 | inclus |
| QuantConnect | projects | 114 | .net-csharp (1), python3 (113) | 1 | 0 | 49 | 0 | 2 | 1406 (+9) | service optionnel (service) |
| QuantConnect | research | 26 | python3 (26) | 0 | 0 | 0 | 0 | 1 | 1397 | inclus |
| RL | (racine) | 32 | .net-csharp (4), python3 (28) | 5 | 0 | 0 | 0 | 1 | 1192 (+1192) | inclus |
| RL | PostTraining | 12 | .net-csharp (1), coursia-ml-training (4), python3 (7) | 4 | 0 | 1 | 0 | 1 | 1192 | service optionnel (service) |
| Search | (racine) | 0 |  | 0 | 0 | 0 | 0 | 1 | 378 (+378) | inclus |
| Search | Part1-Foundations | 57 | .net-csharp (28), lean4-wsl (1), python3 (28) | 0 | 3 | 0 | 1 | 2 | 395 (+20) | inclus |
| Search | Part2-CSP | 20 | .net-csharp (10), python3 (10) | 2 | 4 | 0 | 0 | 1 | 378 | inclus |
| Search | Part3-Cas-pratiques | 53 | .net-csharp (23), python3 (30) | 0 | 0 | 0 | 0 | 1 | 378 | inclus |
| Search | Part4-Metaheuristics | 35 | .net-csharp (33), python3 (2) | 0 | 1 | 0 | 0 | 2 | 395 (+17) | inclus |
| Search | Part5-Frontieres | 15 | .net-csharp (2), python3 (13) | 0 | 1 | 0 | 0 | 1 | 378 | inclus |
| Search | _archive | 2 | python3 (2) | 0 | 0 | 0 | 0 | 1 | 378 | inclus |
| Sudoku | (racine) | 43 | .net-csharp (20), lean4-wsl (1), python3 (21), rust (1) | 1 | 1 | 0 | 0 | 1 | 1293 (+1293) | inclus |
| SymbolicAI | (racine) | 1 | .net-csharp (1) | 0 | 0 | 0 | 0 | 0 | 0 | inclus |
| SymbolicAI | ArgumentAnalysis | 43 | coursia-py313-argu (1), python3 (42) | 0 | 6 | 0 | 0 | 1 | 19 (+19) | inclus |
| SymbolicAI | Lean | 168 | .net-csharp (2), global-3.13 (1), lean4-wsl (35), lean4-wsl-conway (1), lean4-wsl-groth16200 (1), leandojo-v2 (1), py311-po2028 (1), python3 (114), python3-lean (9), python3-wsl (3) | 1 | 7 | 0 | 167 | 2 | 60 (+60) | inclus |
| SymbolicAI | Planners | 27 | .net-csharp (10), lean4-wsl (1), python3 (16) | 1 | 2 | 0 | 1 | 1 | 973 (+973) | inclus |
| SymbolicAI | SMT | 56 | .net-csharp (31), python3 (25) | 0 | 1 | 0 | 0 | 2 | 78 (+78) | inclus |
| SymbolicAI | SemanticWeb | 29 | .net-csharp (14), python3 (15) | 0 | 5 | 0 | 0 | 1 | 139 (+139) | inclus |
| SymbolicAI | SmartContracts | 32 | lean4-wsl (1), python3 (29), python3-sc16-concrete-wsl (1), smartcontracts (1) | 0 | 3 | 0 | 7 | 2 | 76 (+76) | inclus |
| SymbolicAI | SymbolicLearning | 31 | .net-csharp (8), difflogic-sl12 (1), lean4-wsl (1), python3 (19), python3-wsl (2) | 5 | 2 | 0 | 3 | 2 | 1171 (+1171) | inclus |
| SymbolicAI | Tweety | 39 | .net-csharp (19), lean4-wsl (1), python3 (19) | 0 | 0 | 0 | 7 | 1 | 90 (+90) | inclus |
| SymbolicAI | _archive | 1 | python3 (1) | 0 | 0 | 0 | 0 | 0 | 0 | inclus |
| cross-series | AgentSystems | 2 | python3 (2) | 0 | 0 | 0 | 0 | 0 | 0 | inclus |
| cross-series | matching-cv | 0 |  | 0 | 0 | 0 | 0 | 1 | 218 (+218) | inclus |
| cross-series | socle-metadata-driven | 2 | .net-csharp (2) | 0 | 1 | 0 | 0 | 0 | 0 | inclus |
| scripts | notebook_tools | 2 | .net-csharp (1), python3 (1) | 0 | 0 | 0 | 0 | 0 | 0 | inclus |

`GPU`, `API`, `Cloud` et `WSL` comptent les carnets du groupe qui declarent le besoin ; `Deps` compte les fichiers de dependances propres et herites du socle de serie ; `Mo` est l'empreinte installee estimee, socle de serie compris, et `(+N)` l'increment propre du groupe au-dela de ce socle.

## Fichiers de dependances hors perimetre

Ces fichiers ne decrivent aucun environnement de carnet : ils servent l'outillage du depot ou des images de service. Ils n'entrent ni dans la table ni dans le manifeste, et sont listes ici pour que rien ne disparaisse en silence.

| Fichier | Paquets |
|---|---:|
| `docker-configurations/services/comfyui-qwen/workspace/requirements.txt` | 35 |
| `docker-configurations/services/orchestrator/requirements.txt` | 17 |
| `scripts/genai-stack/requirements.txt` | 6 |
| `scripts/notebook_tools/requirements.txt` | 4 |
| `scripts/sudoku/requirements.txt` | 4 |

## Exclusions et motifs

### Motif `gpu` — 6 groupe(s)

| Groupe | Carnets | GPU | Mo | Justification |
|---|---:|---:|---:|---|
| GenAI/00-GenAI-Environment | 7 | 6 | 1787 | 6 carnets sur 7 declarent `requires_gpu` : le GPU est le mode d'execution dominant du groupe |
| GenAI/3D | 9 | 7 | 1787 | 7 carnets sur 9 declarent `requires_gpu` : le GPU est le mode d'execution dominant du groupe |
| GenAI/Audio | 49 | 35 | 1793 | 35 carnets sur 49 declarent `requires_gpu` : le GPU est le mode d'execution dominant du groupe |
| GenAI/FineTuning | 20 | 20 | 1787 | 20 carnets sur 20 declarent `requires_gpu` : le GPU est le mode d'execution dominant du groupe |
| GenAI/PostTraining | 27 | 16 | 1854 | 16 carnets sur 27 declarent `requires_gpu` : le GPU est le mode d'execution dominant du groupe |
| GenAI/Video | 23 | 19 | 1793 | 19 carnets sur 23 declarent `requires_gpu` : le GPU est le mode d'execution dominant du groupe |

### Motif `taille` — 0 groupe(s)

Aucun groupe exclu pour ce motif.

### Motif `licence` — 0 groupe(s)

Aucun groupe exclu pour ce motif.

### Motif `conflit de versions` — 0 groupe(s)

Aucun groupe exclu pour ce motif.

### Services optionnels (Pli 1.5) — 6 groupe(s)

| Groupe | Carnets cloud | Service attendu |
|---|---:|---|
| GenAI/SemanticKernel | 1 | hors image : le carnet attend un service reseau |
| QuantConnect/ML-Training-Pipeline | 4 | hors image : le carnet attend un service reseau |
| QuantConnect/Python | 66 | hors image : le carnet attend un service reseau |
| QuantConnect/kelly_lean | 6 | hors image : le carnet attend un service reseau |
| QuantConnect/projects | 49 | hors image : le carnet attend un service reseau |
| RL/PostTraining | 1 | hors image : le carnet attend un service reseau |

## Poids du manifeste

| Paquet | Mo | Groupes qui le declarent |
|---|---:|---:|
| `torch` | 900 | 8 |
| `tensorflow` | 800 | 1 |
| `bitsandbytes` | 120 | 1 |
| `jax` | 120 | 1 |
| `scikit-learn` | 90 | 7 |
| `opencv-python` | 80 | 2 |
| `pandas` | 70 | 11 |
| `scipy` | 70 | 9 |
| `spacy` | 70 | 1 |
| `transformers` | 70 | 3 |

L'empreinte estimee du manifeste consolide est de 3278 Mo, pour un budget unitaire de 2000 Mo applique a l'increment propre de chaque groupe. L'ecart est une information, pas un defaut du manifeste : c'est au Pli 1.2 de decider s'il scinde l'image ou s'il cible un sous-ensemble des groupes inclus.

## Manifeste consolide

Seule source de paquets de l'image d'apprentissage (Pli 1.2) : elle installe exactement cette table et rien d'autre.

200 paquets, dans l'ordre alphabetique.

| Paquet | Version retenue | Declare par | Contraintes rencontrees |
|---|---|---|---|
| `accelerate` | `>=0.25.0` | GenAI/(racine) | >=0.25.0 |
| `agent-framework-openai` | `>=1.3.0` | SymbolicAI/Lean | >=1.3.0 |
| `aiohttp` | `>=3.8.0` | GenAI/(racine) | >=3.8.0 |
| `anthropic` | `>=0.25.0` | GenAI/(racine), QuantConnect/(racine), SymbolicAI/Lean, SymbolicAI/SemanticWeb | >=0.18.0, >=0.20.0, >=0.21.0, >=0.25.0 |
| `antropy` | `<0.2` | IIT/(racine) | <0.2 |
| `anyio` | `>=4.0.0` | GenAI/(racine) | >=4.0.0 |
| `arch` | `>=6.1.0` | QuantConnect/(racine) | >=6.1.0 |
| `arviz` | `>=1.0` | Probas/(racine) | >=1.0 |
| `asyncio-throttle` | `>=1.0.0` | GenAI/(racine) | >=1.0.0 |
| `audiocraft` | `>=1.0.0` | GenAI/(racine) | >=1.0.0 |
| `automata-lib` | `>=9.2.0` | Search/(racine), Search/Part1-Foundations | >=7.1.0, >=9.2.0 |
| `av` | `>=11.0.0` | GenAI/(racine) | >=11.0.0 |
| `axelrod` | `>=4.0.0` | GameTheory/(racine) | >=4.0.0 |
| `bark` | `>=0.1.0` | GenAI/(racine) | >=0.1.0 |
| `basicsr` | `>=1.4.2` | GenAI/(racine) | >=1.4.2 |
| `bcrypt` | `>=4.0.0` | GenAI/(racine) | >=4.0.0 |
| `beautifulsoup4` | `>=4.12.0` | GenAI/(racine) | >=4.12.0 |
| `bitsandbytes` | `>=0.41.0` | GenAI/(racine) | >=0.41.0 |
| `black` | `>=24.0.0` | GenAI/Vibe-Coding, QuantConnect/(racine) | >=23.0.0, >=24.0.0 |
| `catboost` | `>=1.2.0` | QuantConnect/(racine) | >=1.2.0 |
| `chromadb` | `(non borne)` | cross-series/matching-cv | (aucune) |
| `cloudpickle` | `>=3.0.0` | QuantConnect/(racine) | >=3.0.0 |
| `coinbase-advanced-py` | `>=1.8.4` | QuantConnect/projects | >=1.8.4 |
| `cvxpy` | `>=1.5` | ML/DataScienceWithAgents, QuantConnect/(racine), Search/(racine) | >=1.4.0, >=1.5 |
| `datasets` | `>=5.0` | GenAI/(racine), RL/(racine) | >=2.14.0, >=5.0 |
| `dd` | `>=0.6` | Sudoku/(racine) | >=0.6 |
| `deap` | `>=1.4` | Search/(racine) | >=1.4 |
| `demucs` | `>=4.0.0` | GenAI/(racine) | >=4.0.0 |
| `dice-ml` | `(non borne)` | ML/DataScienceWithAgents | (aucune) |
| `difflogic` | `(non borne)` | SymbolicAI/SymbolicLearning | (aucune) |
| `diffprivlib` | `==0.6.6` | ML/DataScienceWithAgents | ==0.6.6 |
| `diffusers` | `>=0.24.0` | GenAI/(racine) | >=0.24.0 |
| `dowhy` | `>=0.12` | GameTheory/(racine), Probas/(racine) | >=0.12 |
| `duckduckgo-search` | `>=4.0.0` | ML/DataScienceWithAgents | >=4.0.0 |
| `elevenlabs` | `>=0.2.0` | GenAI/(racine) | >=0.2.0 |
| `empyrical` | `>=0.5.5` | QuantConnect/(racine) | >=0.5.5 |
| `eth-tester` | `>=0.13.0b1` | SymbolicAI/SmartContracts | >=0.13.0b1 |
| `fastapi` | `>=0.115` | GenAI/Texte, Search/Part1-Foundations, Search/Part4-Metaheuristics | >=0.115 |
| `faster-whisper` | `>=0.10.0` | GenAI/(racine) | >=0.10.0 |
| `flake8` | `>=7.0.0` | GenAI/Vibe-Coding, QuantConnect/(racine) | >=6.0.0, >=7.0.0 |
| `flask` | `(non borne)` | cross-series/matching-cv | (aucune) |
| `google-adk` | `==2.8.0` | ML/DataScienceWithAgents | ==2.8.0 |
| `google-cloud-aiplatform` | `>=1.40.0` | ML/DataScienceWithAgents | >=1.40.0 |
| `google-cloud-bigquery` | `>=3.0.0` | ML/DataScienceWithAgents | >=3.0.0 |
| `google-generativeai` | `>=0.8.0` | ML/DataScienceWithAgents | >=0.8.0 |
| `graphviz` | `>=0.20` | GameTheory/(racine), Search/(racine) | >=0.20 |
| `groundingdino-py` | `>=0.1.0` | GenAI/(racine) | >=0.1.0 |
| `gymnasium` | `>=0.29.0` | QuantConnect/(racine), RL/(racine) | >=0.29, >=0.29.0 |
| `highway-env` | `>=1.8` | RL/(racine) | >=1.8 |
| `hmmlearn` | `>=0.3` | Probas/(racine) | >=0.3 |
| `httpcore` | `>=1.0.0` | GenAI/(racine) | >=1.0.0 |
| `httpx` | `>=0.27.0` | GenAI/(racine), GenAI/Texte, Search/Part1-Foundations, Search/Part4-Metaheuristics | >=0.27, >=0.27.0 |
| `huggingface-hub` | `>=0.20.0` | GenAI/(racine) | >=0.20.0 |
| `ib-insync` | `>=0.9.86` | QuantConnect/projects | >=0.9.86 |
| `imageio` | `>=2.31.0` | GenAI/(racine) | >=2.31.0 |
| `imageio-ffmpeg` | `>=0.4.9` | GenAI/(racine) | >=0.4.9 |
| `imbalanced-learn` | `(non borne)` | ML/DataScienceWithAgents | (aucune) |
| `ipykernel` | `>=6.29.0` | ML/DataScienceWithAgents, QuantConnect/(racine) | >=6.0.0, >=6.29.0 |
| `ipywidgets` | `>=8.1` | GameTheory/(racine), GenAI/(racine), QuantConnect/(racine), Search/(racine) | >=8.0.0, >=8.1 |
| `jax` | `>=0.4` | Sudoku/(racine) | >=0.4 |
| `jaxtyping` | `>=0.3.0` | GenAI/(racine) | >=0.3.0 |
| `joblib` | `>=1.3.0` | QuantConnect/(racine) | >=1.3.0 |
| `jpype1` | `>=1.4` | Sudoku/(racine), SymbolicAI/ArgumentAnalysis, SymbolicAI/Tweety | >=1.4 |
| `jsonschema` | `>=4.23` | GenAI/Texte | >=4.23 |
| `jupyter` | `>=1.0.0` | GenAI/(racine), ML/DataScienceWithAgents, Probas/Infer, QuantConnect/(racine) | >=1.0.0 |
| `jupyter-client` | `>=7.0.0` | Probas/Infer | >=7.0.0 |
| `jupyter-kernel-gateway` | `>=3.0` | GameTheory/gateway, SymbolicAI/SMT | >=3.0 |
| `jupyter-ui-poll` | `>=1.0.0` | GenAI/(racine) | >=1.0.0 |
| `jupyterlab` | `>=4.0.0` | ML/DataScienceWithAgents, QuantConnect/(racine) | >=4.0.0 |
| `kaggle` | `>=1.6.0` | ML/DataScienceWithAgents | >=1.6.0 |
| `keras` | `>=3.0.0` | QuantConnect/(racine) | >=3.0.0 |
| `kglab` | `>=0.6.0` | SymbolicAI/SemanticWeb | >=0.6.0 |
| `langchain` | `>=0.3.0` | ML/DataScienceWithAgents, QuantConnect/(racine) | >=0.1.0, >=0.3.0 |
| `langchain-community` | `>=0.3.0` | ML/DataScienceWithAgents | >=0.3.0 |
| `langchain-core` | `>=0.3.0` | ML/DataScienceWithAgents | >=0.3.0 |
| `langchain-experimental` | `>=0.3.0` | ML/DataScienceWithAgents | >=0.3.0 |
| `langchain-openai` | `>=0.2.0` | ML/DataScienceWithAgents, QuantConnect/(racine) | >=0.0.5, >=0.2.0 |
| `langgraph` | `>=0.2.0` | ML/DataScienceWithAgents | >=0.2.0 |
| `libreyolo` | `==1.6.0` | ML/DataScienceWithAgents | ==1.6.0 |
| `librosa` | `>=0.10.0` | GenAI/(racine) | >=0.10.0 |
| `lightgbm` | `>=4.0.0` | QuantConnect/(racine) | >=4.0.0 |
| `lime` | `(non borne)` | ML/DataScienceWithAgents | (aucune) |
| `litellm` | `==1.100.4` | ML/DataScienceWithAgents | ==1.100.4 |
| `loguru` | `>=0.7.0` | QuantConnect/(racine) | >=0.7.0 |
| `ltntorch` | `>=1.0` | SymbolicAI/SymbolicLearning | >=1.0 |
| `lxml` | `>=5.0.0` | GenAI/(racine) | >=5.0.0 |
| `matching` | `(non borne)` | cross-series/matching-cv | (aucune) |
| `matplotlib` | `>=3.7.0` | CaseStudies/(racine), GameTheory/(racine), GenAI/(racine), IIT/(racine), ML/DataScienceWithAgents, Probas/(racine), QuantConnect/(racine), RL/(racine), Search/(racine), Sudoku/(racine), SymbolicAI/Lean, SymbolicAI/Planners, SymbolicAI/SMT, SymbolicAI/SemanticWeb, SymbolicAI/SmartContracts, SymbolicAI/SymbolicLearning, SymbolicAI/Tweety | >=3.5, >=3.7, >=3.7.0 |
| `mealpy` | `>=3.0` | Search/(racine), Sudoku/(racine) | >=3.0 |
| `mlflow` | `>=2.10.0` | ML/DataScienceWithAgents | >=2.10.0 |
| `moviepy` | `>=2.0` | GenAI/(racine), RL/(racine) | >=1.0, >=2.0 |
| `mpyc` | `>=0.10` | SymbolicAI/SmartContracts | >=0.10 |
| `nashpy` | `>=0.0.40` | GameTheory/(racine) | >=0.0.40 |
| `nbformat` | `>=5.0.0` | Probas/Infer | >=5.0.0 |
| `nest-asyncio` | `>=1.6.0` | SymbolicAI/ArgumentAnalysis, SymbolicAI/Lean | >=1.5, >=1.6.0 |
| `networkx` | `>=3.1` | GameTheory/(racine), Probas/(racine), Search/(racine), Sudoku/(racine), SymbolicAI/Planners, SymbolicAI/SemanticWeb, SymbolicAI/Tweety | >=3.0, >=3.1 |
| `newsapi-python` | `>=0.2.7` | QuantConnect/(racine) | >=0.2.7 |
| `numpy` | `>=1.24.0` | CaseStudies/(racine), GameTheory/(racine), GenAI/(racine), IIT/(racine), ML/DataScienceWithAgents, Probas/(racine), QuantConnect/(racine), RL/(racine), Search/(racine), Sudoku/(racine), SymbolicAI/Planners, SymbolicAI/SymbolicLearning, cross-series/matching-cv | >=1.21, >=1.24, >=1.24.0 |
| `numpyro` | `>=0.12` | Sudoku/(racine) | >=0.12 |
| `open-spiel` | `>=2.0` | GameTheory/(racine), GameTheory/gateway | >=1.4, >=2.0 |
| `openai` | `==2.24.0` | GenAI/(racine), GenAI/Texte, ML/DataScienceWithAgents, QuantConnect/(racine), Sudoku/(racine), SymbolicAI/ArgumentAnalysis, SymbolicAI/Lean, SymbolicAI/SemanticWeb, SymbolicAI/SmartContracts, SymbolicAI/SymbolicLearning | ==2.24.0, >=1.0, >=1.0.0, >=1.12.0, >=1.55, >=2.0.0 |
| `opencv-python` | `>=4.8.0` | GenAI/(racine), ML/DataScienceWithAgents | >=4.8.0 |
| `opentelemetry-sdk` | `>=1.20.0` | SymbolicAI/Lean | >=1.20.0 |
| `optuna` | `>=3.5.0` | ML/DataScienceWithAgents, Search/(racine) | >=3.0, >=3.5.0 |
| `ortools` | `>=9.11` | CaseStudies/(racine), GameTheory/(racine), Search/(racine), Sudoku/(racine), SymbolicAI/Planners | >=9.11, >=9.8 |
| `owlready2` | `>=0.45` | SymbolicAI/SemanticWeb | >=0.45 |
| `owlrl` | `>=0.4.0` | SymbolicAI/SemanticWeb | >=0.4.0 |
| `pandas` | `>=2.0.0` | CaseStudies/(racine), GameTheory/(racine), GenAI/(racine), ML/DataScienceWithAgents, Probas/(racine), QuantConnect/(racine), RL/(racine), Search/(racine), Sudoku/(racine), SymbolicAI/SemanticWeb, cross-series/matching-cv | >=2.0, >=2.0.0 |
| `pandas-ta` | `>=0.3.14b0` | QuantConnect/(racine) | >=0.3.14b0 |
| `papermill` | `>=2.4.0` | Probas/Infer, Search/(racine), Sudoku/(racine) | >=2.4, >=2.4.0 |
| `pettingzoo` | `>=1.24.0` | RL/(racine) | >=1.24.0 |
| `phe` | `>=1.5` | SymbolicAI/SmartContracts | >=1.5 |
| `pillow` | `>=10.0.0` | GenAI/(racine), ML/DataScienceWithAgents | >=10.0.0 |
| `pillow-heif` | `>=0.13.0` | GenAI/(racine) | >=0.13.0 |
| `playwright` | `(non borne)` | cross-series/matching-cv | (aucune) |
| `plotly` | `>=5.14.0` | QuantConnect/(racine) | >=5.14.0 |
| `pulp` | `>=2.8.0` | Search/(racine) | >=2.8.0 |
| `py-ecc` | `>=7.0` | SymbolicAI/SmartContracts | >=7.0 |
| `py-evm` | `>=0.12.1b1` | SymbolicAI/SmartContracts | >=0.12.1b1 |
| `py-solc-x` | `>=1.1` | SymbolicAI/SmartContracts | >=1.1 |
| `pyarrow` | `>=26.0.0` | GameTheory/(racine), GenAI/(racine) | >=14.0.0, >=26.0.0 |
| `pycryptodome` | `>=3.20` | SymbolicAI/SmartContracts | >=3.20 |
| `pydantic` | `==2.12.5` | GenAI/Texte, ML/DataScienceWithAgents, QuantConnect/(racine) | ==2.12.5, >=2.6.0, >=2.7 |
| `pydantic-settings` | `>=2.1.0` | ML/DataScienceWithAgents, QuantConnect/(racine) | >=2.0.0, >=2.1.0 |
| `pydub` | `>=0.25.0` | GenAI/(racine) | >=0.25.0 |
| `pyemd` | `==0.5.1` | IIT/(racine) | ==0.5.1 |
| `pyfolio` | `>=0.9.2` | QuantConnect/(racine) | >=0.9.2 |
| `pygad` | `>=3.3` | Search/(racine), Sudoku/(racine) | >=3.3 |
| `pymc` | `>=6.0` | Probas/(racine) | >=6.0 |
| `pymoo` | `>=0.6` | Search/(racine) | >=0.6 |
| `pyphi` | `==1.2.0` | IIT/(racine) | ==1.2.0 |
| `pyportfolioopt` | `>=1.5.5` | QuantConnect/(racine) | >=1.5.5 |
| `pyro-ppl` | `>=1.8` | CaseStudies/(racine), Probas/(racine) | >=1.8 |
| `pyshacl` | `>=0.27.0` | SymbolicAI/SemanticWeb | >=0.27.0 |
| `pytest` | `>=8.0.0` | GameTheory/(racine), GenAI/Vibe-Coding, QuantConnect/(racine), Search/Part1-Foundations, Search/Part4-Metaheuristics, SymbolicAI/Lean, cross-series/matching-cv | >=7.0.0, >=8.0.0 |
| `pytest-asyncio` | `>=0.23.0` | SymbolicAI/Lean | >=0.23.0 |
| `pytest-html` | `(non borne)` | cross-series/matching-cv | (aucune) |
| `pytest-playwright` | `(non borne)` | cross-series/matching-cv | (aucune) |
| `python-binance` | `>=1.0.37` | QuantConnect/projects | >=1.0.37 |
| `python-bitcoinlib` | `>=0.12` | SymbolicAI/SmartContracts | >=0.12 |
| `python-constraint` | `>=1.4.0` | Search/(racine) | >=1.4.0 |
| `python-dotenv` | `>=1.0.0` | GameTheory/(racine), GenAI/(racine), ML/DataScienceWithAgents, QuantConnect/(racine), SymbolicAI/ArgumentAnalysis, SymbolicAI/Lean, SymbolicAI/SmartContracts, SymbolicAI/SymbolicLearning, cross-series/matching-cv | >=1.0, >=1.0.0 |
| `python-sat` | `>=1.8.dev13` | GameTheory/(racine), Search/(racine), SymbolicAI/ArgumentAnalysis, SymbolicAI/Tweety | >=0.1, >=0.1.8, >=1.8.dev13 |
| `pyvis` | `>=0.3.0` | SymbolicAI/SemanticWeb | >=0.3.0 |
| `quantconnect-lean` | `>=2.5.14000` | QuantConnect/(racine) | >=2.5.14000 |
| `quantconnect-stubs` | `>=14.0.0` | QuantConnect/(racine) | >=14.0.0 |
| `qwen-vl-utils` | `>=0.0.1` | GenAI/(racine) | >=0.0.1 |
| `rdflib` | `>=7.0.0` | CaseStudies/(racine), SymbolicAI/SemanticWeb, SymbolicAI/SymbolicLearning | >=7.0, >=7.0.0 |
| `realesrgan` | `>=0.3.0` | GenAI/(racine) | >=0.3.0 |
| `reasonable` | `>=0.1.0` | SymbolicAI/SemanticWeb | >=0.1.0 |
| `regex` | `>=2023.0` | Sudoku/(racine) | >=2023.0 |
| `requests` | `>=2.31.0` | GenAI/(racine), ML/DataScienceWithAgents, QuantConnect/(racine), SymbolicAI/ArgumentAnalysis, SymbolicAI/SemanticWeb, SymbolicAI/SmartContracts, SymbolicAI/Tweety | >=2.28, >=2.31, >=2.31.0 |
| `rustuna` | `>=0.1.0` | Search/(racine) | >=0.1.0 |
| `safetensors` | `>=0.4.0` | GenAI/(racine) | >=0.4.0 |
| `scikit-learn` | `==1.5.2` | GenAI/(racine), ML/DataScienceWithAgents, Probas/(racine), QuantConnect/(racine), Search/(racine), SymbolicAI/SymbolicLearning, cross-series/matching-cv | ==1.5.2, >=1.2, >=1.3, >=1.3.0 |
| `scipy` | `==1.14.1` | GameTheory/(racine), GenAI/(racine), IIT/(racine), ML/DataScienceWithAgents, Probas/(racine), QuantConnect/(racine), Search/(racine), Sudoku/(racine), SymbolicAI/SymbolicLearning | ==1.14.1, >=0.13.3, >=1.10, >=1.10.0, >=1.11 |
| `seaborn` | `>=0.12.0` | CaseStudies/(racine), GameTheory/(racine), ML/DataScienceWithAgents, QuantConnect/(racine) | >=0.12, >=0.12.0 |
| `semantic-kernel` | `>=1.39.0` | GenAI/(racine), SymbolicAI/ArgumentAnalysis, SymbolicAI/Lean, cross-series/matching-cv | >=1.0, >=1.0.0, >=1.39.0 |
| `sentencepiece` | `>=0.1.99` | GenAI/(racine) | >=0.1.99 |
| `shap` | `(non borne)` | ML/DataScienceWithAgents | (aucune) |
| `shimmy` | `>=1.3.0` | QuantConnect/(racine) | >=1.3.0 |
| `simanneal` | `>=0.5` | Sudoku/(racine) | >=0.5 |
| `soundfile` | `>=0.12.0` | GenAI/(racine) | >=0.12.0 |
| `spacy` | `>=3.7.0` | QuantConnect/(racine) | >=3.7.0 |
| `sparqlwrapper` | `>=2.0.0` | SymbolicAI/SemanticWeb | >=2.0.0 |
| `stable-baselines3` | `>=2.2.0` | QuantConnect/(racine), RL/(racine) | >=2.0, >=2.2.0 |
| `statsmodels` | `(non borne)` | ML/DataScienceWithAgents | (aucune) |
| `sympy` | `>=1.12` | GameTheory/(racine) | >=1.12 |
| `ta-lib` | `>=0.4.28` | QuantConnect/(racine) | >=0.4.28 |
| `tabulate` | `>=0.9` | SymbolicAI/SmartContracts | >=0.9 |
| `tavily-python` | `>=0.3.0` | ML/DataScienceWithAgents | >=0.3.0 |
| `tenseal` | `>=0.3` | SymbolicAI/SmartContracts | >=0.3 |
| `tensorflow` | `>=2.15.0` | QuantConnect/(racine) | >=2.15.0 |
| `tensorflow-probability` | `>=0.23.0` | QuantConnect/(racine) | >=0.23.0 |
| `textblob` | `>=0.17.0` | QuantConnect/(racine) | >=0.17.0 |
| `tiktoken` | `>=0.7.0` | GenAI/(racine) | >=0.7.0 |
| `tokenizers` | `>=0.21` | RL/(racine) | >=0.21 |
| `torch` | `==2.14.0` | CaseStudies/(racine), GenAI/(racine), ML/DataScienceWithAgents, Probas/(racine), RL/(racine), Sudoku/(racine), SymbolicAI/Planners, SymbolicAI/SymbolicLearning | ==2.14.0, >=2.0, >=2.0.0, >=2.13 |
| `torchaudio` | `>=2.0.0` | GenAI/(racine) | >=2.0.0 |
| `torchlens` | `==3.0.3` | IIT/ICT-Series | ==3.0.3 |
| `torchvision` | `==0.29.0` | GenAI/(racine), ML/DataScienceWithAgents, SymbolicAI/SymbolicLearning | ==0.29.0, >=0.15.0 |
| `tqdm` | `>=4.66.0` | GameTheory/(racine), GenAI/(racine), QuantConnect/(racine), SymbolicAI/SemanticWeb, SymbolicAI/SymbolicLearning, SymbolicAI/Tweety | >=4.65, >=4.65.0, >=4.66.0 |
| `transformers` | `>=5.12` | GenAI/(racine), QuantConnect/(racine), RL/(racine) | >=4.35.0, >=4.37.0, >=5.12 |
| `trl` | `>=1.10` | RL/(racine) | >=1.10 |
| `tts` | `>=0.22.0` | GenAI/(racine) | >=0.22.0 |
| `ultralytics` | `==8.4.173` | ML/DataScienceWithAgents | ==8.4.173 |
| `umap-learn` | `(non borne)` | ML/DataScienceWithAgents | (aucune) |
| `unified-planning` | `>=1.1` | SymbolicAI/Planners | >=1.1 |
| `up-aries` | `>=0.5` | SymbolicAI/Planners | >=0.5 |
| `up-fast-downward` | `>=1.0` | SymbolicAI/Planners | >=1.0 |
| `up-pyperplan` | `>=1.1` | SymbolicAI/Planners | >=1.1 |
| `uvicorn` | `>=0.30` | GenAI/Texte, Search/Part1-Foundations, Search/Part4-Metaheuristics | >=0.30 |
| `vadersentiment` | `>=3.3.2` | QuantConnect/(racine) | >=3.3.2 |
| `vyper` | `>=0.4` | SymbolicAI/SmartContracts | >=0.4 |
| `web3` | `>=7.0` | SymbolicAI/SmartContracts | >=7.0 |
| `werkzeug` | `(non borne)` | cross-series/matching-cv | (aucune) |
| `xgboost` | `>=2.0.0` | QuantConnect/(racine) | >=2.0.0 |
| `xrpl-py` | `>=3.0` | SymbolicAI/SmartContracts | >=3.0 |
| `yfinance` | `>=0.2.36` | Probas/(racine), QuantConnect/(racine) | >=0.2, >=0.2.36 |
| `z3-solver` | `>=4.13` | CaseStudies/(racine), GameTheory/(racine), Search/(racine), Sudoku/(racine), SymbolicAI/SMT, SymbolicAI/Tweety | >=4.12, >=4.13 |

## Conflits de versions

Aucun conflit dur : aucune contrainte n'est contredite par une autre.

## Divergences de bornes

Un paquet declare par plusieurs series avec des contraintes differentes n'est pas un conflit : c'est la contrainte la plus exigeante qui est retenue. Chaque ligne dit lesquelles.

| Paquet | Version retenue | Contraintes | Series |
|---|---|---|---|
| `anthropic` | `>=0.25.0` | >=0.18.0, >=0.20.0, >=0.21.0, >=0.25.0 | GenAI/(racine), QuantConnect/(racine), SymbolicAI/Lean, SymbolicAI/SemanticWeb |
| `automata-lib` | `>=9.2.0` | >=7.1.0, >=9.2.0 | Search/(racine), Search/Part1-Foundations |
| `black` | `>=24.0.0` | >=23.0.0, >=24.0.0 | GenAI/Vibe-Coding, QuantConnect/(racine) |
| `cvxpy` | `>=1.5` | >=1.4.0, >=1.5 | ML/DataScienceWithAgents, QuantConnect/(racine), Search/(racine) |
| `datasets` | `>=5.0` | >=2.14.0, >=5.0 | GenAI/(racine), RL/(racine) |
| `flake8` | `>=7.0.0` | >=6.0.0, >=7.0.0 | GenAI/Vibe-Coding, QuantConnect/(racine) |
| `gymnasium` | `>=0.29.0` | >=0.29, >=0.29.0 | QuantConnect/(racine), RL/(racine) |
| `httpx` | `>=0.27.0` | >=0.27, >=0.27.0 | GenAI/(racine), GenAI/Texte, Search/Part1-Foundations, Search/Part4-Metaheuristics |
| `ipykernel` | `>=6.29.0` | >=6.0.0, >=6.29.0 | ML/DataScienceWithAgents, QuantConnect/(racine) |
| `ipywidgets` | `>=8.1` | >=8.0.0, >=8.1 | GameTheory/(racine), GenAI/(racine), QuantConnect/(racine), Search/(racine) |
| `langchain` | `>=0.3.0` | >=0.1.0, >=0.3.0 | ML/DataScienceWithAgents, QuantConnect/(racine) |
| `langchain-openai` | `>=0.2.0` | >=0.0.5, >=0.2.0 | ML/DataScienceWithAgents, QuantConnect/(racine) |
| `matplotlib` | `>=3.7.0` | >=3.5, >=3.7, >=3.7.0 | CaseStudies/(racine), GameTheory/(racine), GenAI/(racine), IIT/(racine), ML/DataScienceWithAgents, Probas/(racine), QuantConnect/(racine), RL/(racine), Search/(racine), Sudoku/(racine), SymbolicAI/Lean, SymbolicAI/Planners, SymbolicAI/SMT, SymbolicAI/SemanticWeb, SymbolicAI/SmartContracts, SymbolicAI/SymbolicLearning, SymbolicAI/Tweety |
| `moviepy` | `>=2.0` | >=1.0, >=2.0 | GenAI/(racine), RL/(racine) |
| `nest-asyncio` | `>=1.6.0` | >=1.5, >=1.6.0 | SymbolicAI/ArgumentAnalysis, SymbolicAI/Lean |
| `networkx` | `>=3.1` | >=3.0, >=3.1 | GameTheory/(racine), Probas/(racine), Search/(racine), Sudoku/(racine), SymbolicAI/Planners, SymbolicAI/SemanticWeb, SymbolicAI/Tweety |
| `numpy` | `>=1.24.0` | >=1.21, >=1.24, >=1.24.0 | CaseStudies/(racine), GameTheory/(racine), GenAI/(racine), IIT/(racine), ML/DataScienceWithAgents, Probas/(racine), QuantConnect/(racine), RL/(racine), Search/(racine), Sudoku/(racine), SymbolicAI/Planners, SymbolicAI/SymbolicLearning, cross-series/matching-cv |
| `open-spiel` | `>=2.0` | >=1.4, >=2.0 | GameTheory/(racine), GameTheory/gateway |
| `openai` | `==2.24.0` | ==2.24.0, >=1.0, >=1.0.0, >=1.12.0, >=1.55, >=2.0.0 | GenAI/(racine), GenAI/Texte, ML/DataScienceWithAgents, QuantConnect/(racine), Sudoku/(racine), SymbolicAI/ArgumentAnalysis, SymbolicAI/Lean, SymbolicAI/SemanticWeb, SymbolicAI/SmartContracts, SymbolicAI/SymbolicLearning |
| `optuna` | `>=3.5.0` | >=3.0, >=3.5.0 | ML/DataScienceWithAgents, Search/(racine) |
| `ortools` | `>=9.11` | >=9.11, >=9.8 | CaseStudies/(racine), GameTheory/(racine), Search/(racine), Sudoku/(racine), SymbolicAI/Planners |
| `pandas` | `>=2.0.0` | >=2.0, >=2.0.0 | CaseStudies/(racine), GameTheory/(racine), GenAI/(racine), ML/DataScienceWithAgents, Probas/(racine), QuantConnect/(racine), RL/(racine), Search/(racine), Sudoku/(racine), SymbolicAI/SemanticWeb, cross-series/matching-cv |
| `papermill` | `>=2.4.0` | >=2.4, >=2.4.0 | Probas/Infer, Search/(racine), Sudoku/(racine) |
| `pyarrow` | `>=26.0.0` | >=14.0.0, >=26.0.0 | GameTheory/(racine), GenAI/(racine) |
| `pydantic` | `==2.12.5` | ==2.12.5, >=2.6.0, >=2.7 | GenAI/Texte, ML/DataScienceWithAgents, QuantConnect/(racine) |
| `pydantic-settings` | `>=2.1.0` | >=2.0.0, >=2.1.0 | ML/DataScienceWithAgents, QuantConnect/(racine) |
| `pytest` | `>=8.0.0` | >=7.0.0, >=8.0.0 | GameTheory/(racine), GenAI/Vibe-Coding, QuantConnect/(racine), Search/Part1-Foundations, Search/Part4-Metaheuristics, SymbolicAI/Lean, cross-series/matching-cv |
| `python-dotenv` | `>=1.0.0` | >=1.0, >=1.0.0 | GameTheory/(racine), GenAI/(racine), ML/DataScienceWithAgents, QuantConnect/(racine), SymbolicAI/ArgumentAnalysis, SymbolicAI/Lean, SymbolicAI/SmartContracts, SymbolicAI/SymbolicLearning, cross-series/matching-cv |
| `python-sat` | `>=1.8.dev13` | >=0.1, >=0.1.8, >=1.8.dev13 | GameTheory/(racine), Search/(racine), SymbolicAI/ArgumentAnalysis, SymbolicAI/Tweety |
| `rdflib` | `>=7.0.0` | >=7.0, >=7.0.0 | CaseStudies/(racine), SymbolicAI/SemanticWeb, SymbolicAI/SymbolicLearning |
| `requests` | `>=2.31.0` | >=2.28, >=2.31, >=2.31.0 | GenAI/(racine), ML/DataScienceWithAgents, QuantConnect/(racine), SymbolicAI/ArgumentAnalysis, SymbolicAI/SemanticWeb, SymbolicAI/SmartContracts, SymbolicAI/Tweety |
| `scikit-learn` | `==1.5.2` | ==1.5.2, >=1.2, >=1.3, >=1.3.0 | GenAI/(racine), ML/DataScienceWithAgents, Probas/(racine), QuantConnect/(racine), Search/(racine), SymbolicAI/SymbolicLearning, cross-series/matching-cv |
| `scipy` | `==1.14.1` | ==1.14.1, >=0.13.3, >=1.10, >=1.10.0, >=1.11 | GameTheory/(racine), GenAI/(racine), IIT/(racine), ML/DataScienceWithAgents, Probas/(racine), QuantConnect/(racine), Search/(racine), Sudoku/(racine), SymbolicAI/SymbolicLearning |
| `seaborn` | `>=0.12.0` | >=0.12, >=0.12.0 | CaseStudies/(racine), GameTheory/(racine), ML/DataScienceWithAgents, QuantConnect/(racine) |
| `semantic-kernel` | `>=1.39.0` | >=1.0, >=1.0.0, >=1.39.0 | GenAI/(racine), SymbolicAI/ArgumentAnalysis, SymbolicAI/Lean, cross-series/matching-cv |
| `stable-baselines3` | `>=2.2.0` | >=2.0, >=2.2.0 | QuantConnect/(racine), RL/(racine) |
| `torch` | `==2.14.0` | ==2.14.0, >=2.0, >=2.0.0, >=2.13 | CaseStudies/(racine), GenAI/(racine), ML/DataScienceWithAgents, Probas/(racine), RL/(racine), Sudoku/(racine), SymbolicAI/Planners, SymbolicAI/SymbolicLearning |
| `torchvision` | `==0.29.0` | ==0.29.0, >=0.15.0 | GenAI/(racine), ML/DataScienceWithAgents, SymbolicAI/SymbolicLearning |
| `tqdm` | `>=4.66.0` | >=4.65, >=4.65.0, >=4.66.0 | GameTheory/(racine), GenAI/(racine), QuantConnect/(racine), SymbolicAI/SemanticWeb, SymbolicAI/SymbolicLearning, SymbolicAI/Tweety |
| `transformers` | `>=5.12` | >=4.35.0, >=4.37.0, >=5.12 | GenAI/(racine), QuantConnect/(racine), RL/(racine) |
| `yfinance` | `>=0.2.36` | >=0.2, >=0.2.36 | Probas/(racine), QuantConnect/(racine) |
| `z3-solver` | `>=4.13` | >=4.12, >=4.13 | CaseStudies/(racine), GameTheory/(racine), Search/(racine), Sudoku/(racine), SymbolicAI/SMT, SymbolicAI/Tweety |

## Consommation par l'image 1.2

Contrat du Pli 1.2 : le `Dockerfile` de `docker-configurations/notebook-runner` prendra ses paquets de `kernel-manifest.json` (cle `manifest`), sans liste paralleve. Aujourd'hui le `Dockerfile` porte encore sa propre liste : c'est le Pli 1.2 qui la remplace. Apres ce remplacement, un paquet absent du manifeste n'entre pas dans l'image, et ajouter un paquet se fait par un fichier `requirements` du depot puis par regeneration de ce manifeste.
