# AIMA : des tables des matieres aux carnets du dépôt

> Données : les deux éditions d'*Artificial Intelligence: A Modern Approach*
> (Russell & Norvig), lues dans les copies archivées du gisement
> (`G:\Mon Drive\MyIA\IA\Bibliographie IA\AI`) ; les PDF ne sont jamais committés.
> Ce document est **généré** par `scripts/research/aima_mapping.py`.

## Ce que contient ce dossier

| Fichier | Contenu |
|---|---|
| `aima3e-toc.json` | table des matières de la 3e édition (parties, chapitres, sections, page imprimée, page PDF) |
| `aima4e-toc.json` | idem pour la 4e édition |
| `ecarts-3e-4e.json` | ce qui est ajouté, retiré, renommé ou renuméroté entre les deux éditions |
| `couverture-3e.json` · `couverture-4e.json` | section → concepts → carnets du dépôt, avec la preuve (terme trouvé) |

## 1. Méthode — quatre étapes reproductibles

```bash
python scripts/research/aima_mapping.py extract   # les deux tables des matières
python scripts/research/aima_mapping.py diff      # les écarts 3e → 4e
python scripts/research/aima_mapping.py coverage  # la correspondance avec les carnets
python scripts/research/aima_mapping.py rapport   # ce document
```

**3e édition** — la structure vient de l'outline du PDF (niveaux 1/2/3 = partie/chapitre/section). La page imprimée est lue dans le sommaire imprimé, ligne par ligne et par coordonnées : à gauche le numéro, au centre le titre, à droite la page. L’offset du corps (page PDF − page imprimée) est ensuite appliqué à toutes les entrées et vérifié une à une.

**4e édition** — la structure et la page imprimée sont lues dans le sommaire imprimé (pages PDF 16 à 26). L’ancre de vérification est la page du corps où le titre de la section s’ouvre : une section par sa ligne « N.M Titre », un chapitre par la ligne « Chapter N » suivie de son titre. Les titres coupés sur deux lignes dans le corps sont reconstruits.

**Correspondance** — les termes d’une section sont les racines des mots significatifs de son titre. Un carnet « couvre » une section si l’un de ces termes apparaît dans son markdown ou son code (les sorties de cellules ne sont pas lues). Un terme présent dans plus de 20 % des carnets est écarté : il ne prouve rien (28 termes écartés). Les JSON de couverture citent 8 carnets d’exemple par section et la liste de ses séries ; la liste complète se régénère par la commande `coverage`.

## 2. Les deux éditions en données

| | 3e édition | 4e édition |
|---|---:|---:|
| parties | 7 | 7 |
| chapitres | 27 | 28 |
| sections | 177 | 165 |
| annexes | 2 | 2 |
| entrées ancrées sur une page PDF | 206 | 195 |

Offset du corps 3e : **19** (page PDF − offset = page imprimée). Entrées divergentes : 2.

Écart avec l’[armature AIMA](../../cadrage/aima-armature.md) : sa prose annonce « 27 chapitres en 7 parties », la table des matières en compte **28** (son propre tableau en liste 28). L’écart est dans la prose de l’armature, pas dans sa carte ; ce document ne la modifie pas.

## 3. Ce qui change de la 3e à la 4e édition

- chapitres ajoutés : **10** ; retirés : **9** ; renommés : **17**
- sections ajoutées : **74** ; retirées : **60** ; renommées : **93** ; renumérotées : **41**

La comparaison porte sur les **titres**, pas sur les numéros : la 4e édition a refait sa numérotation, donc un écart de numéro ne prouve rien. Les chapitres présents en 4e et absents de la 3e (10) :

- **5 — Adversarial Search and Games**
- **11 — Automated Planning**
- **25 — Computer Vision**
- **21 — Deep Learning**
- **24 — Deep Learning for Natural Language Processing**
- **18 — Multiagent Decision Making**
- **27 — Philosophy, Ethics, and Safety of AI**
- **15 — Probabilistic Programming**
- **4 — Search in Complex Environments**
- **28 — The Future of AI**

Les chapitres de la 3e édition absents de la 4e (9) :

- **5 — Adversarial Search**
- **27 — AI: The Present and Future**
- **4 — Beyond Classical Search**
- **10 — Classical Planning**
- **19 — Knowledge in Learning**
- **23 — Natural Language for Communication**
- **24 — Perception**
- **26 — Philosophical Foundations**
- **11 — Planning and Acting in the Real World**

## 4. Correspondance 4e édition → carnets

La colonne « série » est celle de l’[armature AIMA](../../cadrage/aima-armature.md) (l’organe qui exécute) ; la colonne « sections couvertes » vient de la recherche dans le corpus (le contenu qui enseigne).

| Chap. | Titre (4e) | Série porteuse | Sections | Couvertes | Séries couvertes (3 premières, par nombre de carnets) |
|---|---|---|---:|---:|---|
| 1 | Introduction | — | 5 | 3 | `Search/Part1-Foundations`, `QuantConnect/Python`, `QuantConnect/projects` |
| 2 | Intelligent Agents | `ML/DataScienceWithAgents/Track2-GoogleADK` | 4 | 3 | `GameTheory`, `QuantConnect/projects`, `SymbolicAI/Lean` |
| 3 | Solving Problems by Searching | `Search/Part1-Foundations` | 6 | 4 | `GameTheory`, `Search/Part3-Cas-pratiques`, `Search/Part1-Foundations` |
| 4 | Search in Complex Environments | `Search/Part4-Metaheuristics` | 5 | 5 | `Search/Part3-Cas-pratiques`, `Search/Part1-Foundations`, `SymbolicAI/Lean` |
| 5 | Adversarial Search and Games | `GameTheory` | 7 | 7 | `GameTheory`, `SymbolicAI/Lean`, `Search/Part3-Cas-pratiques` |
| 6 | Constraint Satisfaction Problems | `Search/Part2-CSP`, `Sudoku`, `SymbolicAI/SMT`, `SymbolicAI/OR-tools-Stiegler.ipynb` | 5 | 4 | `Search/Part3-Cas-pratiques`, `Sudoku`, `Search/Part1-Foundations` |
| 7 | Logical Agents | `SymbolicAI/Lean` | 7 | 7 | `SymbolicAI/Lean`, `SymbolicAI/Tweety`, `QuantConnect/Python` |
| 8 | First-Order Logic | `SymbolicAI/Lean` | 4 | 4 | `SymbolicAI/Tweety`, `SymbolicAI/SymbolicLearning`, `QuantConnect/Python` |
| 9 | Inference in First-Order Logic | `SymbolicAI/Lean` | 5 | 4 | `ML/DataScienceWithAgents`, `Probas/DecisionTheory`, `Probas/PyMC` |
| 10 | Knowledge Representation | `SymbolicAI/SemanticWeb`, `SymbolicAI/Tweety`, `SymbolicAI/Argument_Analysis` | 6 | 6 | `QuantConnect/Python`, `SymbolicAI/Lean`, `SymbolicAI/Tweety` |
| 11 | Automated Planning | `SymbolicAI/Planners/02-Classical` | 7 | 7 | `SymbolicAI/Planners`, `SymbolicAI/Lean`, `QuantConnect/Python` |
| 12 | Quantifying Uncertainty | `Probas` | 7 | 7 | `SymbolicAI/Lean`, `Probas/DecisionTheory`, `ML/DataScienceWithAgents` |
| 13 | Probabilistic Reasoning | `Probas`, `Probas/DecisionTheory/Causal-Bridges` | 5 | 5 | `ML/DataScienceWithAgents`, `Probas/DecisionTheory`, `QuantConnect/Python` |
| 14 | Probabilistic Reasoning over Time | `NLP/05-HMM-Viterbi` | 5 | 5 | `QuantConnect/Python`, `QuantConnect/projects`, `ML/DataScienceWithAgents` |
| 15 | Probabilistic Programming | `Probas`, `ML/ML.Net` | 4 | 4 | `SymbolicAI/Lean`, `QuantConnect/Python`, `GameTheory` |
| 16 | Making Simple Decisions | `Probas/DecisionTheory/DecInfer` | 7 | 6 | `GameTheory`, `SymbolicAI/Lean`, `Probas/DecisionTheory` |
| 17 | Making Complex Decisions | `RL` | 5 | 5 | `GameTheory`, `Probas/DecisionTheory`, `ML/DataScienceWithAgents` |
| 18 | Multiagent Decision Making | `GameTheory`, `GameTheory/game_theory_lean` | 4 | 4 | `GameTheory`, `SymbolicAI/Lean`, `Probas/DecisionTheory` |
| 19 | Learning from Examples | `ML/ML.Net` | 9 | 8 | `ML/DataScienceWithAgents`, `GameTheory`, `SymbolicAI/Lean` |
| 20 | Learning Probabilistic Models | `ML/ML.Net`, `Probas` | 3 | 2 | `QuantConnect/Python`, `ML/DataScienceWithAgents`, `Probas/Infer` |
| 21 | Deep Learning | `ML/DataScienceWithAgents/03-Deep-Learning`, `GenAI` | 8 | 6 | `ML/DataScienceWithAgents`, `QuantConnect/Python`, `RL` |
| 22 | Reinforcement Learning | `RL`, `QuantConnect/projects` | 7 | 7 | `RL`, `QuantConnect/Python`, `GenAI/PostTraining` |
| 23 | Natural Language Processing | `NLP` | 6 | 6 | `GenAI/Texte`, `SymbolicAI/Lean`, `ML/DataScienceWithAgents` |
| 24 | Deep Learning for Natural Language Processing | `GenAI/Texte`, `GenAI/Integrations-DotNet`, `GenAI/RAG-et-Memoire-Semantique` | 6 | 5 | `ML/DataScienceWithAgents`, `GenAI/Texte`, `GenAI/Audio` |
| 25 | Computer Vision | `ML/DataScienceWithAgents/04-Vision`, `GenAI/Image`, `GenAI/Video` | 7 | 6 | `ML/DataScienceWithAgents`, `SymbolicAI/Lean`, `GenAI/Image` |
| 26 | Robotics | — | 10 | 10 | `SymbolicAI/Planners`, `Search/Part4-Metaheuristics`, `RL` |
| 27 | Philosophy, Ethics, and Safety of AI | `GenAI/Security`, `Control`, `Oversight` | 3 | 3 | `SymbolicAI/Lean`, `GenAI/Texte`, `Search/Part1-Foundations` |
| 28 | The Future of AI | — | 2 | 1 | `QuantConnect/Python`, `QuantConnect/projects`, `GameTheory` |

## 5. Sections non couvertes

15 sections de la 4e édition n’ont **aucun** carnet dont le markdown ou le code porte un terme de leur titre. La liste complète est dans `couverture-4e.json` ; voici les chapitres concernés :

| Chap. | Sections non couvertes |
|---|---|
| 1 | 2 — 1.1, 1.4 |
| 2 | 1 — 2.4 |
| 3 | 2 — 3.1, 3.2 |
| 6 | 1 — 6.5 |
| 9 | 1 — 9.5 |
| 16 | 1 — 16.6 |
| 19 | 1 — 19.8 |
| 20 | 1 — 20.2 |
| 21 | 2 — 21.4, 21.8 |
| 24 | 1 — 24.6 |
| 25 | 1 — 25.1 |
| 28 | 1 — 28.2 |

## 6. Au-delà du livre

Le dépôt exécute des séries qu’aucun chapitre de l’AIMA ne réclame : **22 séries** hors de la carte de l’armature, 389 carnets au total.

| Série (hors carte) | Carnets |
|---|---:|
| `IIT/ICT-Series` | 102 |
| `QuantConnect/Python` | 67 |
| `Search/Part3-Cas-pratiques` | 51 |
| `SymbolicAI/SmartContracts` | 32 |
| `SymbolicAI/SymbolicLearning` | 29 |
| `QuantConnect/research` | 25 |
| `QuantConnect/ML-Training-Pipeline` | 18 |
| `QuantConnect/partner-course-quant-trading` | 12 |
| `Search/Part5-Frontieres` | 11 |
| `IIT` | 10 |
| `Compression` | 7 |
| `QuantConnect/kelly_lean` | 6 |
| `Physique/Integrales` | 4 |
| `Physique/Jauge` | 3 |
| `CaseStudies/Diagnostic-Medical` | 2 |
| `CaseStudies/Oncology-Planning` | 2 |
| `CaseStudies/SmartGrid-Energy` | 2 |
| `cross-series/socle-metadata-driven` | 2 |
| `(racine)` | 1 |
| `Compression/Compression_lean` | 1 |
| `Physique/Constructeur` | 1 |
| `Physique/Numerique` | 1 |

## 7. Chapitres sans organe ou à couverture partielle

Deux mesures distinctes, à ne pas confondre : l’**organe** (la bibliothèque ou le moteur que la série appelle) et le **contenu** (un carnet dont le texte porte un terme de la section). Un chapitre peut avoir l’un sans l’autre.

| Chapitre | Organe (armature) | Sections couvertes |
|---|---|---:|
| 1 — Introduction | — aucun — | 3/5 |
| 2 — Intelligent Agents | `ML/DataScienceWithAgents/Track2-GoogleADK` | 3/4 |
| 3 — Solving Problems by Searching | `Search/Part1-Foundations` | 4/6 |
| 6 — Constraint Satisfaction Problems | `Search/Part2-CSP`, `Sudoku`, `SymbolicAI/SMT`, `SymbolicAI/OR-tools-Stiegler.ipynb` | 4/5 |
| 9 — Inference in First-Order Logic | `SymbolicAI/Lean` | 4/5 |
| 16 — Making Simple Decisions | `Probas/DecisionTheory/DecInfer` | 6/7 |
| 19 — Learning from Examples | `ML/ML.Net` | 8/9 |
| 20 — Learning Probabilistic Models | `ML/ML.Net`, `Probas` | 2/3 |
| 21 — Deep Learning | `ML/DataScienceWithAgents/03-Deep-Learning`, `GenAI` | 6/8 |
| 24 — Deep Learning for Natural Language Processing | `GenAI/Texte`, `GenAI/Integrations-DotNet`, `GenAI/RAG-et-Memoire-Semantique` | 5/6 |
| 25 — Computer Vision | `ML/DataScienceWithAgents/04-Vision`, `GenAI/Image`, `GenAI/Video` | 6/7 |
| 26 — Robotics | — aucun — | 10/10 |
| 28 — The Future of AI | — aucun — | 1/2 |

---

Reproduction : `python scripts/research/aima_mapping.py extract && python scripts/research/aima_mapping.py diff && python scripts/research/aima_mapping.py coverage && python scripts/research/aima_mapping.py rapport`.
