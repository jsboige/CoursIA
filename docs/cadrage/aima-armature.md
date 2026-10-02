# L'armature AIMA 4e dans CoursIA — carte des chapitres exécutés, et ce que nos gates ne savent pas voir

> Document de cadrage — communauté « fondateurs de la discipline » ([règle d'agrégation #17525](README.md)).
> Arc E de l'Epic #17528 (l'armature elle-même), avec l'arc C (position *benchmark-driven AI*).
> Livrable #17541. Toutes les mesures de ce document sont reproductibles par les commandes de la [section Mesure](#mesure-reproductible).

## Constat de départ

*Artificial Intelligence: A Modern Approach* (4e éd., Russell & Norvig, 2021) est la référence de cours la plus citée du dépôt : **56 carnets** la citent (motif `Modern Approach` ou `Russell…Norvig` — commande en fin de document). La citation vaut ancrage de cours, mais aucun document n'établit **quels chapitres du livre ont un organe dans nos séries, et lesquels n'en ont aucun**. Ce document dresse cette carte.

La règle de la carte : **une citation ne suffit pas — l'organe doit exécuter**. Chaque ligne nomme la bibliothèque, le moteur ou le module que la série appelle réellement. Les chemins vérifiés sont ceux de `main` au 2026-10-02.

## La carte — chapitre par chapitre

Structure de la 4e édition lue dans le sommaire du PDF du gisement (p. vii-xiii) : 27 chapitres en 7 parties, plus un appendice mathématique.

| Chap. | Titre (4e) | Série porteuse | Organe exécutant | Notebooks |
|---|---|---|---|---:|
| 1 | Introduction | — | — (chapitre de cadrage, pas d'organe par nature) | — |
| 2 | Intelligent Agents | `ML/DataScienceWithAgents/Track2-GoogleADK` | Google ADK (Agent Development Kit), p. ex. `Lab8-ADK-Introduction` | 101 |
| 3 | Solving Problems by Searching | `Search/Part1-Foundations` | A*, heuristiques (implémentations C#/Python + `Search/MetaGeneticSharp`) | 156 (série Search entière) |
| 4 | Search in Complex Environments | `Search/Part4-Metaheuristics` | métaheuristiques, algos évolutionnaires (`MetaGeneticSharp`, sous-module) | idem |
| 5 | Adversarial Search and Games | `GameTheory` | OpenSpiel (`pyspiel`), minimax/CFR/MCTS + miroirs C# | 109 |
| 6 | Constraint Satisfaction Problems | `Search/Part2-CSP` · `Sudoku` · `SymbolicAI/SMT` · `SymbolicAI/OR-tools-Stiegler.ipynb` | backtracking (`Sudoku-01-Backtracking-Csharp`), solveur SAT/SMT Z3 (`Z3-API`), Google OR-Tools | 156+38+47 |
| 7 | Logical Agents | `SymbolicAI/Lean` | Lean 4 (logique propositionnelle, satisfiabilité) | 82 |
| 8 | First-Order Logic | `SymbolicAI/Lean` | Lean 4 (FOL, quantificateurs) | 82 |
| 9 | Inference in First-Order Logic | `SymbolicAI/Lean` | Lean 4 (chaînage avant via tactiques, résolution) | 82 |
| 10 | Knowledge Representation | `SymbolicAI/SemanticWeb` · `SymbolicAI/Tweety` · `SymbolicAI/Argument_Analysis` | SPARQL/OWL (RDF), Tweety (ASP, argumentation de Dung), Argumentum (sous-module) | 28+39+32 |
| 11 | Automated Planning | `SymbolicAI/Planners/02-Classical` | Fast Downward (`Planners-4-Fast-Downward`), PDDL, heuristiques (`Planners-5`) | 25 |
| 12 | Quantifying Uncertainty | `Probas` | Infer.NET (probabilités, réseaux bayésiens) | 75 |
| 13 | Probabilistic Reasoning | `Probas` · `Probas/DecisionTheory/Causal-Bridges` | Infer.NET, do-calculus (`CausalBridges-01-Do-Calculus`) | 75 |
| 14 | Probabilistic Reasoning over Time | `NLP/05-HMM-Viterbi` | HMM, décodage de Viterbi (module numpy dédié) | 5 |
| 15 | Probabilistic Programming | `Probas` · `ML/ML.Net` | Infer.NET **est** un langage de programmation probabiliste (cf. `Infer.NETCacheHelper.cs`) | 75 |
| 16 | Making Simple Decisions | `Probas/DecisionTheory/DecInfer` | fondations d'utilité (`DecInfer-01-Utility-Foundations`, Infer.NET) | 75 |
| 17 | Making Complex Decisions | `RL` (MDP, POMDP) | PPO (`ppo_cartpole.zip`), `rl_11_pomdp` | 36 |
| 18 | Multiagent Decision Making | `GameTheory` · `GameTheory/game_theory_lean` | OpenSpiel (jeux répétés, enchères, négociation), jeux coopératifs en Lean (Shapley) | 109 |
| 19 | Learning from Examples | `ML/ML.Net` | ML.NET (classifieurs, régression, évaluation) | 23 |
| 20 | Learning Probabilistic Models | `ML/ML.Net` · `Probas` | EM/clustering ML.NET, mélanges Infer.NET | — (transversal, pas de sous-série dédiée) |
| 21 | Deep Learning | `ML/DataScienceWithAgents/03-DeepLearning` · `GenAI` | torch (entraînements GPU), pile GenAI | 101 (série) |
| 22 | Reinforcement Learning | `RL` · `QuantConnect/projects` (ML-Training-Pipeline) | PPO/Decision Transformer/LSTM du pipeline QC (multi-seed, DM) | 36+220 |
| 23 | Natural Language Processing | `NLP` | n-grammes, CRF, PCFG/CYK (`01`–`05`) | 5 |
| 24 | Deep Learning for NLP | `GenAI/Texte` · `GenAI/Integrations-DotNet` · `GenAI/RAG-et-Memoire-Semantique` | Semantic Kernel (`Microsoft.SemanticKernel`), vLLM/Qwen locaux, function calling, RAG | 41 |
| 25 | Computer Vision | `ML/DataScienceWithAgents/04-Vision` · `GenAI/Image` · `GenAI/Video` | classifieurs vision (04-Vision), génération ComfyUI/Qwen-VL | 101 (série) + 24 |
| 26 | Robotics | **aucun** | — | 0 |
| 27 | Philosophy, Ethics, and Safety of AI | `GenAI/Security` (`Control`, `Oversight`) + [singapore-consensus-self-audit.md](singapore-consensus-self-audit.md) | wargames d'oversight (`Oversight-Scaling-Laws-Wargames`), statistiques d'escalade — l'audit Singapore est un document, pas un exécutant | 6 |
| 28 | The Future of AI | **aucun** | — (chapitre prospectif, pas d'organe attendu) | 0 |
| App. A | Mathematical Background | `Complexity` | analyse de complexité mesurée (O(·) empirique) | 9 |

### Les chapitres sans organe — le livrable qui compte

Deux chapitres manquent d'organe sur 27 :

1. **Ch. 26 — Robotics** : aucun notebook du dépôt n'exécute de robotique (perception→action incarnée, SLAM, contrôle moteur). Les seules occurrences du mot « robot » dans les carnets sont des exemples de domaine (jeux coopératifs) et des noms de modèles TTS. C'est le front le plus net que l'enseignement AIMA suppose et que le dépôt ne sert pas — cohérent avec un dépôt sans matériel incarné, mais à écrire comme choix plutôt que comme trou muet.
2. **Ch. 28 — The Future of AI** : prospectif par nature ; le dépôt le traite indirectement via les documents de cadrage (`docs/cadrage/`) et l'observatoire (`Argument_Analysis`). Pas d'organe attendu.

Un cas intermédiaire : **Ch. 20 — Learning Probabilistic Models** (EM, apprentissage de modèles à variables cachées) n'a pas de sous-série dédiée — le thème vit en creux dans ML.NET (clustering) et Infer.NET (mélanges). Un chapitre « couvert par incidence » plutôt qu'exécuté de front : candidat à un carnet dédié si le front intéresse.

### Ce que le dépôt exécute au-delà de l'armature

La carte ne doit pas se lire comme un plafond. Le dépôt exécute des sujets **hors AIMA 4e** : information intégrée (`IIT`, PyPhi, 93 carnets — l'IIT n'est pas dans le livre), émergence causale (`IIT/ICT-Series`), contrats intelligents (`SymbolicAI/SmartContracts`, 31), géométrie symbolique (`SymbolicAI/Geometry`), apprentissage symbolique (`SymbolicAI/SymbolicLearning`), trading quantitatif (`QuantConnect`, 220 — le plus grand consommateur de RL du dépôt), argumentation datée (`Argument_Analysis`). L'armature est un socle de référence, pas le périmètre du dépôt.

## Ce que nos gates ne savent pas voir

*Position: There Are Futures That Benchmark-Driven AI Cannot See* (Lotfi, Russell et al., ICML 2026 — PDF du gisement, sha8 `01B15D8B`) soutient que lorsqu'une règle de sélection domine un environnement de recherche, **les idées qui ne s'y conforment pas n'ont nulle part où persister** — la thèse de l'exaptation. CoursIA est un tel environnement : gates, ratchets, verdicts, planchers. La question posée organe par organe : lequel **taxe** ce qui ne se mesure pas encore, que refuse-t-il **par construction**, et qu'avons-nous **prévu** pour ce qu'il ne sait pas voir.

| Organe | Ce qu'il taxe | Ce qu'il refuse par construction | Ce qui est prévu pour l'aveugle |
|---|---|---|---|
| **Plancher G-VAR-1** (≥1 DEEP de CONTENU par cycle) | le travail META (guard, tooling, docs) ne tient jamais le plancher, même excellent | le cycle « tout-META » comme cycle valable | le plancher est **par cycle**, pas par grain : le META est bienvenu au-delà |
| **G-VAR-2/3** (budget LIGHT, adjacence) | les séries de micro-corrections utiles (guards en chaîne) | deux LIGHT de même genre d'affilée | exception mécanique #14357 (second grain MED/DEEP, zéro fichier partagé) |
| **DWELL** (plancher 120 min avant merge) | l'urgence légitime (rouge sur `main`, correctif attendu) | rien — c'est un minuteur, pas un jugement | le balayage automatique lève seul ; la jambe se rejoue (`gh run rerun`) sans push |
| **B.0** (aucun nit non levé ne survit) | la réserve d'un bot dont l'émetteur ne re-review jamais | le merge avec réserve d'autrui non levée **par l'auteur** (mur `lift_author`, #13495) | `[OVERRIDE]` coordinateur + issue de suivi voie 3 — mais le mur lui-même est structurel |
| **Gate sorry** (`distinct_code_sorry`, axiomes forbidden) | la formalisation neuve difficile (un nouveau lake « doit » naître à sorry bas) | `native_decide`, `sorryAx`, `Classical.choice` non whitelisté | l'annotation INTRINSIC honnête dans le fichier (knot_lean) — le gate ne la lit pas, l'humain oui |
| **Critères BEATS** (multi-seed ≥4 + DM < 0.05) | l'exploration rapide (une après-midi ne produit jamais un verdict BEATS) | le claim d'amélioration single-seed | **le flag `[POC]` du §C** — l'échappatoire désignée qui rend l'exploration publiable sans la dégrader en claim |
| **Ratchets output/source-collapse** | le rétrécissement légitime (suppression d'une méthode remplacée) | la perte silencieuse de sortie ou de source | justification d'allègement dans le body — friction déclarée, pas interdit |
| **prose-counts bloquant** (README) | la prose qui compte (« N notebooks ») | le total mis à jour à la main | régénération catalogue = chemin désigné, toujours disponible |

### Lecture d'ensemble

Le motif commun : chaque gate rend **visible** une classe de dégradation (perte de sortie, preuve vide, claim non mesuré) et, ce faisant, rend **plus coûteux** le travail qui n'a pas encore la forme mesurable. C'est le prix de l'honnêteté des livrables, payé d'abord par le neuf mal différencié. Trois amortisseurs existent déjà et fonctionnent : `[POC]` (l'exploration déclarée), l'exception mécanique G-VAR-3 (les séries utiles), la levée DWELL automatique. Le mur B.0 auteur-vs-bot (#13495) est le seul organe du tableau dont l'aveugle est **structurel** — il ne se contourne que par la re-review de l'émetteur, et la file Hermes est la contrepartie connue de ce choix.

**Pratiques à changer : liste vide à ce stade.** Les amortisseurs désignés existent ; aucun organe du tableau ne supprime par construction une famille entière d'idées — ils contraignent la *forme de publication*, pas le *contenu*. Ce constat se re-testera à chaque fois qu'un gate nouveau naîtra : la question à inscrire dans sa PR est « quelle est la voie `[POC]` de ce gate ? ».

## Mesure reproductible

```bash
# Citations AIMA (mesuré : 56 au 2026-10-02)
grep -rlE "Modern Approach|Russell.{0,30}Norvig" MyIA.AI.Notebooks --include="*.ipynb" | wc -l

# Comptes par série (colonnes « Notebooks » de la carte, exclus _archive/ et .lake/)
for d in Search Sudoku SymbolicAI/Planners SymbolicAI/Lean SymbolicAI/Tweety \
         SymbolicAI/SemanticWeb SymbolicAI/SMT SymbolicAI/Argument_Analysis \
         Probas ML/ML.Net ML/DataScienceWithAgents NLP RL GameTheory IIT \
         GenAI/Texte GenAI/Image GenAI/Security QuantConnect Complexity; do
  printf '%4d  %s\n' $(find "MyIA.AI.Notebooks/$d" -name "*.ipynb" \
    -not -path "*_archive*" -not -path "*.lake*" | wc -l) "$d"
done
```

La carte se rafraîchit en rejouant ces commandes ; toute divergence de plus de cinq carnets signale une série à re-mapper.

## Sources (gisement `G:\Mon Drive\MyIA\IA\Bibliographie IA`)

| Source | Chemin | sha8 |
|---|---|---|
| Russell & Norvig, *Artificial Intelligence: A Modern Approach*, 4e éd. (2021) | racine du gisement | — |
| Lotfi et al., *Position: There Are Futures That Benchmark-Driven AI Cannot See* (ICML 2026) | `MachineLearning\2026 - Lotfi et al - Position - There Are Futures That Benchmark-Driven AI Cannot See (ICML 2026).pdf` | `01B15D8B` (vérifié) |

See #17528 · See #17525 · See #17541
