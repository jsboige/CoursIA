# Argument_Analysis - Analyse Argumentative avec Agents IA

Pipeline complet d'analyse argumentative combinant Semantic Kernel, TweetyProject et programmation logique pour l'identification et l'evaluation d'arguments dans des textes.

## Vue d'ensemble

| Statistique | Valeur |
|-------------|--------|
| Notebooks | 6 |
| Kernel | Python 3 |
| Duree estimee | ~4-5h |
| API requise | OpenAI |

## Notebooks

| # | Notebook | Contenu | Role |
|---|----------|---------|------|
| 0 | [Agentic-0-init](Argument_Analysis_Agentic-0-init.ipynb) | Configuration, chargement API | Setup |
| 1 | [Agentic-1-informal_agent](Argument_Analysis_Agentic-1-informal_agent.ipynb) | Agent analyse informelle | Detection d'arguments |
| 2 | [Agentic-2-pl_agent](Argument_Analysis_Agentic-2-pl_agent.ipynb) | Agent logique propositionnelle | Formalisation |
| 3 | [Agentic-3-orchestration](Argument_Analysis_Agentic-3-orchestration.ipynb) | Orchestration multi-agents | Coordination |
| UI | [UI_configuration](Argument_Analysis_UI_configuration.ipynb) | Interface utilisateur widgets | Interaction |
| Exec | [Executor](Argument_Analysis_Executor.ipynb) | Orchestrateur principal | Execution |

## Architecture

```
                    ┌─────────────┐
                    │  Executor   │
                    └──────┬──────┘
                           │
           ┌───────────────┼───────────────┐
           │               │               │
    ┌──────▼──────┐ ┌──────▼──────┐ ┌──────▼──────┐
    │  Informal   │ │     PL      │ │ Orchestration│
    │   Agent     │ │   Agent     │ │    Agent     │
    └─────────────┘ └─────────────┘ └──────────────┘
           │               │               │
           └───────────────┴───────────────┘
                           │
                    ┌──────▼──────┐
                    │   Tweety    │
                    │  (Java/JPype)│
                    └─────────────┘
```

## Pipeline d'analyse

1. **Extraction** - Identification des arguments dans le texte
2. **Formalisation** - Conversion en logique propositionnelle
3. **Validation** - Verification coherence via Tweety
4. **Evaluation** - Detection de sophismes et faiblesses
5. **Rapport** - Generation conclusion structuree

## Mode batch

Pour execution automatisee (Papermill/MCP) :

```bash
# Dans .env
BATCH_MODE="true"
# Optionnel : texte personnalise
# BATCH_TEXT="Votre texte a analyser..."
```

## Technologies

| Technologie | Usage |
|-------------|-------|
| **Semantic Kernel** | Orchestration agents |
| **OpenAI GPT** | Analyse textuelle |
| **TweetyProject** | Logique formelle (Java) |
| **JPype** | Pont Python-Java |

## Prerequisites

### Python

```bash
pip install semantic-kernel openai python-dotenv jpype1
```

### Java

JDK 17+ requis (auto-telecharge via `install_jdk_portable.py`).

### Configuration

```bash
# Dans .env
OPENAI_API_KEY=sk-...
GLOBAL_LLM_SERVICE=openai
BATCH_MODE=false
```

## Structure des fichiers

```
Argument_Analysis/
├── *.ipynb                    # 6 notebooks
├── .env / .env.example        # Configuration
├── install_jdk_portable.py    # Installation JDK
├── data/                      # Donnees (taxonomie sophismes)
├── ext_tools/                 # Outils externes
├── jdk-17-portable/           # JDK (ignore git)
├── libs/                      # JARs Tweety
├── ontologies/                # Ontologies OWL
├── output/                    # Resultats analyses
└── resources/                 # Ressources Tweety
```

## Sortie

Le pipeline genere un rapport JSON dans `output/analysis_report.json` :

```json
{
  "validation_status": "COMPLETE_VALIDATED",
  "confidence_score": 85,
  "checks": {
    "ARGUMENTS_IDENTIFIED": true,
    "FALLACIES_ANALYZED": true,
    "BELIEF_SET_CREATED": true,
    "QUERIES_EXECUTED": true,
    "CONCLUSION_GENERATED": true
  }
}
```

## Concepts cles

| Concept | Description |
|---------|-------------|
| **Argument** | Premisses + Conclusion |
| **Sophisme** | Raisonnement fallacieux |
| **Belief Set** | Ensemble de croyances formalisees |
| **SAT** | Satisfaisabilite logique |

## Ponts avec les autres series

| Serie | Connection | Details |
| ----- | ---------- | ------- |
| **[Tweety](../Tweety/)** | Backend argumentatif | Utilise directement TweetyProject (JPype) pour le raisonnement formel. Les semantiques de Dung (Tweety-5) et la revision de croyances (Tweety-4) sont au coeur du pipeline. |
| **[Lean](../Lean/)** | Preuves formelles | La formalisation logique des arguments (Agentic-2) suit le meme paradigme que les tactiques Lean. La verification de coherence via SAT est analogue aux proof checkers. |
| **[Tweety-9](../Tweety/Tweety-9-Preferences.ipynb)** | Preferences et vote | L'analyse d'arguments de valeur croise les modeles de preference et la theorie du choix social (GameTheory/social_choice_lean/). |

> **Note** : Cette serie est en statut DRAFT — les notebooks definissent l'architecture mais n'ont pas encore d'execution complete. Voir [RECONSTRUCTION_PLAN.md](RECONSTRUCTION_PLAN.md) pour le statut.

## Ressources

- [Semantic Kernel Docs](https://learn.microsoft.com/en-us/semantic-kernel/)
- [TweetyProject](https://tweetyproject.org/)

## Licence

Voir la licence du repository principal.
