# Argument_Analysis - Analyse Argumentative avec Agents IA

<!-- CATALOG-STATUS
series: SymbolicAI-Argument_Analysis
pedagogical_count: 6
breakdown: Pipeline=5, UI=1
maturity: PRODUCTION=5, BETA=1
-->

Pipeline complet d'analyse argumentative combinant Semantic Kernel, TweetyProject et programmation logique pour l'identification et l'evaluation d'arguments dans des textes.

## Pourquoi cette serie

Distinguer un argument valide d'un sophisme est un acte essentiel dans une societe sature de discours generes a la chaine. Lorsque les LLMs produisent des textes plausibles a la demande, la frontiere entre persuasion legitime et manipulation rhetorique se brouille : raisonnements circulaires, faux dilemmes, appels a l'autorite mal calibres deviennent indetectables par simple lecture rapide. La verification formelle, autrefois reservee aux logiciens, devient un service de masse : moderation de plateformes, journalisme assiste, education critique, audit de contenus pedagogiques generes par IA.

Cette serie pose une question concrete : peut-on construire un pipeline qui prend un texte argumentatif en entree et qui en restitue une carte logique formelle, validee par un solveur SAT, avec detection systematique des sophismes connus ? La reponse passe par un assemblage soigne de trois competences distinctes : un LLM pour extraire le tissu argumentatif informel (premisses, conclusions, transitions), un solveur logique (TweetyProject, Java via JPype) pour verifier la coherence des formalisations propositionnelles obtenues, et une couche d'orchestration agentique (Semantic Kernel) qui transforme cette chaine en pipeline reproductible. Le travail pedagogique consiste a maitriser chacune de ces briques *et* leur composition : ou s'arrete le LLM, ou commence le verificateur formel, comment une boucle informel/formel converge vers un verdict.

Le contexte de recherche actuel rend cette competence particulierement pertinente. Les frameworks de raisonnement structure (ASPIC+, ABA, DeLP) sont implementes en JVM et accessibles via les memes ponts JPype que ceux utilises ici. Les LLMs de 2025-2026 sont assez fiables pour la phase d'extraction informelle mais restent faibles sur la verification formelle, ce qui motive precisement le pattern hybride documente dans la serie. Les ponts vers [Tweety](../Tweety/) (semantiques de Dung, revision de croyances AGM, preferences de Tweety-9) et [Lean](../Lean/) (preuves formelles, tactiques) permettent d'aller plus loin pour qui veut depasser la simple verification SAT.

**A qui s'adresse cette serie** : enseignants en pensee critique, equipes editoriales construisant des outils de fact-checking, etudiants en philosophie computationnelle ou en linguistique formelle, et ingenieurs explorant les architectures hybrides LLM + solveur. La maitrise prealable supposee est moderee : Python intermediate, intuition logique propositionnelle, familiarite minimale avec les LLMs et l'OpenAI API. Les notebooks (~4-5h total) s'enchainent dans l'ordre 0 → 1 → 2 → 3, avec l'`Executor` comme point d'entree pour une execution batch reproducible (Papermill / MCP).

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

## Objectifs d'apprentissage

A l'issue de cette serie, vous serez capable de :

1. **Extraire le tissu argumentatif** d'un texte en identifiant premisses, conclusions et transitions a l'aide d'un agent LLM (Semantic Kernel)
2. **Formaliser des arguments** en logique propositionnelle et verifier leur coherence avec un solveur SAT (TweetyProject)
3. **Detecter les sophismes** courants (homme de paille, faux dilemme, ad hominem, appel a l'autorite) de maniere systematique
4. **Orchestrer un pipeline multi-agents** combinant extraction informelle, formalisation logique et validation formelle
5. **Comparer les approches** LLM-only vs hybride (LLM + solveur formel) et comprendre les limites de chaque couche

## Ce que chaque notebook apporte

| Notebook | Competence clee | Temps |
|----------|----------------|-------|
| **0-init** | Configurer l'environnement Python + Java, charger les cles API, verifier la connexion Tweety/JVM | 30 min |
| **1-informal_agent** | Construire un agent LLM qui identifie et annote les arguments dans un texte naturel | 60 min |
| **2-pl_agent** | Convertir les arguments informels en formules propositionnelles et les verifier via SAT | 60 min |
| **3-orchestration** | Composer les agents precedents en pipeline coordonne avec rapport de sortie structure | 50 min |
| **UI_configuration** | Creer une interface interactive (ipywidgets) pour piloter le pipeline en mode exploratoire | 30 min |
| **Executor** | Executer le pipeline complet en mode batch (Papermill/MCP) avec configuration .env | 20 min |

## FAQ / Troubleshooting

| Probleme | Solution |
|----------|----------|
| **`ModuleNotFoundError: semantic_kernel`** | `pip install semantic-kernel`. Verifier le kernel Jupyter actif (`jupyter kernelspec list`). |
| **`OPENAI_API_KEY not set`** | Copier `.env.example` en `.env` et renseigner la cle. Verifier que le notebook 0 charge bien le `.env`. |
| **`JVM not found`** au demarrage | JDK 17+ requis. Executer `python install_jdk_portable.py` dans le repertoire. |
| **`FileNotFoundException` sur un JAR Tweety** | Les JARs doivent etre dans `libs/`. Re-executer le notebook 0 qui les telecharge. |
| **`BATCH_MODE` ignore** | Verifier que `.env` contient `BATCH_MODE="true"` (avec guillemets) et que le fichier est au meme niveau que les notebooks. |
| **Erreur `dotnet` ou `.NET`** | Cette serie est 100% Python. Seul Semantic Kernel (package Python) est utilise, pas le SDK .NET. |
| **Sortie `PARTIAL_VALIDATED`** | Le pipeline n'a pas convergé. Verifier les logs de l'agent PL (formalisation incomplete). Relancer avec un texte plus court. |
| **`OutOfMemoryError` JVM** | Augmenter le heap dans la cellule de demarrage : ajouter `-Xmx2g` aux arguments JPype. |

## Quel parcours choisir ?

| Profil | Parcours recommande | Notebooks |
|--------|-------------------|-----------|
| **Decouvreur de l'analyse argumentative** | Pipeline complet en ordre | 0 → 1 → 2 → 3 (~3h) |
| **Enseignant en pensee critique** | Extraction + detection sophismes | 0 → 1 → UI_configuration (~1h30) |
| **Ingenieur ML/LLM** | Architecture multi-agents | 0 → 3 → Executor (~1h30) |
| **Chercheur en logique formelle** | Formalisation + verification SAT | 0 → 2 (~1h) |

---

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

## Domaines d'application

L'analyse argumentative outillee s'inscrit dans plusieurs cas concrets ou la distinction "argument valide / sophisme" doit etre rendue automatique ou semi-automatique :

- **Moderation de discussions en ligne** : detection des sophismes recurrents (homme de paille, faux dilemmes, glissement, ad hominem) dans des fils de commentaires longs, avec un rapport agrege par utilisateur ou par fil. Le pattern LLM-extracteur + verificateur formel est calibre precisement pour cet usage.
- **Fact-checking et journalisme assiste** : decomposition d'un editorial ou d'un discours politique en chaine de premisses et conclusions, marquage des transitions logiquement faibles, identification des affirmations factuelles a verifier externement. La phase "formalisation" cree un livrable inspectable, contrairement aux jugements opaques d'un LLM seul.
- **Education a la pensee critique** : production d'exercices d'analyse a partir de textes reels (discours, essais, posts), avec correction automatisee partielle. L'enseignant valide la decomposition, l'eleve apprend a justifier chaque etape.
- **Audit de contenus IA** : verification de la coherence interne des reponses LLM longues sur sujets sensibles (medical, juridique, financier). Un LLM peut produire un raisonnement plausible mais incoherent ; le solveur formel detecte les contradictions internes.
- **Recherche en argumentation structuree** : terrain experimental pour les frameworks Dung, ASPIC+, ABA, accessibles via les ponts Tweety. La serie sert de support a des explorations academiques (memoires, theses) sur les semantiques d'acceptabilite, la revision de croyances AGM, ou les preferences entre arguments.

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

## Quick Start

```bash
# 1. Installer les dependances Python
pip install semantic-kernel openai python-dotenv jpype1

# 2. Configurer les API keys
cp .env.example .env
# Editer .env : OPENAI_API_KEY, BATCH_MODE=true

# 3. Lancer le premier notebook
jupyter notebook Argument_Analysis_Agentic-0-init.ipynb
```

> **Note** : JDK 17+ est requis mais auto-telecharge via `install_jdk_portable.py` (pas d'installation systeme).

---

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

### References academiques

| Reference | Couverture |
|-----------|------------|
| Dung, "On the Acceptability of Arguments and its Fundamental Role in Nonmonotonic Reasoning" (1995) | Argumentation abstraite, semantiques |
| Modgil & Prakken, "The ASPIC+ Framework for Structured Argumentation" (2014) | Argumentation structuree |
| Alchourron, Gardenfors & Makinson, "On the Logic of Theory Change" (1985) | Revision de croyances AGM |
| Besnard & Hunter, *Elements of Argumentation* (2008) | Cadre general argumentation |
| Walton, *Argumentation Schemes for Presumptive Reasoning* (1996) | Taxonomie des sophismes |

### Ressources en ligne

- [Semantic Kernel Docs](https://learn.microsoft.com/en-us/semantic-kernel/)
- [TweetyProject](https://tweetyproject.org/)

## Licence

Voir la licence du repository principal.
