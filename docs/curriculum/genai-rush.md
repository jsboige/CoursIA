<!--
  FICHIER MANUEL — parcours narratif écrit à la main, PAS un artefact du
  catalogue. scripts/notebook_tools/generate_parcours.py n'écrit que les
  5 pages catalogue (genai.md, ia-classique.md, ia-symbolique.md,
  trading.md, recherche.md) ; ce fichier suit la convention des pages
  manuelles (comme _inventory.md, hors de la liste du générateur et du cron
  catalog-cron.yml) et n'est jamais régénéré. Cf EPIC #13844 Phase 2
  (pilote 1) et #15805.
-->

# Accéléré vers GenAI (~8-10 h)

Premier des trois parcours narratifs pilotes de l'EPIC #13844 (Phase 2). Sa
matière première est l'inventaire des embryons de parcours livré en Phase 0
([_inventory.md](_inventory.md), entrées #19-27 et #36) ; sa forme généralise
les « Parcours alternatifs » de GameTheory ([README](../../MyIA.AI.Notebooks/GameTheory/README.md) :
durée annoncée, liste numérotée, clause de prérequis explicite). Les cinq
pages catalogue (`genai.md`, `ia-classique.md`, …) restent en place comme
filet alphabétique : elles disent *ce qui existe* ; ce parcours dit *dans
quel ordre le faire*.

**Public visé** — le développeur ou la développeuse qui pratique déjà un peu
de Python et veut être opérationnel sur les APIs d'IA générative — texte,
image, voix, agents — sans monter de stack GPU.

## Prérequis vérifiables (~10 minutes)

| À vérifier | Comment | Succès attendu |
|---|---|---|
| Python 3.10+ | `python --version` | `Python 3.1x` ou plus |
| Jupyter | `jupyter --version` (ou l'extension Jupyter de VS Code) | une version s'affiche, sans erreur |
| Clé OpenAI **directe** | un compte avec crédit sur platform.openai.com, la clé exportée dans l'environnement | le one-liner ci-dessous affiche `200` |
| Connexion + ~1 Go libre | — | l'étape 13 télécharge ~130 Mo de modèle d'embeddings au premier appel |

Test de la clé (stdlib uniquement, aucune installation) :

```bash
python -c "import os,urllib.request as u; r=u.Request('https://api.openai.com/v1/models', headers={'Authorization':'Bearer '+os.environ['OPENAI_API_KEY']}); print(u.urlopen(r).status)"
```

Clause de prérequis — ce qui est supposé, et ce qui ne l'est pas :

> Ce parcours suppose une pratique élémentaire de Python (boucles, fonctions,
> dictionnaires) et **rien d'autre** : ni GPU, ni Docker, ni ComfyUI, ni
> expérience préalable des API OpenAI — chaque brique s'installe en route, à
> commencer par l'étape 1. Une seule subtilité : deux étapes (6 — DALL-E 3 et
> 8 — TTS) exigent la clé OpenAI **directe** ; les relais tiers comme
> OpenRouter ne servent ni `/v1/images/generations` ni les endpoints audio
> (avertissement posé dans l'en-tête de ces deux notebooks).

## Durée estimée — et pourquoi elle est défendable

Chaque étape porte ci-dessous la `duree_estimee` du catalogue
(`COURSE_CATALOG.generated.json`). Somme sur les 13 étapes :

| Bloc | Étapes | Durée catalogue |
|---|---|---|
| Mise en place | 1 | 30 min |
| Le texte : du prompt à l'agent | 2-5 | 2 h 30 |
| L'image | 6-7 | 1 h 15 |
| La voix | 8-9 | 1 h 30 |
| Orchestration et grounding | 10-13 | 1 h 45 |
| **Total** | | **7 h 30** |

Deux comptes plutôt qu'un chiffre flottant : le catalogue totalise **7 h 30** ;
en substituant, pour les 8 notebooks sur 13 qui annoncent leur propre durée
en en-tête, la valeur annoncée à celle du catalogue (elles divergent dans les
deux sens — ex. SK-3 annonce 55 min contre 15 au catalogue, 00-1 annonce
15 min contre 30), on obtient **7 h 45**. La fenêtre **~8-10 h** du titre
couvre ces deux comptes plus les relectures et reprises d'appels API
inévitables sur un itinéraire qui enchaîne 13 notebooks.

## Sortie concrète

À la fin du parcours, vous avez **exécuté** :

- une boucle agentique texte : le modèle choisit d'appeler *vos* fonctions,
  les exécute, puis reformule la réponse (étape 5) ;
- une chaîne image : génération DALL-E 3 puis transformations PIL
  (chargement, recadrage, redimensionnement, encodage) sur le même fichier
  (étapes 6-7) ;
- la paire voix : synthèse (TTS) et transcription (Whisper STT)
  (étapes 8-9) ;
- un agent Semantic Kernel avec plugins et conversation multi-agents
  `AgentGroupChat` (étape 12) ;
- une recherche sémantique sur une base vectorielle Qdrant embarquée — la
  brique de grounding de tout RAG (étape 13).

Et vous pouvez les chaîner : une question posée à la voix, transcrite
(étape 9), traitée par un LLM outillé (étape 5), répondue en voix (étape 8).
C'est le socle d'un assistant vocal minimal, construit uniquement avec ce
que le parcours a installé.

## Le parcours (13 étapes, dans l'ordre)

Pour chaque étape : ce qu'elle **apporte**, ce qu'elle **suppose acquis** —
lu sur la section Prérequis réelle du notebook quand elle existe (marqué
« déclaré »), sinon déduit de son contenu — et sa durée catalogue.

### Mise en place

1. **[Environment Setup](../../MyIA.AI.Notebooks/GenAI/00-GenAI-Environment/00-1-Environment-Setup.ipynb)**
   (`00-GenAI-Environment/00-1`, 30 min)
   - **Apporte** : l'environnement complet de la série — Python, fichier
     `.env`, clés, dépendances — installé et vérifié une fois pour toutes
     les étapes suivantes.
   - **Suppose** : rien. C'est le point d'entrée.

### Le texte : du prompt à l'agent

2. **[Texte 1 — Introduction à l'IA générative (API OpenAI)](../../MyIA.AI.Notebooks/GenAI/Texte/01_OpenAI_Intro.ipynb)**
   (30 min)
   - **Apporte** : le premier appel chat completions, la structure
     messages/rôles, le `.env` en pratique.
   - **Suppose** : l'étape 1 ; des bases de Python (déclaré).

3. **[Texte 2 — Prompt Engineering](../../MyIA.AI.Notebooks/GenAI/Texte/02_PromptEngineering.ipynb)**
   (45 min)
   - **Apporte** : les techniques de prompting (few-shot, décomposition…)
     qui rendent les étapes suivantes économes.
   - **Suppose** : le notebook 1 de la série (déclaré) ; la clé API.

4. **[Texte 3 — Structured Outputs : sorties JSON garanties](../../MyIA.AI.Notebooks/GenAI/Texte/03_Structured_Outputs.ipynb)**
   (30 min)
   - **Apporte** : des sorties JSON contraintes par schéma — la fondation
     pour brancher un LLM sur du code.
   - **Suppose** : le notebook 1 de la série (déclaré).

5. **[Texte 4 — Function Calling : connecter les LLM au monde réel](../../MyIA.AI.Notebooks/GenAI/Texte/04_Function_Calling.ipynb)**
   (45 min)
   - **Apporte** : les tools et la boucle agentique complète
     (`tool_calls` → exécution → ré-injection → réponse finale).
   - **Suppose** : le vocabulaire de schéma JSON installé par l'étape 4
     (DAG de la série : 3 → 4, cf [README Texte](../../MyIA.AI.Notebooks/GenAI/Texte/README.md)) ;
     la clé API.

### L'image

6. **[Image 01-1 — DALL-E 3](../../MyIA.AI.Notebooks/GenAI/Image/01-Foundation/01-1-OpenAI-DALL-E-3.ipynb)**
   (30 min)
   - **Apporte** : la génération d'images par API et ses premiers réglages
     (taille, qualité, style).
   - **Suppose** : l'Environment Setup (déclaré) ; la clé OpenAI
     **directe** — OpenRouter ne sert pas `/v1/images/generations`
     (déclaré) ; des bases de prompting (étape 3).

7. **[Image 01-3 — Opérations de base (PIL)](../../MyIA.AI.Notebooks/GenAI/Image/01-Foundation/01-3-Basic-Image-Operations.ipynb)**
   (45 min)
   - **Apporte** : la boîte à outils déterministe PIL qui entoure tout
     pipeline d'images — charger, recadrer, redimensionner, encoder.
   - **Suppose** : la lecture de 01-1 pour le contexte génératif ; aucune
     sortie d'un autre notebook n'est réutilisée (le notebook fabrique sa
     propre image de test).

### La voix

8. **[Audio 01-1 — TTS : synthèse vocale par API](../../MyIA.AI.Notebooks/GenAI/Audio/01-Foundation/01-1-OpenAI-TTS-Intro.ipynb)**
   (45 min)
   - **Apporte** : la synthèse vocale par API — voix, formats, réglages.
   - **Suppose** : l'Environment Setup (déclaré) ; la clé OpenAI
     **directe** pour les endpoints audio (déclaré) ; des bases Python.

9. **[Audio 01-2 — Whisper STT : reconnaissance vocale](../../MyIA.AI.Notebooks/GenAI/Audio/01-Foundation/01-2-OpenAI-Whisper-STT.ipynb)**
   (45 min)
   - **Apporte** : la transcription Whisper — l'autre moitié de la boucle
     voix.
   - **Suppose** : l'Environment Setup et la clé API (déclarés) ; le
     notebook 01-1, recommandé (déclaré).

### Orchestration et grounding

10. **[SK-1 — Fundamentals : introduction à Semantic Kernel](../../MyIA.AI.Notebooks/GenAI/SemanticKernel/01-SemanticKernel-Intro.ipynb)**
    (30 min)
    - **Apporte** : le Kernel comme orchestrateur — services LLM, plugins,
      fonctions sémantiques, chat avec historique.
    - **Suppose** : Python 3.10+, la clé, le `.env` (déclarés) ; le
      vocabulaire LLM des étapes 2-5.

11. **[SK-2 — Functions : function calling, mémoire, avancé](../../MyIA.AI.Notebooks/GenAI/SemanticKernel/02-SemanticKernel-Advanced.ipynb)**
    (30 min)
    - **Apporte** : le function calling automatique
      (`FunctionChoiceBehavior`), la mémoire vectorielle (API moderne), le
      contrôle de groundedness.
    - **Suppose** : le notebook SK-1 complet (déclaré).

12. **[SK-3 — Agents : Agent Framework](../../MyIA.AI.Notebooks/GenAI/SemanticKernel/03-SemanticKernel-Agents.ipynb)**
    (15 min)
    - **Apporte** : `ChatCompletionAgent`, l'orchestration multi-agents
      `AgentGroupChat`, les stratégies de terminaison.
    - **Suppose** : les notebooks SK-1 **et** SK-2 complets (déclaré) —
      d'où la présence de SK-2 dans cet itinéraire.

13. **[RAG 01 — Hands-On Grounding : Qdrant en mémoire](../../MyIA.AI.Notebooks/GenAI/RAG-et-Memoire-Semantique/01-Hands-On-Grounding.ipynb)**
    (30 min)
    - **Apporte** : une vraie base vectorielle Qdrant **embarquée**
      (`:memory:`), des embeddings multilingues locaux sur CPU, la recherche
      sémantique opposée au `grep` — la brique de grounding de tout RAG.
    - **Suppose** : rien de plus — « sans Docker, sans GPU, sans clé d'API »
      (déclaré en en-tête) ; le premier appel télécharge ~130 Mo de modèle
      d'embeddings.

## Pourquoi cet itinéraire, et pas un autre

- La série GenAI compte **215 notebooks au catalogue** : l'apprenant ne
  peut pas les trier seul (cf #15805). Celui-ci en traverse 13, choisis pour
  couvrir les quatre usages (texte outillé, image, voix, agents+grounding)
  en respectant les prérequis **déclarés** de chaque notebook. Le critère
  de succès de l'EPIC — « un apprenant qui suit le parcours dans l'ordre
  peut compléter chacun des notebooks référencés avec ses prérequis
  satisfaits » — a été vérifié étape par étape sur les sections Prérequis
  réelles, pas déduit des numérotations.
- Les niveaux avancés exigeant une stack locale sont volontairement hors
  itinéraire : p. ex. Audio 03-2 (pipeline STT→LLM→TTS avec faster-whisper
  et ~14 Go de VRAM) suppose un GPU local et des notebooks non inclus — il
  casserait la promesse « ni GPU ni Docker » et le critère de prérequis
  ci-dessus. Il reste la première marche des prolongements.

## Prolongements (ce que ce parcours débloque)

- **La recette podcast complète** (12 notebooks, cf [README Audio](../../MyIA.AI.Notebooks/GenAI/Audio/README.md) §
  recette) : le fil rouge narratif de la série audio ; ce parcours en pose
  les deux premières pierres (TTS, STT).
- **SemanticKernel 04-08** : Filters/Observabilité, VectorStores, Process
  Framework, MultiModal, MCP (cf [README SemanticKernel](../../MyIA.AI.Notebooks/GenAI/SemanticKernel/README.md)).
- **RAG-et-Memoire-Semantique 02+** : Qdrant en conteneur, retrieval
  avancé, Kernel Memory (cf [README RAG](../../MyIA.AI.Notebooks/GenAI/RAG-et-Memoire-Semantique/README.md) §
  parcours par niveau).
- **Texte 05_RAG_Modern et 09_Production** : le RAG moderne côté LLM, puis
  la mise en production (cf [README Texte](../../MyIA.AI.Notebooks/GenAI/Texte/README.md)).
- Selon l'objectif : [FineTuning](../../MyIA.AI.Notebooks/GenAI/FineTuning/README.md)
  (parcours Découverte ~1 h), Video, Vibe-Coding.

## Sources

- [_inventory.md](_inventory.md) — inventaire Phase 0 de l'EPIC #13844 :
  entrées #19 (modèle profil/durée), #20-27 (branches GenAI, statut
  INTEGRATE), #36 (DAG Texte) ; section « Modèles à exporter ».
- [README GameTheory](../../MyIA.AI.Notebooks/GameTheory/README.md) §
  « Parcours alternatifs » — la forme généralisée ici : durée annoncée,
  liste ordonnée, clause de prérequis qui dit ce qui est supposé **et ce
  qui ne l'est pas**.
- READMEs des séries traversées : [GenAI (racine, § Prérequis)](../../MyIA.AI.Notebooks/GenAI/README.md),
  [Texte (§ DAG)](../../MyIA.AI.Notebooks/GenAI/Texte/README.md),
  [Image (§ quick start)](../../MyIA.AI.Notebooks/GenAI/Image/README.md),
  [Audio (§ niveaux + recette)](../../MyIA.AI.Notebooks/GenAI/Audio/README.md),
  [SemanticKernel (§ DAG)](../../MyIA.AI.Notebooks/GenAI/SemanticKernel/README.md),
  [RAG (§ parcours par niveau)](../../MyIA.AI.Notebooks/GenAI/RAG-et-Memoire-Semantique/README.md).
- `COURSE_CATALOG.generated.json` — champ `duree_estimee` par notebook,
  sommé étape par étape ci-dessus.
