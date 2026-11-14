# RAG et Mémoire Sémantique — Infrastructure de Grounding (Qdrant)

[← GenAI](../README.md) | [Vibe-Coding — front-ends agents](../Vibe-Coding/README.md)

Cette section documente le **backend de mémoire sémantique** qui donne aux agents de codage une mémoire long-terme et les ancre dans des faits vérifiables plutôt que dans des suppositions : une base de données vectorielle [Qdrant](https://qdrant.tech/) qui indexe l'historique des conversations d'agents et le code des dépôts, interrogée à chaque tâche pour retrouver « ce qui a déjà été dit, écrit, décidé ». Le contenu est volontairement honnête sur les incidents traversés (pertes de données, dérives de montage disque, sauvegardes à moitié câblées) : ces pannes sont la matière pédagogique la plus utile.

> Avertissement de scope : ce répertoire documente le **backend mémoire/recherche** (Qdrant, embeddings, indexation, grounding). Les architectures d'agents autonomes sont couvertes par [Claw Systems](../Vibe-Coding/Claw-Systems/), et l'assurance qualité des notebooks par leurs sections respectives. Tous les exemples sont **anonymisés** : aucune clé d'API, aucun secret, aucune adresse interne réelle.

## Hook — pourquoi cette section

Les sections [Claude Code](../Vibe-Coding/Claude-Code/), [Roo Code](../Vibe-Coding/Roo-Code/) et [Claw Systems](../Vibe-Coding/Claw-Systems/) décrivent des **front-ends d'agents** : les interfaces par lesquelles un humain (ou un bot) pilote un assistant de codage. Cette section documente la couche d'en dessous.

Un assistant de codage sans mémoire externe ré-explore le même terrain à chaque session, re-pose des questions déjà tranchées, et finit par **halluciner** un état du projet qui n'existe plus. La mémoire sémantique répond à ce manque : elle transforme des milliers de conversations et de fichiers en un index interrogeable par le sens, pas seulement par les mots-clés.

| Aspect | Front-ends agents (Claude/Roo/Claw) | Mémoire sémantique (cette section) |
|--------|-------------------------------------|-------------------------------------|
| **Rôle** | Exécuter la tâche demandée | Fournir le contexte vérifié à l'agent |
| **Question posée** | « Comment fais-je X ? » | « Qu'a-t-on déjà fait autour de X ? » |
| **Objet** | LLM + outils | Base vectorielle + embeddings + indexation |
| **Horizon mémoire** | La session courante | L'historique complet du cluster |
| **Échec typique** | Mauvaise édition de code | Hallucination faute de contexte |
| **Persistance** | Éphémère (le contexte se résume) | Durable (sur disque, sauvegardée) |

## À qui s'adresse cette section

- **Opérateurs d'agents** qui veulent comprendre comment leurs outils sont *ancrés* dans un historique vérifié.
- **Curieux d'infrastructure ML / vectorielle** qui cherchent un récit honnête de mise en production (Docker, WSL2, quantization, anti-split-brain).
- **Lecteurs des notebooks pratiques** `01-Hands-On-Grounding.ipynb` (le contexte de l'infrastructure avant de manipuler Qdrant), `02-Retrieval-Avance.ipynb` (mesurer HyDE et le reranking sur un gold français), `03-Embeddings-From-Scratch.ipynb` (ce qu'un embedding *est*, avant de s'en servir), `03b-Espace-Embeddings-Visualisation.ipynb` (voir l'espace : PCA à la main et t-SNE pour projeter les embeddings en deux axes, et un banc de trois modèles mesuré sur le même corpus français), `04-Tokenisation-From-Scratch.ipynb` (ce qu'un token *est*, l'unité de compte que tout le dépôt consomme), `04b-Tokenisateurs-Compares.ipynb` (WordPiece et Unigram construits à la main et comparés au BPE, à budget de vocabulaire égal, avec l'effet multilingue), `05-Stockage-Vectoriel.ipynb` (la persistance sur disque et le compromis exact/ANN quand le corpus ne tient plus en RAM), `05b-Stockage-Vectoriel-Serveur.ipynb` (le même compromis sur un serveur Qdrant réel, puis FAISS, pgvector et le SDK Qdrant mesurés à côté de lui sur le même corpus — rappel, latence, mémoire, et où passe le filtre métadonnées) et `06-KernelMemory-InProcess.ipynb` (la couche d'abstraction Kernel Memory par-dessus l'infrastructure), `07-KernelMemory-Python-Quickstart.ipynb` (le jumeau Python en mode service : ingestion HTTP, citations, mesure), `08-KernelMemory-Hybrid-Search.ipynb` (la seconde jambe : BM25 + dense fusionnés en RRF sur l'index KM projeté, et la mesure honnête du gain sur petit corpus), `09-KernelMemory-Multimodal.ipynb` (le plafond multimodal du service OSS, constaté puis franchi par le pont vision, avec mesure avant/après), `10-RAG-Visuel-Embedding-Conjoint.ipynb` (le RAG visuel sans OCR : l'embedding joint SigLIP interroge les pages par leur apparence, l'écart mesuré par classe de requête) et `11-Alignement-Representationnel-Cross-Modal.ipynb` (comparer récupération et géométrie des représentations image-texte, sans supposer leur convergence).
- **Personnes ayant vécu un incident** (perte de données, dérive de montage disque, sauvegardes à moitié câblées) et cherchant des leçons partageables.

## Objectifs d'apprentissage

À l'issue de cette section, vous saurez :

1. **Pourquoi** une base vectorielle est nécessaire pour ancrer un agent dans des faits vérifiables (grounding, méthode SDDD).
2. **Comment** déployer Qdrant en Docker, sur WSL2, avec quantization (TurboQuant) et durcissement anti-split-brain.
3. **Comment** brancher un agent via MCP, indexer du code et des conversations, requêter par le sens (pas par mots-clés).
4. **Quelles pannes réelles** peuvent survenir en production (dérive de montage disque, perte de données, sauvegardes mal câblées) et comment durcir l'infrastructure.
5. **Comment mesurer** un alignement image-texte et distinguer la récupération de paires de la similarité géométrique des représentations.

## Notebooks et documents

Cette section regroupe les notebooks pratiques énumérés ci-dessous (Qdrant en mémoire, retrieval avancé mesuré, embeddings from scratch puis leur espace visualisé et mis en banc de modèles, tokenisation BPE à la main puis ses familles concurrentes, stockage vectoriel persistant puis son variant serveur, qui compare quatre moteurs côte à côte sur un seul corpus, la couche d'abstraction Kernel Memory en .NET in-process comme en service Python, la recherche hybride BM25+dense mesurée, le plafond multimodal du service OSS franchi par le pont vision, puis le RAG visuel et la mesure de l'alignement image-texte) et les documents de cadrage du dossier `docs/` :

| Support | Type | Vous y trouverez |
|---------|------|------------------|
| [`01-Hands-On-Grounding.ipynb`](01-Hands-On-Grounding.ipynb) | Notebook pratique | Manipuler Qdrant en mémoire : embeddings, upsert, recherche, index de payload — zéro dépendance externe |
| [`02-Retrieval-Avance.ipynb`](02-Retrieval-Avance.ipynb) | Notebook pratique | Comparer baseline bi-encoder, HyDE et reranking cross-encoder sur 24 questions françaises avec Recall@k et nDCG@k |
| [`03-Embeddings-From-Scratch.ipynb`](03-Embeddings-From-Scratch.ipynb) | Notebook pratique | Construire un word2vec (skip-gram NSG) en NumPy : co-occurrences + PMI, la géométrie qui émerge, et le pont vers un transformer contextuel |
| [`03b-Espace-Embeddings-Visualisation.ipynb`](03b-Espace-Embeddings-Visualisation.ipynb) | Notebook pratique | Voir l'espace des embeddings : PCA construite à la main (SVD, variance expliquée, validation contre sklearn) puis t-SNE via l'organ natif, sur un banc de trois modèles (MiniLM, DistilUSE, E5 et son préfixe `passage:`) encodant le même corpus français — silhouette, voisins croisés, contrôle négatif, et le coût mesuré de la réduction en deux axes |
| [`04-Tokenisation-From-Scratch.ipynb`](04-Tokenisation-From-Scratch.ipynb) | Notebook pratique | Construire une tokenisation BPE à la main, et mesurer le coût du choix de tokenizer sur le chunking et le budget de contexte |
| [`04-Tokenisation-From-Scratch-CSharp.ipynb`](04-Tokenisation-From-Scratch-CSharp.ipynb) | Notebook pratique C# | Construire BPE et comparer au tokenizer Qwen réel |
| [`04b-Tokenisateurs-Compares.ipynb`](04b-Tokenisateurs-Compares.ipynb) | Notebook pratique | WordPiece et Unigram construits à la main sur le corpus du 04, comparés à budget de vocabulaire égal, parité contre la bibliothèque `tokenizers`, et l'effet multilingue du choix de tokenizer sur le coût |
| [`05-Stockage-Vectoriel.ipynb`](05-Stockage-Vectoriel.ipynb) | Notebook pratique | Persistance sur disque (Qdrant), HNSW déplié à la main, et le compromis rappel-exact vs ANN mesuré — zéro conteneur |
| [`05b-Stockage-Vectoriel-Serveur.ipynb`](05b-Stockage-Vectoriel-Serveur.ipynb) | Notebook pratique (Python) | Le compromis ef exact/ANN sur un serveur Qdrant réel, 10k vecteurs, puis **quatre portes de mesure sur un seul corpus** — le serveur en HTTP, FAISS (bibliothèque C), pgvector (base SQL conteneurisée) et le SDK Qdrant (même serveur, autre porte) : rappel, latence médiane, empreinte mémoire mesurée, et la vraie divergence, où passe le filtre métadonnées (intégré au graphe, plan SQL strict ou itératif, post-filtre manuel et ses requêtes incomplètes) |
| [`06-KernelMemory-InProcess.ipynb`](06-KernelMemory-InProcess.ipynb) | Notebook pratique (.NET 10) | La couche d'abstraction Kernel Memory in-process : ETL documentaire, partitionnement en paragraphes, recherche avec citations, et le compromis granularité/rappel mesuré — embeddings locaux via LLamaSharp (GGUF `granite-embedding` CPU), zéro service. **Prérequis runtime : noyau .NET Interactive en .NET 10** (parité `Microsoft.Extensions.Logging.Abstractions 10.x` ↔ `Microsoft.KernelMemory.Core 0.98` compilé en 9.x) ; sur un hôte .NET 9 uniquement, ajouter `DOTNET_ROLL_FORWARD=LatestMajor` au lancement de la cellule 2 |
| [`07-KernelMemory-Python-Quickstart.ipynb`](07-KernelMemory-Python-Quickstart.ipynb) | Notebook pratique (Python) | Le jumeau Python du 06, en mode service : le service web Kernel Memory (Docker `kernelmemory/service`) piloté en HTTP depuis Python — ingestion d'un corpus hétérogène (22 textes français + PDF réel du dépôt + code source), recherche par similarité avec citations, inspection de ce que KM écrit dans Qdrant, `/ask` sourcé, gold-set français mesuré, épreuve de persistance par redémarrage |
| [`08-KernelMemory-Hybrid-Search.ipynb`](08-KernelMemory-Hybrid-Search.ipynb) | Notebook pratique (Python) | La recherche hybride par-dessus l'index KM : corpus français ingéré par le service Kernel Memory, constat des deux verrous (KM dense-only, Qdrant refuse d'étendre une collection existante), projection vers une collection hybride (dense + BM25 `Qdrant/bm25` via fastembed), puis mesure contrôlée dense vs BM25 vs fusion RRF — recall@3/@5 et MRR@10 sur un gold à deux classes (terme exact rare vs paraphrase sémantique) |
| [`09-KernelMemory-Multimodal.ipynb`](09-KernelMemory-Multimodal.ipynb) | Notebook pratique (Python) | La frontière modale du service KM OSS, mesurée : corpus polarisé par modalité (PDF réel, textes, schéma PNG) — le PNG est accepté (202) mais son pipeline **stand silencieusement** à l'extraction (zéro record), plafond documenté ; puis le pont vision : un modèle de vision décrit l'image, la description est ingérée, et la mesure avant/après montre les termes propres à l'image (`capteur impairfaux`) passant de miss à hit avec citations |
| [`10-RAG-Visuel-Embedding-Conjoint.ipynb`](10-RAG-Visuel-Embedding-Conjoint.ipynb) | Notebook pratique (Python) | Le RAG visuel **sans OCR ni description intermédiaire** : les 446 pages des decks de slides du dépôt embeddées par SigLIP multilingue dans un espace joint image-texte, interrogées en français, recall@k et MRR mesurés par classe de requête contre une baseline couche-texte — l'écart des requêtes visuelles rendu visible |
| [`11-Alignement-Representationnel-Cross-Modal.ipynb`](11-Alignement-Representationnel-Cross-Modal.ipynb) | Notebook pratique (Python) | Sur 72 paires synthétiques image-légende, comparer voisins mutuels de SigLIP et CKA entre encodeurs, avec contrôle brouillé et plafond lié au contenu des légendes ; la pente de convergence attendue ne se manifeste pas sur ce corpus hors distribution |
| [`01-Pourquoi-Memoire-Semantique.md`](docs/01-Pourquoi-Memoire-Semantique.md) | Document de cadrage | Le besoin : grounding, SDDD, RAG |
| [`02-Infrastructure-Qdrant.md`](docs/02-Infrastructure-Qdrant.md) | Document de déploiement | Docker, WSL2, quantization, anti-split-brain |
| [`03-Utilisation-MCP-Indexation.md`](docs/03-Utilisation-MCP-Indexation.md) | Document d'usage | Brancher un agent via MCP, indexer, rechercher |
| [`04-Incidents-et-Lecons.md`](docs/04-Incidents-et-Lecons.md) | Document de retours d'expérience | Diagnostiquer une dérive de montage, une perte de données, durcir les sauvegardes |

## Parcours recommandés

| Profil | Parcours suggéré |
|--------|------------------|
| **Vous découvrez la mémoire sémantique** | [01 - Pourquoi](docs/01-Pourquoi-Memoire-Semantique.md) → [Notebook Hands-On](01-Hands-On-Grounding.ipynb) → [03 - Utilisation](docs/03-Utilisation-MCP-Indexation.md) |
| **Vous voulez déployer Qdrant** | [02 - Infrastructure](docs/02-Infrastructure-Qdrant.md) → [04 - Incidents](docs/04-Incidents-et-Lecons.md) |
| **Vous voulez brancher un agent MCP** | [03 - Utilisation](docs/03-Utilisation-MCP-Indexation.md) → [Notebook Hands-On](01-Hands-On-Grounding.ipynb) |
| **Vous explorez les représentations multimodales** | [RAG visuel SigLIP](10-RAG-Visuel-Embedding-Conjoint.ipynb) → [Alignement cross-modal](11-Alignement-Representationnel-Cross-Modal.ipynb) : voisins mutuels, CKA et limites de transfert |
| **Vous avez vécu un incident** | [04 - Incidents](docs/04-Incidents-et-Lecons.md) en priorité, puis [02 - Infrastructure](docs/02-Infrastructure-Qdrant.md) |

## Prérequis

- **Docker** + Docker Compose.
- Notions de **base de données vectorielle** et de **plongements** (embeddings) — couvertes dans le [document 01](docs/01-Pourquoi-Memoire-Semantique.md).
- Pour reproduire l'usage avec un agent : une installation [Claude Code](../Vibe-Coding/Claude-Code/) ou [Roo Code](../Vibe-Coding/Roo-Code/) et le serveur MCP correspondant.
- Pour la partie infrastructure avancée (document 02/04) : familiarité avec WSL2 sous Windows, ou un hôte Linux équivalent.

## Limitations connues

- **Dépendance à un service externe pour la production.** Le notebook pratique fonctionne en mémoire sans dépendance, mais l'usage réel (indexation de conversations et de code) requiert Qdrant + service d'embeddings opérationnels.
- **Coût mémoire / disque.** Qdrant scale linéairement avec le corpus indexé ; un cluster de développement actif consomme rapidement plusieurs dizaines de Go. Prévoir un disque virtuel isolé (VHDX ou volume dédié) pour éviter les collisions de montage avec d'autres services GenAI.
- **Quantization = précision moindre.** Le service d'embeddings `qwen3-4b-awq` en 2560 dimensions remplace une API 1536 dimensions propriétaire : moins de dimensions, mais c'est *un modèle ouvert* et *auto-hébergé* — pas de dépendance à un fournisseur externe.
- **Honnêteté sur les incidents.** Le contenu documente des pertes de données et des dérives de montage disque traversées en production. Ces récits ne sont pas là pour décourager, mais pour armer le lecteur en cas de panne similaire.

## Concepts clés

- **Qdrant** — moteur de recherche vectorielle écrit en Rust. Il stocke des *points* (un vecteur + une charge utile JSON) regroupés en *collections*, et répond à des requêtes de plus proches voisins via un index HNSW.
- **Service d'embeddings** — modèle auto-hébergé (`qwen3-4b-awq`, 2560 dimensions) qui transforme un texte en vecteur. Il a remplacé une API commerciale propriétaire (1536 dimensions), coûteuse et fermée.
- **Serveur MCP `roo-state-manager`** — pont entre les agents et Qdrant. Il indexe les conversations et les dépôts, et expose des outils de recherche (`codebase_search`, `roosync_search`) directement dans l'agent.
- **Flotte d'agents** — Claude Code et Roo Code, sur plusieurs machines, qui produisent le contenu indexé *et* le consomment via les outils de recherche.
- **Grounding** — action d'ancrer une réponse d'agent dans des faits vérifiables, plutôt que dans une hallucination. La mémoire sémantique est l'infrastructure qui rend le grounding opérationnel.

## Contenu détaillé

### Écosystème

Quatre briques coopèrent pour former la chaîne de grounding :

1. **Qdrant** — le moteur de recherche vectorielle (Rust). *Points* (vecteur + payload JSON) regroupés en *collections*, recherche HNSW.
2. **Service d'embeddings** — modèle auto-hébergé (`qwen3-4b-awq`, 2560 dimensions). Remplace une API commerciale propriétaire (1536 dimensions) coûteuse et fermée.
3. **Serveur MCP `roo-state-manager`** — pont entre agents et Qdrant. Indexe conversations et dépôts, expose `codebase_search` et `roosync_search` directement dans l'agent.
4. **Flotte d'agents** — Claude Code et Roo Code, sur plusieurs machines, qui produisent le contenu indexé *et* le consomment via les outils de recherche.

### Schéma du pipeline

```text
   Conversations d'agents          Dépôts de code
   (Claude Code, Roo Code)         (fichiers source)
            │                             │
            └──────────────┬──────────────┘
                           ▼
              Découpage en fragments (chunking)
                           ▼
              Service d'embeddings (qwen3-4b-awq, 2560d)
                           ▼
              Qdrant — upsert dans une collection
              (vecteur + payload : source, date, type…)
                           ▼
   ┌───────────────────────────────────────────────┐
   │  Requête de l'agent : codebase_search(...)     │
   │   texte → embedding → recherche HNSW → top-k   │
   └───────────────────────────────────────────────┘
                           ▼
              Fragments pertinents réinjectés
              dans le contexte de l'agent (grounding)
```

### Structure du répertoire

```text
RAG-et-Memoire-Semantique/
├── README.md                              # Ce fichier — cadrage et vue d'ensemble
├── 01-Hands-On-Grounding.ipynb            # Notebook pratique — Qdrant en mémoire, zéro dépendance
├── 02-Retrieval-Avance.ipynb              # Notebook pratique — HyDE + reranking évalués sur gold français
├── 03-Embeddings-From-Scratch.ipynb       # Notebook pratique — word2vec from scratch + pont transformer
├── 04-Tokenisation-From-Scratch.ipynb     # Notebook pratique — BPE from scratch + coût du choix de tokenizer
├── 05-Stockage-Vectoriel.ipynb            # Notebook pratique — persistance + HNSW + compromis exact/ANN
├── 06-KernelMemory-InProcess.ipynb        # Notebook pratique (.NET 10) — Kernel Memory in-process, LLamaSharp CPU (DOTNET_ROLL_FORWARD=LatestMajor si hôte .NET 9)
├── 07-KernelMemory-Python-Quickstart.ipynb # Notebook pratique (Python) — service KM en HTTP, corpus hétérogène, citations
├── 08-KernelMemory-Hybrid-Search.ipynb    # Notebook pratique (Python) — hybride BM25+dense RRF sur index KM projeté, mesure
├── 09-KernelMemory-Multimodal.ipynb        # Notebook pratique (Python) — plafond multimodal OSS + pont vision, mesure avant/après
├── 10-RAG-Visuel-Embedding-Conjoint.ipynb  # Notebook pratique (Python) — embedding joint SigLIP sur pages de slides, requêtes FR, mesure par classe
├── 11-Alignement-Representationnel-Cross-Modal.ipynb  # Notebook pratique — voisins mutuels, CKA et limites cross-modales
├── docs/
│   ├── 01-Pourquoi-Memoire-Semantique.md  # Le besoin : grounding, SDDD, RAG
│   ├── 02-Infrastructure-Qdrant.md        # Le déploiement : Docker, WSL2, quantization
│   ├── 03-Utilisation-MCP-Indexation.md   # L'usage : MCP, indexation, recherche
│   └── 04-Incidents-et-Lecons.md          # Les pannes réelles et ce qu'elles enseignent
└── configs/
    ├── docker-compose.qdrant.example.yml  # Template Docker Compose (anonymisé)
    ├── qdrant.production.example.yaml      # Config moteur (HNSW, quantization, limites)
    └── qdrant.env.example                  # Variables d'environnement (placeholders)
```

### Infrastructure requise

| Composant | Rôle | Empreinte indicative |
|-----------|------|----------------------|
| Qdrant (Docker) | Base vectorielle | 1 conteneur, RAM selon volume (dizaines de Go) |
| Service d'embeddings | Texte → vecteur | 1 modèle ~4B en VRAM, ou API |
| Serveur MCP | Pont agent ↔ Qdrant | Process Node, léger |
| Stockage dédié | Données Qdrant | Disque virtuel isolé (VHDX/volume), proportionnel au corpus |

## Théorie — grounding, RAG, et la différence backend / application

Cette section documente l'**infrastructure** de mémoire sémantique : le backend Qdrant qui ancre des agents. Pour le versant **applicatif** du RAG (*Retrieval-Augmented Generation*) sur des documents texte, deux notebooks de la section [Texte](../Texte/) sont complémentaires :

- [`5_RAG_Modern.ipynb`](../Texte/05_RAG_Modern.ipynb) — construire un pipeline RAG moderne (découpage, embeddings, recherche, génération augmentée) : le pendant « application » de l'infrastructure décrite ici.
- [`14_Persistent_Memory.ipynb`](../Texte/14_Persistent_Memory.ipynb) — donner une mémoire persistante à un agent conversationnel : le même besoin de mémoire long-terme, vu côté application plutôt que côté infrastructure.

Le notebook pratique de cette section, [`01-Hands-On-Grounding.ipynb`](01-Hands-On-Grounding.ipynb), fait le pont : il manipule Qdrant directement (embeddings → upsert → recherche → index de payload) sur une base **en mémoire**, sans aucune dépendance externe.

## Portée scientifique

- Les documents relatent l'**infrastructure opérationnelle** ; les notebooks explorent aussi les embeddings, la recherche et l'alignement multimodal par des mesures contrôlées.
- Les passages « théorie » (méthode SDDD, RAG, grounding) renvoient à des sources externes (Qdrant docs, articles RAG, méthode SDDD) plutôt que de ré-exposer des mathématiques ou algorithmes.
- Cette section complète la littérature RAG classique par le retour de production et des expériences sur la représentation et la recherche ; elle ne prétend pas démontrer une convergence générale des modèles.

## FAQ

**Q : Cette section parle-t-elle de RAG ?**
R : Oui, mais du **côté backend** (base vectorielle, embeddings, indexation). Le côté *application* (pipeline RAG complet : découper, indexer, rechercher, générer) est traité dans la section [Texte](../Texte/) via [`5_RAG_Modern.ipynb`](../Texte/05_RAG_Modern.ipynb).

**Q : Faut-il Docker pour suivre le notebook ?**
R : Non. Le notebook `01-Hands-On-Grounding.ipynb` utilise Qdrant **en mémoire** (client Python Qdrant), zéro dépendance externe. Docker n'est requis que pour reproduire l'infrastructure de production décrite dans le document 02.

**Q : Pourquoi un disque virtuel isolé pour les données Qdrant ?**
R : Pour éviter les collisions de montage avec d'autres services GenAI qui partagent parfois le même répertoire hôte. C'est aussi un garde-fou anti-split-brain : Qdrant voit un seul volume dédié, pas une agrégation de montages hétérogènes.

**Q : Puis-je utiliser une autre base vectorielle (Chroma, Weaviate, Milvus) ?**
R : Le notebook pratique est spécifique à Qdrant (client Python Qdrant). Les concepts (HNSW, payload, upsert) se transfèrent, mais les API diffèrent. Le document 03 se concentre sur Qdrant pour cette raison.

**Q : Quelle est la différence entre « mémoire sémantique » et « mémoire long-terme » ?**
R : La mémoire sémantique est *indexée par le sens* (embeddings + recherche vectorielle). La mémoire long-terme est une notion plus large qui inclut aussi les fichiers, les bases SQL, les caches. Cette section documente spécifiquement la **mémoire sémantique vectorielle** comme backend de grounding.

## Conclusion / Prochaines étapes

`RAG-et-Memoire-Semantique` est une section modeste en volume mais dense en leçons opérationnelles : chaque incident documenté a renforcé une règle de durcissement (disque dédié, sauvegardes testées, anti-split-brain). Pour aller plus loin :

- **Lire les incidents.** Le document [04 - Incidents et leçons](docs/04-Incidents-et-Lecons.md) est la matière pédagogique la plus utile de cette section — il documente des pannes *réelles* et leurs *solutions*.
- **Faire tourner les notebooks.** [`01-Hands-On-Grounding.ipynb`](01-Hands-On-Grounding.ipynb) fonctionne en mémoire, sans Docker, en quelques minutes ; [`02-Retrieval-Avance.ipynb`](02-Retrieval-Avance.ipynb) mesure réellement HyDE et un cross-encoder multilingue sur CPU ; [`03-Embeddings-From-Scratch.ipynb`](03-Embeddings-From-Scratch.ipynb) construit un word2vec en NumPy, puis le compare à un transformer contextuel ; [`04-Tokenisation-From-Scratch.ipynb`](04-Tokenisation-From-Scratch.ipynb) construit un BPE à la main et mesure le coût du choix de tokenizer ; [`04b-Tokenisateurs-Compares.ipynb`](04b-Tokenisateurs-Compares.ipynb) construit WordPiece et Unigram sur le même corpus et mesure l'effet multilingue du choix de tokenizer ; [`05-Stockage-Vectoriel.ipynb`](05-Stockage-Vectoriel.ipynb) déplie un HNSW à la main et mesure le compromis rappel-exact vs ANN ; [`05b-Stockage-Vectoriel-Serveur.ipynb`](05b-Stockage-Vectoriel-Serveur.ipynb) rejoue le compromis sur un serveur Qdrant réel ; [`06-KernelMemory-InProcess.ipynb`](06-KernelMemory-InProcess.ipynb) (.NET 10 ou .NET 9 + `DOTNET_ROLL_FORWARD=LatestMajor`, modèle GGUF d'embeddings mis en cache, inférence llama.cpp CPU) délègue le pipeline à Kernel Memory et mesure le compromis granularité/rappel — sans service ni conteneur ; [`07-KernelMemory-Python-Quickstart.ipynb`](07-KernelMemory-Python-Quickstart.ipynb) en est le jumeau Python en mode service : le conteneur `kernelmemory/service` piloté en HTTP, ingestion d'un corpus hétérogène (textes français, PDF réel, code source), citations, réponse sourcée et épreuve de persistance ; [`08-KernelMemory-Hybrid-Search.ipynb`](08-KernelMemory-Hybrid-Search.ipynb) projette l'index vers une collection hybride dense + BM25 et mesure honnêtement ce que la fusion RRF ajoute ; [`09-KernelMemory-Multimodal.ipynb`](09-KernelMemory-Multimodal.ipynb) pousse jusqu'à la frontière modale : le schéma PNG accepté mais jamais indexé (plafond OCR du service OSS), puis rendu cherchable par le pont vision, mesure avant/après à l'appui ; [`10-RAG-Visuel-Embedding-Conjoint.ipynb`](10-RAG-Visuel-Embedding-Conjoint.ipynb) referme la boucle sans OCR : l'embedding joint SigLIP interroge les pages par leur apparence, l'écart rendu visible par classe de requête.
- **Comparer les représentations.** Après le RAG visuel du 10, le [carnet 11](11-Alignement-Representationnel-Cross-Modal.ipynb) met à l’épreuve l’[hypothèse platonicienne des représentations](https://arxiv.org/abs/2405.07987) sur 72 paires de formes et légendes synthétiques. Il emploie un voisin mutuel strict en top-1, distinct du recouvrement à k = 10 du papier, et une CKA linéaire pour comparer les géométries. SigLIP retrouve les paires au niveau du hasard ; la pente attendue entre `e5-small` et `e5-base` ne se lit pas ici. La CKA de DINOv2 et e5 compare leurs géométries, sans mesurer leur récupération mutuelle. Ces résultats sur un petit corpus hors distribution ne tranchent pas la convergence générale. Les modèles publics sont téléchargés au premier usage.
- **Brancher un agent.** Le document [03 - Utilisation et indexation](docs/03-Utilisation-MCP-Indexation.md) montre comment relier Claude Code ou Roo Code à Qdrant via MCP.

Pour le versant *application* du RAG (pas infrastructure), voir les notebooks [`5_RAG_Modern.ipynb`](../Texte/05_RAG_Modern.ipynb) et [`14_Persistent_Memory.ipynb`](../Texte/14_Persistent_Memory.ipynb) de la section Texte.

## Annexes

### Liens transverses

- [Notebook pratique — Hands-On Grounding](01-Hands-On-Grounding.ipynb)
- [Notebook pratique — Retrieval avancé](02-Retrieval-Avance.ipynb)
- [Notebook pratique — Embeddings from scratch](03-Embeddings-From-Scratch.ipynb)
- [Notebook pratique — Tokenisation from scratch](04-Tokenisation-From-Scratch.ipynb)
- [Notebook pratique — Tokenisateurs comparés](04b-Tokenisateurs-Compares.ipynb)
- [Notebook pratique — Stockage vectoriel](05-Stockage-Vectoriel.ipynb)
- [Notebook pratique — Stockage vectoriel, serveur](05b-Stockage-Vectoriel-Serveur.ipynb)
- [Notebook pratique — Kernel Memory in-process (.NET 10)](06-KernelMemory-InProcess.ipynb)
- [Notebook pratique — Kernel Memory Python, mode service](07-KernelMemory-Python-Quickstart.ipynb)
- [Notebook pratique — Kernel Memory hybride BM25+dense](08-KernelMemory-Hybrid-Search.ipynb)
- [Notebook pratique — Kernel Memory multimodal, pont vision](09-KernelMemory-Multimodal.ipynb)
- [Notebook pratique — RAG visuel par embedding joint](10-RAG-Visuel-Embedding-Conjoint.ipynb)
- [Notebook pratique — Alignement représentationnel cross-modal](11-Alignement-Representationnel-Cross-Modal.ipynb)
- [Pourquoi la mémoire sémantique](docs/01-Pourquoi-Memoire-Semantique.md)
- [Infrastructure Qdrant](docs/02-Infrastructure-Qdrant.md)
- [Utilisation et indexation](docs/03-Utilisation-MCP-Indexation.md)
- [Incidents et leçons](docs/04-Incidents-et-Lecons.md)
- [Documentation Qdrant officielle](https://qdrant.tech/documentation/)
- RAG appliqué au texte : [5_RAG_Modern](../Texte/05_RAG_Modern.ipynb) · [14_Persistent_Memory](../Texte/14_Persistent_Memory.ipynb)
- [GenAI (parent)](../README.md)
- [Vibe-Coding — front-ends agents (Claude Code, Roo Code, Claw Systems)](../Vibe-Coding/README.md)

### Parcours de lecture par niveau

| Document | Vous y apprendrez | Niveau |
|----------|-------------------|--------|
| [01 - Pourquoi la mémoire sémantique](docs/01-Pourquoi-Memoire-Semantique.md) | Pourquoi une base vectorielle, ce qu'est le grounding, la méthode SDDD | Débutant+ |
| [02 - Infrastructure Qdrant](docs/02-Infrastructure-Qdrant.md) | Déployer Qdrant en Docker, le stockage WSL2, la quantization TurboQuant, l'anti-split-brain | Intermédiaire |
| [03 - Utilisation et indexation](docs/03-Utilisation-MCP-Indexation.md) | Brancher un agent via MCP, indexer code et conversations, requêter par le sens | Intermédiaire |
| [04 - Incidents et leçons](docs/04-Incidents-et-Lecons.md) | Diagnostiquer une dérive de montage, une perte de données, durcir les sauvegardes | Avancé |
| [Notebook — Hands-On Grounding](01-Hands-On-Grounding.ipynb) | Manipuler Qdrant en mémoire : embeddings, upsert, recherche, index de payload | Pratique |
| [Notebook — Retrieval avancé](02-Retrieval-Avance.ipynb) | Évaluer bi-encoder, HyDE et cross-encoder avec Recall@k, nDCG@k et cas hors corpus | Avancé |
| [Notebook — Embeddings from scratch](03-Embeddings-From-Scratch.ipynb) | Construire un word2vec (skip-gram NSG) en NumPy, lire la géométrie, comparer à un transformer | Pratique |
| [Notebook — Tokenisation from scratch](04-Tokenisation-From-Scratch.ipynb) | Construire une tokenisation BPE à la main, mesurer le coût du choix de tokenizer sur le chunking et le budget | Pratique |
| [Notebook — Tokenisateurs comparés](04b-Tokenisateurs-Compares.ipynb) | WordPiece et Unigram from scratch sur le même corpus, parité contre la bibliothèque `tokenizers`, effet multilingue sur le coût | Pratique |
| [Notebook — Stockage vectoriel](05-Stockage-Vectoriel.ipynb) | Persister sur disque, déplier un HNSW à la main, mesurer le compromis rappel-exact vs ANN | Pratique |
| [Notebook — Stockage vectoriel, serveur](05b-Stockage-Vectoriel-Serveur.ipynb) | Rejouer le compromis ef exact/ANN sur un serveur Qdrant réel, 10k vecteurs | Pratique |
| [Notebook — Kernel Memory in-process](06-KernelMemory-InProcess.ipynb) | Déléguer ETL, partitionnement et citations à Kernel Memory (.NET 10 — ou .NET 9 avec `DOTNET_ROLL_FORWARD=LatestMajor`), mesurer la granularité contre le rappel | Pratique |
| [Notebook — Kernel Memory Python, mode service](07-KernelMemory-Python-Quickstart.ipynb) | Piloter le service web Kernel Memory en HTTP depuis Python : corpus hétérogène, citations, pont Qdrant, réponse sourcée, gold-set mesuré | Pratique |
| [Notebook — Kernel Memory hybride BM25+dense](08-KernelMemory-Hybrid-Search.ipynb) | Projeter l'index KM vers une collection hybride (dense + BM25 fastembed) et mesurer honnêtement ce que la fusion RRF ajoute — y compris quand elle n'ajoute rien — gold à deux classes, recall@k et MRR | Pratique |
| [Notebook — Kernel Memory multimodal, pont vision](09-KernelMemory-Multimodal.ipynb) | Constater le plafond OCR du service OSS (PNG accepté, pipeline figé), le franchir par le pont vision, mesurer avant/après | Pratique |
| [Notebook — RAG visuel, embedding joint](10-RAG-Visuel-Embedding-Conjoint.ipynb) | Retrouver des pages par leur apparence sans OCR : SigLIP multilingue embedde requête et image dans un même espace, recall@k et MRR mesurés par classe contre une baseline couche-texte | Pratique |
| [Notebook — Alignement représentationnel cross-modal](11-Alignement-Representationnel-Cross-Modal.ipynb) | Distinguer récupération par voisins mutuels et géométrie CKA, examiner la pente et les limites sur 72 paires synthétiques | Avancé |


### Compagnon C# des tokenisateurs comparés

Le [carnet C# 04b](04b-Tokenisateurs-Compares-CSharp.ipynb) reprend les algorithmes pédagogiques, les exercices et les mesures du [carnet Python](04b-Tokenisateurs-Compares.ipynb). La BCL réalise les jouets ; `Microsoft.ML.Tokenizers` 3.0.0 calcule Qwen, tandis que Python.NET 3.0.5 appelle les vrais entraîneurs Rust et le pipeline DistilBERT. Le SDK BERT .NET et la référence diffèrent pour certains caractères (par exemple `🙂`).

Préparer sous Linux un Python partagé 3.13 et un environnement isolé, puis **lancer Jupyter depuis le même terminal** après avoir positionné les variables suivantes :

```bash
python3.13 -m venv .venv-tokenizers
.venv-tokenizers/bin/pip install tokenizers==0.23.3 huggingface-hub==2.4.0
TOKEN_VENV="$PWD/.venv-tokenizers"
TOKEN_BASE="$("$TOKEN_VENV/bin/python" -c 'import sys; print(sys.base_prefix)')"
TOKEN_PYDLL="$("$TOKEN_VENV/bin/python" - <<'PYLIB'
import sys
import sysconfig
from pathlib import Path

library = sysconfig.get_config_var("LDLIBRARY")
if not library or not sysconfig.get_config_var("Py_ENABLE_SHARED"):
    raise SystemExit("Une distribution CPython 3.13 partagée est requise.")
base_lib = Path(sys.base_prefix) / "lib"
folders = [base_lib, Path(sysconfig.get_config_var("LIBDIR") or base_lib)]
if sysconfig.get_config_var("MULTIARCH"):
    folders.append(base_lib / sysconfig.get_config_var("MULTIARCH"))
for folder in folders:
    candidate = folder / library
    if candidate.is_file():
        print(candidate.resolve())
        break
else:
    raise SystemExit("libpython introuvable dans les chemins de cette installation.")
PYLIB
)" || exit 1
TOKEN_SITE="$("$TOKEN_VENV/bin/python" -c 'import sysconfig; print(sysconfig.get_path("purelib"))')"
export PYTHONHOME="$TOKEN_BASE"
export PYTHONNET_PYDLL="$TOKEN_PYDLL"
export PYTHONPATH="$TOKEN_SITE"
# Lancer ici Jupyter avec le noyau .NET Interactive.
```

La bibliothèque `libpython` doit exister au chemin calculé ; installer une distribution Python partagée si nécessaire. Les paquets NuGet sont restaurés par le carnet. Au premier lancement, Hugging Face télécharge les petits fichiers de tokenisation publics (sans poids de modèle ni clé) ; les révisions sont épinglées et leurs empreintes vérifiées. Ensuite le cache peut être réutilisé. Aucun service GenAI ni GPU n'est requis.

---

*Section RAG et Mémoire Sémantique — Juin 2026*
