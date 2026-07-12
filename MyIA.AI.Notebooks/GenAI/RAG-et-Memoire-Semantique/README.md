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
- **Lecteurs du notebook pratique** `01-Hands-On-Grounding.ipynb` qui veulent le contexte de l'infrastructure avant de manipuler Qdrant en mémoire.
- **Personnes ayant vécu un incident** (perte de données, dérive de montage disque, sauvegardes à moitié câblées) et cherchant des leçons partageables.

## Objectifs d'apprentissage

À l'issue de cette section, vous saurez :

1. **Pourquoi** une base vectorielle est nécessaire pour ancrer un agent dans des faits vérifiables (grounding, méthode SDDD).
2. **Comment** déployer Qdrant en Docker, sur WSL2, avec quantization (TurboQuant) et durcissement anti-split-brain.
3. **Comment** brancher un agent via MCP, indexer du code et des conversations, requêter par le sens (pas par mots-clés).
4. **Quelles pannes réelles** peuvent survenir en production (dérive de montage disque, perte de données, sauvegardes mal câblées) et comment durcir l'infrastructure.

## Notebooks et documents

Cette section ne contient qu'**un seul notebook** (mise en pratique sur Qdrant en mémoire) et **quatre documents** de cadrage :

| Support | Type | Vous y trouverez |
|---------|------|------------------|
| [`01-Hands-On-Grounding.ipynb`](01-Hands-On-Grounding.ipynb) | Notebook pratique | Manipuler Qdrant en mémoire : embeddings, upsert, recherche, index de payload — zéro dépendance externe |
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

- [`5_RAG_Modern.ipynb`](../Texte/5_RAG_Modern.ipynb) — construire un pipeline RAG moderne (découpage, embeddings, recherche, génération augmentée) : le pendant « application » de l'infrastructure décrite ici.
- [`14_Persistent_Memory.ipynb`](../Texte/14_Persistent_Memory.ipynb) — donner une mémoire persistante à un agent conversationnel : le même besoin de mémoire long-terme, vu côté application plutôt que côté infrastructure.

Le notebook pratique de cette section, [`01-Hands-On-Grounding.ipynb`](01-Hands-On-Grounding.ipynb), fait le pont : il manipule Qdrant directement (embeddings → upsert → recherche → index de payload) sur une base **en mémoire**, sans aucune dépendance externe.

## Portée scientifique

- Le contenu est un récit d'**infrastructure opérationnelle** : ce qui a été déployé, ce qui a marché, ce qui a cassé.
- Les passages « théorie » (méthode SDDD, RAG, grounding) renvoient à des sources externes (Qdrant docs, articles RAG, méthode SDDD) plutôt que de ré-exposer des mathématiques ou algorithmes.
- Cette section complète — sans la dupliquer — la littérature RAG classique : on y lit *comment ça tourne en production*, pas *comment un transformer encode du texte*.

## FAQ

**Q : Cette section parle-t-elle de RAG ?**
R : Oui, mais du **côté backend** (base vectorielle, embeddings, indexation). Le côté *application* (pipeline RAG complet : découper, indexer, rechercher, générer) est traité dans la section [Texte](../Texte/) via [`5_RAG_Modern.ipynb`](../Texte/5_RAG_Modern.ipynb).

**Q : Faut-il Docker pour suivre le notebook ?**
R : Non. Le notebook `01-Hands-On-Grounding.ipynb` utilise Qdrant **en mémoire** (client Python Qdrant), zéro dépendance externe. Docker n'est requis que pour reproduire l'infrastructure de production décrite dans le document 02.

**Q : Pourquoi un disque virtuel isolé pour les données Qdrant ?**
R : Pour éviter les collisions de montage avec d'autres services GenAI qui partagent parfois le même répertoire hôte. C'est aussi un garde-fou anti-split-brain : Qdrant voit un seul volume dédié, pas une agrégation de montages hétérogènes.

**Q : Puis-je utiliser une autre base vectorielle (Chroma, Weaviate, Milvus) ?**
R : Le notebook pratique est spécifique à Qdrant (client Python Qdrant). Les concepts (HNSW, payload, upsert) se transfèrent, mais les API diffèrent. Le document 03 se concentre sur Qdrant pour cette raison.

**Q : Quelle est la différence entre « mémoire sémantique » et « mémoire long-terme » ?**
R : La mémoire sémantique est *indexée par le sens* (embeddings + recherche vectorielle). La mémoire long-terme est une notion plus large qui inclut aussi les fichiers, les bases SQL, les caches. Cette section documente spécifiquement la **mémoire sémantique vectorielle** comme backend de grounding.

## Conclusion / Prochaines étapes

`RAG-et-Memoire-Semantique` est une section modeste en volume (1 notebook + 4 documents) mais dense en leçons opérationnelles : chaque incident documenté a renforcé une règle de durcissement (disque dédié, sauvegardes testées, anti-split-brain). Pour aller plus loin :

- **Lire les incidents.** Le document [04 - Incidents et leçons](docs/04-Incidents-et-Lecons.md) est la matière pédagogique la plus utile de cette section — il documente des pannes *réelles* et leurs *solutions*.
- **Faire tourner le notebook.** [`01-Hands-On-Grounding.ipynb`](01-Hands-On-Grounding.ipynb) fonctionne en mémoire, sans Docker, en quelques minutes.
- **Brancher un agent.** Le document [03 - Utilisation et indexation](docs/03-Utilisation-MCP-Indexation.md) montre comment relier Claude Code ou Roo Code à Qdrant via MCP.

Pour le versant *application* du RAG (pas infrastructure), voir les notebooks [`5_RAG_Modern.ipynb`](../Texte/5_RAG_Modern.ipynb) et [`14_Persistent_Memory.ipynb`](../Texte/14_Persistent_Memory.ipynb) de la section Texte.

## Annexes

### Liens transverses

- [Notebook pratique — Hands-On Grounding](01-Hands-On-Grounding.ipynb)
- [Pourquoi la mémoire sémantique](docs/01-Pourquoi-Memoire-Semantique.md)
- [Infrastructure Qdrant](docs/02-Infrastructure-Qdrant.md)
- [Utilisation et indexation](docs/03-Utilisation-MCP-Indexation.md)
- [Incidents et leçons](docs/04-Incidents-et-Lecons.md)
- [Documentation Qdrant officielle](https://qdrant.tech/documentation/)
- RAG appliqué au texte : [5_RAG_Modern](../Texte/5_RAG_Modern.ipynb) · [14_Persistent_Memory](../Texte/14_Persistent_Memory.ipynb)
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

---

*Section RAG et Mémoire Sémantique — Juin 2026*