# RAG et Mémoire Sémantique — Infrastructure de Grounding (Qdrant)

[← GenAI](../README.md) | [Vibe-Coding — front-ends agents](../Vibe-Coding/README.md)

Les sections [Claude Code](../Vibe-Coding/Claude-Code/), [Roo Code](../Vibe-Coding/Roo-Code/) et [Claw Systems](../Vibe-Coding/Claw-Systems/) décrivent des **front-ends d'agents** : les interfaces par lesquelles un humain (ou un bot) pilote un assistant de codage. Cette section documente la couche d'en dessous : le **backend de mémoire sémantique** qui donne à ces agents une mémoire long-terme et les ancre dans des faits vérifiables plutôt que dans des suppositions.

Concrètement, c'est le récit d'une infrastructure réelle, opérée en continu sur un cluster de machines de développement : une base de données vectorielle [Qdrant](https://qdrant.tech/) qui indexe l'historique des conversations d'agents et le code des dépôts, interrogée à chaque tâche pour retrouver « ce qui a déjà été dit, écrit, décidé ». Le contenu est volontairement honnête sur les incidents traversés (pertes de données, dérives de montage disque, sauvegardes à moitié câblées) : ces pannes sont la matière pédagogique la plus utile.

> Avertissement de scope : ce répertoire documente le **backend mémoire/recherche** (Qdrant, embeddings, indexation, grounding). Les architectures d'agents autonomes sont couvertes par [Claw Systems](../Vibe-Coding/Claw-Systems/), et l'assurance qualité des notebooks par leurs sections respectives. Tous les exemples sont **anonymisés** : aucune clé d'API, aucun secret, aucune adresse interne réelle.

## Pourquoi une section Mémoire Sémantique ?

| Aspect | Front-ends agents (Claude/Roo/Claw) | Mémoire sémantique (cette section) |
|--------|-------------------------------------|-------------------------------------|
| **Rôle** | Exécuter la tâche demandée | Fournir le contexte vérifié à l'agent |
| **Question posée** | « Comment fais-je X ? » | « Qu'a-t-on déjà fait autour de X ? » |
| **Objet** | LLM + outils | Base vectorielle + embeddings + indexation |
| **Horizon mémoire** | La session courante | L'historique complet du cluster |
| **Échec typique** | Mauvaise édition de code | Hallucination faute de contexte |
| **Persistance** | Éphémère (le contexte se résume) | Durable (sur disque, sauvegardée) |

Un assistant de codage sans mémoire externe ré-explore le même terrain à chaque session, re-pose des questions déjà tranchées, et finit par **halluciner** un état du projet qui n'existe plus. La mémoire sémantique répond à ce manque : elle transforme des milliers de conversations et de fichiers en un index interrogeable par le sens, pas seulement par les mots-clés.

## Écosystème

Quatre briques coopèrent pour former la chaîne de grounding :

1. **Qdrant** — le moteur de recherche vectorielle (écrit en Rust). Il stocke des *points* (un vecteur + une charge utile JSON) regroupés en *collections*, et répond à des requêtes de plus proches voisins via un index HNSW.
2. **Le service d'embeddings** — un modèle auto-hébergé (`qwen3-4b-awq`, 2560 dimensions) qui transforme un texte en vecteur. Il a remplacé une API commerciale propriétaire (1536 dimensions), coûteuse et fermée.
3. **Le serveur MCP `roo-state-manager`** — le pont entre les agents et Qdrant. Il indexe les conversations et les dépôts, et expose des outils de recherche (`codebase_search`, `roosync_search`) directement dans l'agent.
4. **La flotte d'agents** — Claude Code et Roo Code, sur plusieurs machines, qui produisent le contenu indexé *et* le consomment via les outils de recherche.

## Schéma du pipeline

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

## Structure

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

## Parcours de lecture

| Document | Vous y apprendrez | Niveau |
|----------|-------------------|--------|
| [01 - Pourquoi la mémoire sémantique](docs/01-Pourquoi-Memoire-Semantique.md) | Pourquoi une base vectorielle, ce qu'est le grounding, la méthode SDDD | Débutant+ |
| [02 - Infrastructure Qdrant](docs/02-Infrastructure-Qdrant.md) | Déployer Qdrant en Docker, le stockage WSL2, la quantization TurboQuant, l'anti-split-brain | Intermédiaire |
| [03 - Utilisation et indexation](docs/03-Utilisation-MCP-Indexation.md) | Brancher un agent via MCP, indexer code et conversations, requêter par le sens | Intermédiaire |
| [04 - Incidents et leçons](docs/04-Incidents-et-Lecons.md) | Diagnostiquer une dérive de montage, une perte de données, durcir les sauvegardes | Avancé |
| [Notebook — Hands-On Grounding](01-Hands-On-Grounding.ipynb) | Manipuler Qdrant en mémoire : embeddings, upsert, recherche, index de payload | Pratique |

## Pour aller plus loin — la série RAG sur texte

Cette section documente l'**infrastructure** de mémoire sémantique : le backend Qdrant qui ancre des agents. Pour le versant **applicatif** du RAG (*Retrieval-Augmented Generation*) sur des documents texte, deux notebooks de la section [Texte](../Texte/) sont complémentaires :

- [`5_RAG_Modern.ipynb`](../Texte/5_RAG_Modern.ipynb) — construire un pipeline RAG moderne (découpage, embeddings, recherche, génération augmentée) : le pendant « application » de l'infrastructure décrite ici.
- [`14_Persistent_Memory.ipynb`](../Texte/14_Persistent_Memory.ipynb) — donner une mémoire persistante à un agent conversationnel : le même besoin de mémoire long-terme, vu côté application plutôt que côté infrastructure.

Le notebook pratique de cette section, [`01-Hands-On-Grounding.ipynb`](01-Hands-On-Grounding.ipynb), fait le pont : il manipule Qdrant directement (embeddings → upsert → recherche → index de payload) sur une base **en mémoire**, sans aucune dépendance externe.

## Infrastructure requise

| Composant | Rôle | Empreinte indicative |
|-----------|------|----------------------|
| Qdrant (Docker) | Base vectorielle | 1 conteneur, RAM selon volume (dizaines de Go) |
| Service d'embeddings | Texte → vecteur | 1 modèle ~4B en VRAM, ou API |
| Serveur MCP | Pont agent ↔ Qdrant | Process Node, léger |
| Stockage dédié | Données Qdrant | Disque virtuel isolé (VHDX/volume), proportionnel au corpus |

## Prérequis

- **Docker** + Docker Compose.
- Notions de **base de données vectorielle** et de **plongements** (embeddings) — couvertes dans le [document 01](docs/01-Pourquoi-Memoire-Semantique.md).
- Pour reproduire l'usage avec un agent : une installation [Claude Code](../Vibe-Coding/Claude-Code/) ou [Roo Code](../Vibe-Coding/Roo-Code/) et le serveur MCP correspondant.
- Pour la partie infrastructure avancée (document 02/04) : familiarité avec WSL2 sous Windows, ou un hôte Linux équivalent.

## Liens

- [Notebook pratique — Hands-On Grounding](01-Hands-On-Grounding.ipynb)
- [Pourquoi la mémoire sémantique](docs/01-Pourquoi-Memoire-Semantique.md)
- [Infrastructure Qdrant](docs/02-Infrastructure-Qdrant.md)
- [Utilisation et indexation](docs/03-Utilisation-MCP-Indexation.md)
- [Incidents et leçons](docs/04-Incidents-et-Lecons.md)
- [Documentation Qdrant officielle](https://qdrant.tech/documentation/)
- RAG appliqué au texte : [5_RAG_Modern](../Texte/5_RAG_Modern.ipynb) · [14_Persistent_Memory](../Texte/14_Persistent_Memory.ipynb)
- [GenAI (parent)](../README.md)
- [Vibe-Coding — front-ends agents (Claude Code, Roo Code, Claw Systems)](../Vibe-Coding/README.md)

---

*Section RAG et Mémoire Sémantique — Juin 2026*
