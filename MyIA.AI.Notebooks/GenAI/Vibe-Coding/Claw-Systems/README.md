# Claw Systems - Agents IA Autonomes en Conteneurs

[← Vibe-Coding](../README.md) | [↑ ..](../README.md)

Les **Claw systems** sont des plateformes d'agents IA autonomes, conteneurisées et self-hosted. Contrairement aux assistants de codage (Claude Code, Roo Code) qui assistent un développeur en temps réel, les Claw systems deployent des agents qui opèrent de manière autonome via des interfaces comme Telegram.

## Pourquoi une section Claw ?

| Aspect | Claude Code / Roo Code | Claw Systems |
|--------|------------------------|--------------|
| **Paradigme** | Assistance au développeur | Agent autonome |
| **Interface** | CLI / VS Code | Telegram, API, Web |
| **Execution** | Session interactive | Service persistant (Docker) |
| **Utilisateur** | Développeur | Utilisateur final |
| **Orchestration** | Agent unique | Multi-agents possible |

Les Claw systems représentent l'évolution naturelle : de l'assistant qui écrit du code a l'agent qui exécuté des tâches de manière autonome.

## Écosystème

### NanoClaw

Agent léger conteneurisé avec interface Telegram.

- **Architecture** : Conteneur Docker + API LLM (OpenRouter/local) + Telegram Bot API
- **Déploiement** : Docker Compose sur serveur (ai-01)
- **Fonctionnalités** : Chat, transcription vocale (ASR), skills personnalisables
- **Code source** : roo-extensions#1318

**Pipeline de production :**

```
Utilisateur Telegram
  → Message vocal/texte
  → NanoClaw (Docker)
    → ASR (whisper-api.myia.io) si vocal
    → LLM (OpenRouter / local)
    → Skills (outils configures)
  → Reponse Telegram
```

### OpenClaw

Plateforme multi-agents open source (en développement).

- Orchestration de plusieurs agents spécialisés
- Cluster management
- Workflows autonomes

## Parcours NanoClaw v2 (en modules)

> Cette série documente le **NanoClaw v2 réel**, tel qu'il tourne en production sur le cluster : un hôte Node unique orchestrant des conteneurs d'agents **par session**, où l'hôte et les agents ne communiquent **que** par des bases SQLite. Elle actualise progressivement les fiches `docs/NanoClaw-*.md`, qui décrivent un modèle conceptuel antérieur. Format **hybride** : une progression pédagogique en modules, chaque module ancré dans des décisions et des incidents de production réels.

| Module | Sujet | Statut |
|--------|-------|--------|
| [M1 · Le modèle « tout est message »](docs/M1-tout-est-message.md) | Principe fondateur (zéro IPC), modèle d'entités, deux bases par session | ✅ disponible |
| M2 · Architecture v2 | Hôte Node, conteneurs par session, détail des deux bases + base centrale | 🔜 à venir |
| M3 · Déploiement Windows réel | Service, build du conteneur, vault de secrets, montages | 🔜 à venir |
| M4 · Vivre en production | La chaîne de patches : incidents réels → correctifs | 🔜 à venir |
| M5 · Coordination multi-bots | Intercom, mentions, patterns et anti-patterns (co-écrit) | 🔜 à venir |

## Structure

```text
Claw-Systems/
├── README.md                    # Ce fichier
├── docs/
│   ├── M1-tout-est-message.md   # Parcours v2 — Module 1 : « tout est message »
│   ├── NanoClaw-Architecture.md # Architecture technique NanoClaw
│   ├── NanoClaw-Deploy.md       # Guide de deploiement
│   └── ASR-Integration.md       # Integration transcription vocale
└── configs/
    ├── docker-compose.nanoclaw.yml  # Template Docker Compose
    └── nanoclaw.env.example         # Variables d'environnement
```

## Infrastructure requise

| Service | Role | Host | URL |
|---------|------|------|-----|
| NanoClaw | Agent IA | ai-01 | Telegram Bot |
| ASR Whisper | Transcription vocale | po-2023 | `whisper-api.myia.io` |
| LLM | Raisonnement | OpenRouter / local | API |

## Prérequis

- **Docker** + Docker Compose
- **Telegram Bot Token** (via @BotFather)
- **OpenRouter API key** ou LLM local
- Acces au endpoint ASR (`whisper-api.myia.io`)

## Liens

- **[Parcours NanoClaw v2 — M1 : « tout est message »](docs/M1-tout-est-message.md)**
- [Architecture NanoClaw](docs/NanoClaw-Architecture.md)
- [Guide de déploiement](docs/NanoClaw-Deploy.md)
- [Intégration ASR](docs/ASR-Integration.md)
- [Vibe-Coding parent](../README.md)

---

*Section Claw Systems - Mai 2026*
