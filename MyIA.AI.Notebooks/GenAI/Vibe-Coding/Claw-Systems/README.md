# Claw Systems - Agents IA Autonomes en Conteneurs

[← Vibe-Coding](../README.md) | [↑ ..](../README.md)

Les **Claw systems** sont des plateformes d'agents IA autonomes, conteneurisees et self-hosted. Contrairement aux assistants de codage (Claude Code, Roo Code) qui assistent un developpeur en temps reel, les Claw systems deployent des agents qui operent de maniere autonome via des interfaces comme Telegram.

## Pourquoi une section Claw ?

| Aspect | Claude Code / Roo Code | Claw Systems |
|--------|------------------------|--------------|
| **Paradigme** | Assistance au developpeur | Agent autonome |
| **Interface** | CLI / VS Code | Telegram, API, Web |
| **Execution** | Session interactive | Service persistant (Docker) |
| **Utilisateur** | Developpeur | Utilisateur final |
| **Orchestration** | Agent unique | Multi-agents possible |

Les Claw systems representent l'evolution naturelle : de l'assistant qui ecrit du code a l'agent qui execute des taches de maniere autonome.

## Ecosysteme

### NanoClaw

Agent leger conteneurise avec interface Telegram.

- **Architecture** : Conteneur Docker + API LLM (OpenRouter/local) + Telegram Bot API
- **Deploiement** : Docker Compose sur serveur (ai-01)
- **Fonctionnalites** : Chat, transcription vocale (ASR), skills personnalisables
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

Plateforme multi-agents open source (en developpement).

- Orchestration de plusieurs agents specialises
- Cluster management
- Workflows autonomes

## Structure

```text
Claw-Systems/
├── README.md                    # Ce fichier
├── docs/
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

## Prerequis

- **Docker** + Docker Compose
- **Telegram Bot Token** (via @BotFather)
- **OpenRouter API key** ou LLM local
- Acces au endpoint ASR (`whisper-api.myia.io`)

## Liens

- [Architecture NanoClaw](docs/NanoClaw-Architecture.md)
- [Guide de deploiement](docs/NanoClaw-Deploy.md)
- [Integration ASR](docs/ASR-Integration.md)
- [Vibe-Coding parent](../README.md)

---

*Section Claw Systems - Mai 2026*
