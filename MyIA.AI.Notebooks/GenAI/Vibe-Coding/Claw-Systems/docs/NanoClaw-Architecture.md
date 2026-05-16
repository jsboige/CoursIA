# NanoClaw - Architecture Technique

## Vue d'ensemble

NanoClaw est un agent IA autonome leger, conteneurise dans Docker, avec une interface Telegram. Il combine un LLM (via OpenRouter ou local) avec des tools/skills pour executer des taches sans supervision humaine continue.

## Composants

```
┌─────────────────────────────────────────────┐
│                 Docker Host                  │
│  ┌────────────────────────────────────────┐  │
│  │          NanoClaw Container            │  │
│  │                                        │  │
│  │  ┌──────────┐    ┌──────────────────┐  │  │
│  │  │  Telegram │    │   Agent Loop     │  │  │
│  │  │  Bot API  │───→│                  │  │  │
│  │  │  Polling  │    │  1. Receive msg   │  │  │
│  │  └──────────┘    │  2. ASR si vocal   │  │  │
│  │                   │  3. LLM call       │  │  │
│  │  ┌──────────┐    │  4. Tool exec      │  │  │
│  │  │  Skills/ │    │  5. Reply          │  │  │
│  │  │  Tools   │←───│                  │  │  │
│  │  └──────────┘    └──────┬───────────┘  │  │
│  │                         │               │  │
│  └─────────────────────────┼───────────────┘  │
│                            │                  │
│              ┌─────────────┼─────────────┐    │
│              ▼             ▼             ▼    │
│     OpenRouter     whisper-api      Outils   │
│     (LLM API)     (ASR po-2023)    locaux    │
└──────────────────────────────────────────────┘
```

## Agent Loop

Le coeur de NanoClaw est une boucle agentique :

1. **Polling Telegram** : Le bot ecoute les messages entrants (texte ou vocal)
2. **Pre-processing** :
   - Si message vocal : transcrire via `whisper-api.myia.io` (faster-whisper large-v3-turbo)
   - Si texte : passer directement a l'etape suivante
3. **Appel LLM** : Envoyer le message + historique + system prompt au modele
4. **Tool calling** : Si le LLM demande un tool, l'executer et renvoyer le resultat
5. **Reponse** : Envoyer la reponse finale via Telegram

## Skills System

Les skills sont des outils declaratifs que l'agent peut invoquer :

```yaml
skills:
  - name: web_search
    description: "Recherche web pour des informations actuelles"
    type: api_call

  - name: code_execute
    description: "Execute du code Python dans un sandbox"
    type: subprocess

  - name: file_read
    description: "Lit un fichier du workspace"
    type: filesystem
```

Chaque skill est expose au LLM via le schema function calling d'OpenAI. L'agent decide quand et comment les utiliser.

## Configuration

### Variables d'environnement

```env
# Telegram
TELEGRAM_BOT_TOKEN=123456:ABC-DEF...

# LLM
OPENROUTER_API_KEY=sk-or-v1-...
MODEL_NAME=openai/qwen3.6-35b-a3b

# ASR
ASR_ENDPOINT=https://whisper-api.myia.io/v1/audio/transcriptions
ASR_API_KEY=optional-bearer-token

# Agent
SYSTEM_PROMPT="Tu es un assistant utile..."
MAX_TOKENS=4096
TEMPERATURE=0.7
```

### Docker Compose (template)

```yaml
services:
  nanoclaw:
    image: nanoclaw:latest
    container_name: nanoclaw
    restart: unless-stopped
    env_file: nanoclaw.env
    volumes:
      - ./workspace:/app/workspace
    ports:
      - "8080:8080"  # Health check / metrics
```

## Endpoints ASR

Le service de transcription vocale est heberge sur po-2023 :

| Endpoint | Modele | Latence typique |
|----------|--------|-----------------|
| `POST /v1/audio/transcriptions` | faster-whisper large-v3-turbo | 2-5s (30s audio) |

Format de requete (compatible OpenAI Whisper API) :

```python
import requests

response = requests.post(
    "https://whisper-api.myia.io/v1/audio/transcriptions",
    files={"file": open("voice.ogg", "rb")},
    data={"model": "large-v3-turbo", "language": "fr"}
)
transcription = response.json()["text"]
```

## Deploiement

Voir [NanoClaw-Deploy.md](NanoClaw-Deploy.md) pour le guide complet de deploiement.

## Points de vigilance

- **Rate limiting** : OpenRouter a des limites par plan. Monitorer l'utilisation.
- **Contexte conversation** : Limiter l'historique envoyé au LLM pour controlling les couts.
- **Messages vocaux** : Les fichiers OGG Telegram doivent etre convertis avant ASR si le endpoint l'exige.
- **Securite** : Le bot token Telegram ne doit jamais etre commité. Utiliser des secrets Docker ou `.env` non versionné.
