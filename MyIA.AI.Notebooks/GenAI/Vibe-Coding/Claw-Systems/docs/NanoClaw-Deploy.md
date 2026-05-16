# NanoClaw - Guide de Deploiement

## Prerequis

| Outil | Version | Usage |
|-------|---------|-------|
| Docker | 20.10+ | Conteneurisation |
| Docker Compose | v2+ | Orchestration |
| curl | any | Tests API |

### Tokens requis

1. **Telegram Bot Token** : Creer via [@BotFather](https://t.me/BotFather) sur Telegram
2. **OpenRouter API Key** : [openrouter.ai](https://openrouter.ai) — route vers GPT-4o, Claude, etc.
3. **ASR Bearer Token** (optionnel) : Si `whisper-api.myia.io` requiert une authentification

## Installation

### 1. Preparer le repertoire

```bash
mkdir -p /opt/nanoclaw && cd /opt/nanoclaw
```

### 2. Configuration

Creer le fichier `.env` a partir du template :

```bash
cp nanoclaw.env.example .env
```

Editer `.env` avec vos tokens :

```env
# OBLIGATOIRE
TELEGRAM_BOT_TOKEN=123456:ABC-DEF...
OPENROUTER_API_KEY=sk-or-v1-...

# OPTIONNEL
ASR_ENDPOINT=https://whisper-api.myia.io/v1/audio/transcriptions
MODEL_NAME=openai/qwen3.6-35b-a3b
SYSTEM_PROMPT=Tu es NanoClaw, un assistant autonome.
```

### 3. Lancer le service

```bash
docker compose -f docker-compose.nanoclaw.yml up -d
```

### 4. Verifier le deploiement

```bash
# Health check
curl http://localhost:8080/health

# Logs
docker logs -f nanoclaw
```

### 5. Tester via Telegram

Envoyer un message texte au bot Telegram. Verifier dans les logs que :
1. Le message est recu
2. Le LLM repond
3. La reponse est envoyee sur Telegram

## Test de la transcription vocale

Envoyer un message vocal au bot. Le flux attendu :

```
[Telegram] Voice message received (duration: 5s, format: ogg)
[ASR] Transcribing via whisper-api.myia.io...
[ASR] Result: "Bonjour, quelle est la meteo a Paris ?"
[LLM] Processing: "Bonjour, quelle est la meteo a Paris ?"
[LLM] Response: "A Paris, il fait actuellement..."
[Telegram] Reply sent
```

Si la transcription echoue :
- Verifier la connectivite vers `whisper-api.myia.io`
- Tester manuellement : `curl -X POST https://whisper-api.myia.io/v1/audio/transcriptions -F "file=@test.ogg" -F "model=large-v3-turbo"`

## Configuration avancee

### Modele local (alternative a OpenRouter)

Si un LLM local est disponible (Ollama, vLLM) :

```env
LLM_BASE_URL=http://localhost:11434/v1
MODEL_NAME=llama3
OPENROUTER_API_KEY=not-needed
```

### Subdomain et HTTPS

Pour exposer NanoClaw via un sous-domaine :

```nginx
server {
    listen 443 ssl;
    server_name nanoclaw.myia.io;

    ssl_certificate /etc/letsencrypt/live/nanoclaw.myia.io/fullchain.pem;
    ssl_certificate_key /etc/letsencrypt/live/nanoclaw.myia.io/privkey.pem;

    # Authentification par bearer token
    location / {
        proxy_pass http://localhost:8080;
        proxy_set_header Authorization $http_authorization;
    }
}
```

### Monitoring

```yaml
# Ajouter au docker-compose
services:
  nanoclaw:
    # ...
    environment:
      - LOG_LEVEL=info
    logging:
      driver: json-file
      options:
        max-size: "10m"
        max-file: "3"
```

## Troubleshooting

| Symptome | Cause probable | Resolution |
|----------|---------------|------------|
| Bot ne repond pas | Token Telegram invalide | Verifier via BotFather |
| Erreur LLM 401 | API key OpenRouter | Verifier cle + credits |
| Timeout ASR | whisper-api down | `curl whisper-api.myia.io/health` |
| Container restart loop | `.env` manquant | Verifier `docker logs nanoclaw` |

## Mise a jour

```bash
docker compose pull
docker compose up -d
```
