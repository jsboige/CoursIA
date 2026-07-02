# NanoClaw - Guide de Deploiement

> **Backend LLM** : NanoClaw consomme le proxy **Claudish** (voir [`Vibe-Coding/Claudish/docs/Claudish-Proxy.md`](../Claudish/docs/Claudish-Proxy.md)), qui route vers 3 providers budgetés selon le tier — **pas** OpenRouter en direct. La configuration ci-dessous reflete cet agencement de production.

## Prerequis

| Outil | Version | Usage |
|-------|---------|-------|
| Docker | 20.10+ | Conteneurisation |
| Docker Compose | v2+ | Orchestration |
| curl | any | Tests API |

### Tokens / acces requis

1. **Telegram Bot Token** : Creer via [@BotFather](https://t.me/BotFather) sur Telegram
2. **Acces Claudish** : `ANTHROPIC_BASE_URL` du proxy (ex. `https://models.myia.io`) + une clé d'auth (`ANTHROPIC_AUTH_TOKEN`). Claudish route ensuite vers le provider du tier demande — voir le guide Claudish pour les providers sous-jacents (GLM Coding Plan / vLLM Qwen / Anthropic natif).
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

Editer `.env` avec vos acces :

```env
# OBLIGATOIRE
TELEGRAM_BOT_TOKEN=123456:ABC-DEF...

# Backend LLM = Claudish (proxy Anthropic-compatible multi-providers)
ANTHROPIC_BASE_URL=https://models.myia.io
ANTHROPIC_AUTH_TOKEN=<claudish-token>
# Tier cible (Claudish remappe vers le provider budgete du tier) :
MODEL_NAME=glm-5.2

# OPTIONNEL
ASR_ENDPOINT=https://whisper-api.myia.io/v1/audio/transcriptions
SYSTEM_PROMPT=Tu es NanoClaw, un assistant autonome.
```

> **Note sur `MODEL_NAME`** : NanoClaw parle le wire Anthropic via Claudish. Envoyer un nom de modele du tier voulu (`glm-5.2` = Sonnet-tier via GLM, `claude-opus-4-8` = Opus-tier Anthropic natif, `qwen3.6-35b-a3b` = Haiku-tier vLLM). Claudish gere la traduction vers le provider réel — NanoClaw n'a pas a connaitre GLM, vLLM ou Anthropic en direct. Voir la section « Connecter un bot » de `Claudish-Proxy.md`.

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
3. La réponse est envoyee sur Telegram

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

### Changer de tier / de modele

Le tier se change en une ligne via `MODEL_NAME`, sans toucher au transport :

```env
# Sonnet-tier (GLM via Claudish) — defaut, bon rapport qualite/cout
MODEL_NAME=glm-5.2

# Haiku-tier (vLLM Qwen self-hoste) — leger, rapide
MODEL_NAME=qwen3.6-35b-a3b

# Opus-tier (Anthropic natif) — reflexion lourde
MODEL_NAME=claude-opus-4-8
```

### Bypass Claudish (provider en direct)

En dev, on peut court-circuiter Claudish et pointer un provider compatible Anthropic en direct (ex. la couche de compat z.ai, meme pattern que le module [06-Hermes-Deploy](06-Hermes-Deploy-s6-Overlay.md)) :

```env
ANTHROPIC_BASE_URL=https://api.z.ai/api/anthropic
ANTHROPIC_AUTH_TOKEN=<zai-api-key>
MODEL_NAME=glm-5.2
```

> En production, préférer Claudish : il ajoute le controle de concurrence, le never-hang (priorite #1), la conversion overload 529 + Retry-After, et l'observabilite (captures, surveillance trafic). Voir `Claudish-Proxy.md` §6.

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
| Erreur LLM 401 | Clé Claudish / `ANTHROPIC_AUTH_TOKEN` | Verifier la cle + que `ANTHROPIC_BASE_URL` pointe le proxy |
| Erreur LLM 404 sur `/chat/completions` | NanoClaw envoie du wire OpenAI au lieu d'Anthropic | Claudish ne sert que le wire Anthropic — verifier que NanoClaw utilise le transport Anthropic (voir `Claudish-Proxy.md` §5, lecon Hermes) |
| Slug modele 404 (`glm-5-2`) | Tiret au lieu du point | Utiliser `glm-5.2` (point), pas `glm-5-2` |
| Timeout ASR | whisper-api down | `curl whisper-api.myia.io/health` |
| Container restart loop | `.env` manquant | Verifier `docker logs nanoclaw` |

## Mise a jour

```bash
docker compose pull
docker compose up -d
```
