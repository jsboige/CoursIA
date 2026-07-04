# Docker GenAI Security Audit

**Date:** 2026-05-08 (runbook rotation ajouté 2026-07-04, issue #16)
 **Issue:** #808 / #16
**Auditor:** po-2023 (Claude Code)
**Scope:** 20 containers on po-2023 (RTX 3080 Ti + RTX 3090)

## Runbook — rotation d'un secret (1 commande)

Tout secret **partagé** (clés API, tokens service↔client) vit dans `.secrets/master.env` (gitignored, source unique). La rotation se fait en **un render + un restart** — jamais d'édition éparpillée à la main.

```bash
# 1. Éditer la source unique
$EDITOR .secrets/master.env                      # ex: QDRANT_API_KEY=<nouvelle valeur>

# 2. Propager vers tous les .env consommateurs (idempotent)
python scripts/secrets/render_envs.py

# 3. Vérifier 0 drift (gate local, exit 1 si écart)
python scripts/secrets/render_envs.py --check

# 4. Redémarrer le container côté SERVEUR (OBLIGATOIRE — ComfyUI-Login
#    régénère son hash bcrypt au restart, pas à chaud ; Qdrant relit
#    QDRANT__SERVICE__API_KEY au startup)
docker compose -f docker-configurations/services/<svc>/docker-compose.yml restart
```

**Spécificité Qdrant (cross-repo) :** la compose Qdrant vit dans `roo-extensions` (autre repo), pas CoursIA. Le côté **client** (`QDRANT_API_KEY`, notebooks CoursIA) est centralisé dans `master.env` via `SECRET_KEYS` → rotation auto côté notebooks. Le côté **serveur** (`QDRANT__SERVICE__API_KEY`, double underscore) reste une op manuelle inter-repo sur `roo-extensions` (même valeur que le client). Détail convention client/serveur : [docs/genai/secrets-management.md](../docs/genai/secrets-management.md).

**Mots de passe par instance** (`COMFYUI_PASSWORD`, `FORGE_PASSWORD`, `WHISPER_*_PASSWORD`) NE sont PAS centralisés (un par container) — leur drift est prévenu par la règle du restart + self-check entrypoint, pas par render. Cf [docs/genai/secrets-management.md](../docs/genai/secrets-management.md).

## Executive Summary

**20/20 containers run as root with unlimited resources.** 1 service (Qdrant) has its reverse-proxy endpoint secured but its **direct LAN port still wide-open** (re-verified 2026-07-04, see §F4). 1 service had no auth code (tts-gateway, now fixed). Remaining exposed services have auth configured but bind to 0.0.0.0.

Overall risk: **HIGH**. Qdrant (vector DB) remains the most critical exposure: the IIS reverse proxy on `qdrant.myia.io` enforces auth (401 on `/collections` without a key), but **direct LAN access on port 6333 returns collection data with no auth at all** (`GET http://LAN:6333/collections` → `{"result":{"collections":[]}}`, 200). The `0.0.0.0` bind means anyone on the LAN can read/write vectors by bypassing the reverse proxy. Fix (set `QDRANT__SERVICE__API_KEY` on the Qdrant container OR bind `127.0.0.1:6333`) is a live inter-repo op on the `roo-extensions` compose — see the **Runbook** section at the top of this document and §F4.

> **Re-verification 2026-07-04 (po-2023, firsthand probes).** Qdrant reverse-proxy auth = ACTIVE (`https://qdrant.myia.io/collections` → 401 "Must provide an API key"). Qdrant direct LAN port 6333 = OPEN (`http://localhost:6333/collections` → 200 with data, container `myia-qdrant` binds `0.0.0.0:6333-6334`). whisper-api / tts-api / comfyui-video reverse-proxy = 401 (secured). demucs-api / z-image reverse-proxy = 502, musicgen-api = timeout (services down — availability, not auth). Live-config fix for Qdrant LAN exposure tracked on dashboard (inter-repo `roo-extensions`).

## Audit Table

| Service | Port(s) | Bind | Auth Method | Auth Active? | User | Mem Limit | Risk |
|---------|---------|------|-------------|-------------|------|-----------|------|
| **Qdrant** | 6333-6334 | 0.0.0.0 | NONE | NO | 0:0 | none | **CRITICAL** |
| **tts-gateway** | 8196 | 0.0.0.0 | Bearer token (added) | YES* | root | none | **HIGH** |
| **forge-turbo** | 1111, 17861 | 0.0.0.0 | gradio-auth | YES | root | none | MEDIUM |
| **sd-forge-main** | 7860 | 0.0.0.0 | gradio-auth | YES | root | none | MEDIUM |
| **sdnext** | 7861 | 0.0.0.0 | gradio-auth | YES | root | none | MEDIUM |
| **whisper-webui** | 36540 | 0.0.0.0 | Basic Auth | YES | root | none | MEDIUM |
| comfyui-qwen | 8188 | 0.0.0.0 | ComfyUI Login | YES | root | none | MEDIUM |
| comfyui-video | 8189 | 0.0.0.0 | ComfyUI Login | YES | root | none | MEDIUM |
| vllm-zimage | 8001 | 0.0.0.0 | vllm --api-key | YES | root | none | MEDIUM |
| whisper-api | 8190 | 0.0.0.0 | Bearer token | YES | root | none | LOW |
| tts-api | 8191 | 0.0.0.0 | Bearer token | YES | root | none | LOW |
| musicgen-api | 8192 | 0.0.0.0 | Bearer token | YES | root | none | LOW |
| demucs-api | 8193 | 0.0.0.0 | Bearer token | YES | root | none | LOW |
| funasr-api | 8194 | 0.0.0.0 | Bearer token | YES | root | none | LOW |
| qwen-asr-api | 8195 | 0.0.0.0 | Bearer token | YES | root | none | LOW |
| tts-kokoro | internal | N/A | N/A | N/A | root | none | OK |
| tts-tada | internal | N/A | N/A | N/A | root | none | OK |
| tts-qwen | internal | N/A | N/A | N/A | root | none | OK |

## Findings

### F1. ALL containers run as root (20/20)

Every container runs as root (empty `user:` field = root). A container escape vulnerability would grant full host access.

**Evidence:**
```
docker inspect <name> --format '{{.Config.User}}'
# Returns empty string for 19/20 containers, "0:0" for Qdrant
```

**Fix:** Add `user: "1000:1000"` to each service in docker-compose.yml. Test each service after applying (some may need chown on volumes).

### F2. NO resource limits (20/20)

All containers have unlimited memory and CPU. A rogue request or memory leak in one service can starve all others.

**Evidence:**
```
docker inspect <name> --format 'Memory={{.HostConfig.Memory}} NanoCpus={{.HostConfig.NanoCpus}}'
# Returns Memory=0 NanoCpus=0 for all 20 containers
```

**Fix:** Add `deploy.resources.limits` to each compose file:
```yaml
deploy:
  resources:
    limits:
      memory: 4G    # per service, adjust based on model
      cpus: '2.0'
```

### F3. All ports bind 0.0.0.0 (17/20 exposed)

17 services bind to `0.0.0.0`, accessible from any network interface. Only 3 TTS workers use internal networking.

The IIS reverse proxy on `*.myia.io` domains provides auth, but direct LAN access on port X bypasses it entirely.

**Fix:** Change port bindings from `0.0.0.0:PORT:PORT` to `127.0.0.1:PORT:PORT` for services behind IIS reverse proxy. Only expose services that need direct access.

### F4. 1 service has NO authentication, 1 had missing auth code

| Service | Port | Issue |
|---------|------|-------|
| Qdrant | 6333-6334 | **Re-verified 2026-07-04.** Reverse-proxy `qdrant.myia.io` = 401 (auth ACTIVE). Direct LAN `0.0.0.0:6333` = 200 with collection data, **no auth**. `QDRANT__SERVICE__API_KEY` not set server-side (else `/collections` would demand a key on direct port too). Full CRUD open on LAN. |
| tts-gateway | 8196 | Was missing auth middleware import (FIXED in earlier PR — now uses shared/auth_middleware.py) |

Note: SD Forge/SDNext/forge-turbo already have `--gradio-auth` with user/password from env vars. Whisper-webui already has `--username`/`--password` in entrypoint. These services auth is ACTIVE but they still bind 0.0.0.0 (see F3).

**Fix:**
- **Qdrant:** Enable API key via `QDRANT__SERVICE__API_KEY` env var or config.yaml
- **SD Forge/SDNext:** Add `--gradio-auth user:pass` or `--api-key` to startup args
- **tts-gateway:** Import and use `auth_middleware.py` from shared/
- **whisper-webui:** Add `--auth` flag or bind to 127.0.0.1 only

### F5. Auth middleware is opt-in, not enforced

The `shared/auth_middleware.py` only activates if `API_KEY` env var is set. If missing, auth is silently disabled with a warning log.

**Fix:** Change default behavior: if no `API_KEY` is set, reject all non-health requests with HTTP 503 "Service misconfigured: API_KEY not set".

### F6. Secrets in environment variables

API keys are passed via `.env` files and `environment:` blocks in docker-compose. These are visible via `docker inspect` on the host.

**Risk level:** LOW (single-user workstation, not multi-tenant). Acceptable for now.

**Future improvement:** Use Docker secrets (`docker secret create`) for production deployments.

## Recommendations (Priority Order)

### Quick Wins (DONE in this PR)

1. **tts-gateway auth:** Import `auth_middleware.py`, add `API_KEY` env var (DONE)
2. **SECURITY.md audit:** Comprehensive audit document created (DONE)

### Next Steps (requires separate PR or manual ops)

1. **Qdrant auth (serveur) :** Add `QDRANT__SERVICE__API_KEY=${QDRANT_API_KEY}` to environment + `.env` — compose Qdrant dans `roo-extensions` (autre repo), op manuelle inter-repo. Le côté **client** (`QDRANT_API_KEY`, notebooks CoursIA) est désormais centralisé dans `master.env` via `SECRET_KEYS` (render_envs.py) — rotation auto côté notebooks, cf runbook en tête de ce document.
2. **Bind 127.0.0.1:** Change port bindings for services behind IIS reverse proxy

### Medium Priority (2-4h, requires testing)

1. **Run as non-root:** Add `user: "1000:1000"` to all compose files, chown volumes
2. **Resource limits:** Add `mem_limit` and `cpus` to all services
3. **Auth middleware default-deny:** Change auth_middleware.py to reject if no API_KEY

### Low Priority (nice to have)

1. **Docker secrets:** Migrate from env vars to Docker secrets
2. **Network isolation:** Create separate Docker networks for internal vs exposed services
3. **Read-only root FS:** Add `read_only: true` + tmpfs mounts for /tmp, /run

## Per-Service Hardening Plan

### Qdrant (CRITICAL)

```yaml
services:
  qdrant:
    image: qdrant/qdrant:latest
    ports:
      - "127.0.0.1:6333:6333"    # Bind localhost only
      - "127.0.0.1:6334:6334"    # gRPC localhost only
    environment:
      - QDRANT__SERVICE__API_KEY=${QDRANT_API_KEY}
    user: "1000:1000"
    deploy:
      resources:
        limits:
          memory: 4G
          cpus: '2.0'
```

### Audio API services (whisper, tts, musicgen, demucs, funasr, qwen-asr)

These already use `auth_middleware.py`. Hardening:
```yaml
    ports:
      - "127.0.0.1:${PORT}:${PORT}"   # Bind localhost
    user: "1000:1000"
    deploy:
      resources:
        limits:
          memory: 4G
          cpus: '2.0'
```

### ComfyUI services (qwen, video)

Already have ComfyUI Login. Add:
```yaml
    user: "1000:1000"
    deploy:
      resources:
        limits:
          memory: 8G
          cpus: '4.0'
```

### SD Forge / SDNext (NO AUTH)

Must add auth OR bind to localhost:
```yaml
    ports:
      - "127.0.0.1:${PORT}:${PORT}"   # Bind localhost only
    # OR add --gradio-auth to command
    user: "1000:1000"
    deploy:
      resources:
        limits:
          memory: 4G
          cpus: '2.0'
```

### tts-gateway (FIXED in this PR)

Auth middleware now imported in `gateway/app.py`, `API_KEY` env var added to compose:
```yaml
    environment:
      - API_KEY=${TTS_GATEWAY_API_KEY:-}
    volumes:
      - type: bind
        source: ../shared
        target: /app/shared
        read_only: true
```

Still needs: `127.0.0.1` binding + `user: "1000:1000"` + resource limits (next PR).

## Validation Checklist

After applying hardening:
- [ ] `docker inspect <name> --format '{{.Config.User}}'` returns non-empty for all containers
- [ ] `docker inspect <name> --format '{{.HostConfig.Memory}}'` returns non-zero
- [ ] `curl http://localhost:6333/collections` returns 401/403 (Qdrant auth active)
- [ ] `curl http://LAN_IP:PORT/health` fails for all services (localhost-only bind)
- [ ] `curl http://localhost:8190/v1/audio/transcriptions` without Bearer returns 401
- [ ] All GenAI notebook tests pass (regression check)
- [ ] IIS reverse proxy `*.myia.io` still routes correctly

## Incident History

- **2026-05-07**: Audit initiated (Issue #808). 15 containers binding 0.0.0.0 as root with no auth.
- **2026-05-08**: Full audit completed by po-2023. 6 services CRITICAL/HIGH risk identified.
