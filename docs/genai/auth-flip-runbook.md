# Runbook — Flip d'authentification des services exposés (#16 P2)

**Issue** : #16 — Sécurisation des services IA exposés.
**Scope** : activation de l'authentification (Bearer/proxy-key) sur les services
LAN-exposés non authentifiés : `claudish-proxy` (:3000), `myia-qdrant` (:6333) et
`tts-gateway` (:8196). **Mise à jour 2026-06-28** : `tts-gateway` (P1) était un
blocage USER — désormais **RECOVERABLE-COORD** (ai-01 a ajouté `TTS_GATEWAY_API_KEY`
au schéma `SECRET_KEYS` via PR #4566 + délégué le bootstrap au value-holder
po-2023 qui héberge la gateway). Procédure couverte **Phase 3** ci-dessous.
**Statut** : greenlight ai-01 2026-06-14 17:14Z — Claudish + Qdrant ;
**tts-gateway EXECUTÉ 2026-06-28** (post-merge #4566, flip vérifié firsthand :
`/v1/models` 401→200 avec clé, endpoint public `tts-multi.myia.io` sécurisé).
Claudish + Qdrant restent à exécuter.
**Caveat scope** : Claudish + Qdrant vivent dans d'**autres repos** (`claudish`,
`roo-extensions`) — le flip y est une **op manuelle** admin. `tts-gateway` est le
seul des 3 dont le compose est **dans CoursIA** (`docker-configurations/services/tts-multi/`)
→ flip exécutable par un worker via le flux canonical `master.env` + `render_envs.py`.

> Référence d'analyse : [service-security-audit.md](service-security-audit.md)
> (bindings, blast-radius, mécanisme d'auth disponible). Ce runbook en est la
> déclinaison opérationnelle, vérifiée contre le code source.

---

## 0. Faits vérifiés contre le code source (SDDD, 2026-06-14)

L'auth est **déjà codée** pour les 2 services. Le flip = **définir une variable
d'env + redémarrer**, sans développement, **réversible**.

| Service | Compose (REPO ≠ CoursIA) | Var serveur (active le 401) | Réversible |
|---------|--------------------------|------------------------------|------------|
| `claudish-proxy` :3000 | `D:\Dev\claudish\docker-compose.yml` | `CLAUDISH_PROXY_KEY` (→ champ config `proxyKey`) | oui (vider + restart) |
| `myia-qdrant` :6333-6334 | `D:\Dev\roo-extensions\docker\docker-compose.yml` | `QDRANT__SERVICE__API_KEY` (native Qdrant, **double `_`**) | oui (idem) |

---

## Phase 1 — Claudish (d'abord, blast plus contenu)

### Mécanisme (vérifié `claudish/packages/cli/src/`)

- `proxy-server.ts:313` : `const proxyKey = process.env.CLAUDISH_PROXY_KEY || loadConfig().proxyKey` — la var d'env **prime** sur le fichier de config.
- `fork/index.ts:30-31` : le middleware `createProxyAuthMiddleware` est monté sur `/v1/*` **uniquement si `proxyKey` est non vide**. Vide = pas de middleware = ouvert (état actuel).
- `fork/middleware/proxy-auth.ts` : enforce la clé proxy pour les requêtes **non-GET et non-Anthropic** sur `/v1/*`.
  - **GET exempté** (healthcheck Docker `/health`, discovery `/v1/models`).
  - **Pass-through Anthropic exempté** (`native-anthropic`) — géré par `NativeHandler` (OAuth ou swap de clé).
  - Header accepté : `x-proxy-key` **ou** `x-api-key` **ou** `Authorization: Bearer <key>` (premier non vide).
  - ⚠️ Comparaison `provided !== proxyKey` (**non timing-safe**, `proxy-auth.ts:49`). Moins robuste que `auth_middleware.py` (`secrets.compare_digest`). Durcissement futur possible mais non bloquant.

### Pre-flight (à compléter avant le flip)

1. **Énumérer les consommateurs claudish** : qui appelle `:3000` en POST non-anthropic ? (agents Roo/Claude du cluster en proxy LLM). Lister les clients à qui propager la clé.
2. **Générer une clé forte** (≥32 chars aléatoires). Rotation indépendante de Qdrant.

### Procédure de flip (sur `po-2023`, manuel)

1. Éditer `D:\Dev\claudish\.env` (fichier **gitignoré**, édition manuelle — le hook `block-secrets.py` interdit l'édition agent) :
   ```
   CLAUDISH_PROXY_KEY=<clé-forte-générée>
   ```
2. Recréer le conteneur pour propager l'env :
   ```bash
   docker compose -f D:\Dev\claudish\docker-compose.yml up -d
   ```
3. **Vérifier la preuve** (401 sans clé, 200 avec clé) :
   ```bash
   # Baseline avant flip (état OUVERT, vérifié 2026-06-14) : doit devenir 401.
   curl -s -o /dev/null -w "%{http_code}\n" -X POST http://localhost:3000/v1/messages \
     -H "Content-Type: application/json" \
     -d '{"model":"openai/gpt-4o-mini","messages":[{"role":"user","content":"hi"}]}'
   #   AVANT flip : 200 (ouvert)   |   APRÈS flip : 401

   # Healthcheck (exempt) reste 200 — confirme le service UP.
   curl -s -o /dev/null -w "%{http_code}\n" http://localhost:3000/health   # 200

   # Preuve que la clé ouvre la route (modèle NON-anthropic obligatoire) :
   curl -s -o /dev/null -w "%{http_code}\n" -X POST http://localhost:3000/v1/messages \
     -H "Content-Type: application/json" -H "x-proxy-key: <clé-forte-générée>" \
     -d '{"model":"openai/gpt-4o-mini","messages":[{"role":"user","content":"hi"}]}'
   #   APRÈS flip : 200
   ```
4. **Propager la clé** aux consommateurs claudish listés au pre-flight (via GDrive chiffré, **jamais** RooSync — règle no-secrets-roosync).

> ⚠️ **Piège de test** : un `POST /v1/messages` avec un modèle `claude-*` reste **200
> même après le flip** (pass-through Anthropic exempté). Pour valider le gate, on
> DOIT utiliser un modèle non-anthropic (`openai/*`, `gemini/*`, etc.).

### Rollback (instantané)

Vider `CLAUDISH_PROXY_KEY=` dans `D:\Dev\claudish\.env` + `docker compose ... up -d`
→ `proxyKey` vide → middleware non monté → retour à l'état ouvert. Aucune donnée
perdue.

---

## Phase 2 — Qdrant (après validation Claudish, blast cluster-wide)

### Subtilité 2-variables — ne PAS confondre

| Var | Côté | Rôle |
|-----|------|------|
| `QDRANT__SERVICE__API_KEY` (**double `_`**) | serveur Qdrant | **active** le 401 |
| `QDRANT_API_KEY` (**simple `_`**) | client MCP `roo-state-manager` | **envoie** la clé pour s'authentifier |

Les 2 doivent matcher. `QDRANT_API_KEY` est une `REQUIRED_ENV_VAR` du MCP
(validée au startup, `process.exit(1)` si vide) → **déjà peuplée** sur chaque
machine du cluster (actuellement ignorée car auth désactivée côté serveur).

### Pre-flight (Step 0 — AVANT le flip serveur)

1. **Confirmer la liste des machines** du cluster (pour la propagation).
2. Sur **chaque machine**, vérifier que `QDRANT_API_KEY` dans l'env MCP
   `roo-state-manager` (`roo-extensions/mcps/internal/servers/roo-state-manager/.env`
   ou `~/.claude.json` → `mcpServers.roo-state-manager.env`) **matche la clé
   prévue côté serveur**. Vérifier `conversation_browser list` fonctionne AVEC la
   clé pendant que Qdrant est encore sans auth (clé ignorée si auth off =
   migration transparente).
3. Générer la clé Qdrant (rotation indépendante de Claudish).

> **Blast-radius maximal** : `myia-qdrant` est consommé par le MCP
> `roo-state-manager` sur **toutes** les machines (`conversation_browser`,
> `roosync_search`, `roosync_indexing`). Un flip serveur non coordonné (Step 0
> incomplet) = indexation/recherche cassées sur tout le cluster jusqu'à
> propagation (cf. leçon Infra #560 — dashboards dark ~48h si clé client
> absente).

### Procédure de flip (sur `po-2023`, APRÈS Step 0 complété sur toutes les machines)

1. Éditer `D:\Dev\roo-extensions\docker\.env` (gitignoré, manuel) :
   ```
   QDRANT__SERVICE__API_KEY=<même clé que QDRANT_API_KEY client>
   ```
2. Recréer le conteneur :
   ```bash
   docker compose -f D:\Dev\roo-extensions\docker\docker-compose.yml up -d myia-qdrant
   ```
3. **Vérifier la preuve** :
   ```bash
   # Sans clé : doit retourner 401/403 APRÈS flip (200 avant).
   curl -s -o /dev/null -w "%{http_code}\n" http://localhost:6333/collections
   # Avec clé :
   curl -s -o /dev/null -w "%{http_code}\n" -H "api-key: <clé>" http://localhost:6333/collections
   ```
4. **Vérifier l'usage cluster** : `roosync_search semantic` depuis chaque machine doit réussir.

### Rollback (instantané)

Vider `QDRANT__SERVICE__API_KEY=` dans `D:\Dev\roo-extensions\docker\.env` +
`docker compose ... up -d myia-qdrant` → retour no-auth. Les clés client propagées
deviennent noop. Aucune collection perdue (Qdrant garde ses données).

---

## Ordre recommandé

1. **Claudish** (blast contenu, auth codée = dry-run du mécanisme, confirme le
   playbook rollback).
2. **Qdrant** (blast maximal = exige Step 0 propagation `QDRANT_API_KEY` sur
   toutes les machines AVANT le flip serveur).
3. **tts-gateway** (blast le plus contenu — consommateurs GenAI uniquement, tous
   key-aware ; mais **seul exposé publiquement** via `tts-multi.myia.io` →
   priorité de sécurité la plus haute une fois deblocked). Exécutable dès merge
   #4566.

---

## Phase 3 — tts-gateway (deblocked 2026-06-28, compose dans CoursIA)

**Différence clé vs Phase 1/2** : le compose est **dans ce dépôt**, le secret est
**partagé** (notebooks GenAI le lisent) → flux canonical `master.env` +
`render_envs.py` (pas d'édition manuelle de `.env`). C'est aussi le **seul des 3
exposé publiquement** (`tts-multi.myia.io` via IIS).

### Mécanisme (vérifié `docker-configurations/services/tts-multi/gateway/app.py`)

- `app.py:20-26` : la gateway monte `/app/shared/auth_middleware.py` (bind-mount
  `../shared` → `/app/shared`, `docker-compose.yml:31-34`) **s'il existe**, et
  appelle `setup_auth(app)` dans un `try/except` (`app.py:50-54`) — exception →
  log "running without auth" (dégrade silencieusement en ouvert).
- `auth_middleware.py:40-54` (`docker-configurations/services/shared/`) : lit
  `API_KEY`. **Vide** → `_AUTH_ENABLED = False` → "Auth middleware NOT installed -
  API is open" (état actuel live). **Non-vide** → `BearerAuthMiddleware` monté sur
  **tous les paths sauf** `/health`, `/docs`, `/openapi.json`, `/redoc`, `/admin/*`
  (`_PUBLIC_PATHS`, `auth_middleware.py:92`). Comparaison **timing-safe**
  `secrets.compare_digest` (`:74`, `:127`) — **déjà durci** (contrairement à Claudish).
- `docker-compose.yml:26` : `API_KEY=${TTS_GATEWAY_API_KEY:-}` → propage la var.
  Vide = pas d'auth. **Le flip = provisionner la valeur + redémarrer, 0 changement
  de code.**

### Bonus hardening : bind `127.0.0.1` (compose) vs `0.0.0.0` (live)

- `docker-compose.yml:18` : `"127.0.0.1:${TTS_GATEWAY_PORT:-8196}:8000"` (localhost-only).
- **Live (vérifié 2026-06-28 `docker port tts-gateway`)** : `0.0.0.0:8196` — le
  conteneur est **stale** (démarré d'un compose antérieur à la correction). Le
  `--force-recreate` du flip applique **les deux** corrections en une fois :
  activation de l'auth **et** bind localhost-only (LAN → ne peut plus être atteint
  directement hors localhost + proxy IIS).

### Blast-radius (vérifié firsthand 2026-06-28, G.1)

| Consommateur | Lit la clé ? | Impact post-flip |
|--------------|--------------|------------------|
| Notebooks GenAI (`qwen_tts_client.py:54`) | ✅ `os.getenv("TTS_GATEWAY_API_KEY") or os.getenv("KOKORO_API_KEY")` (fallback Kokoro) | 0 si `GenAI/.env` propagé |
| Helper GenAI (`genai_service.py:164-166`) | ✅ special-case tts-gateway → `TTS_GATEWAY_API_KEY` | 0 |
| Claudish (`D:\Dev\claudish\{apps,packages,scripts,skills,docs}`) | ❌ 0 référence réelle (`8196` = faux positif `膖` unicode dans `dist/`) | 0 |
| NanoClaw | ❌ dépendance ASR (whisper/qwen-asr), pas TTS | 0 |
| Autres machines (po-2024/2025/2026) | ❌ QC/Lean/ML, ne lancent pas GenAI Audio | 0 |

**Verdict blast-radius : LOW, contenu à GenAI sur po-2023, tous key-aware.**

### Pre-flight

1. **#4566 merged** : `TTS_GATEWAY_API_KEY` ∈ `SECRET_KEYS` dans
   `scripts/secrets/render_envs.py` (sinon `render_envs.py` ne propage pas la clé).
2. **Générer la clé forte** (jamais commitée/in dashboard) :
   ```bash
   python -c "import secrets; print(secrets.token_urlsafe(32))"  # ≥43 chars URL-safe
   ```

### Procédure de flip (sur `po-2023`, post-merge #4566)

1. **Bootstrap master.env** (gitignoré, source unique) — append d'une ligne
   (sans lire les autres valeurs du fichier) :
   ```bash
   printf '\nTTS_GATEWAY_API_KEY=%s\n' "$(python -c 'import secrets; print(secrets.token_urlsafe(32))')" \
     >> /d/Dev/CoursIA/.secrets/master.env
   grep -c "TTS_GATEWAY_API_KEY" /d/Dev/CoursIA/.secrets/master.env  # → 1 (count, pas la valeur)
   ```
2. **Render + vérifier la propagation** :
   ```bash
   cd /d/Dev/CoursIA && python scripts/secrets/render_envs.py
   grep -c "TTS_GATEWAY_API_KEY" docker-configurations/services/tts-multi/.env  # → 1
   grep -c "TTS_GATEWAY_API_KEY" MyIA.AI.Notebooks/GenAI/.env                    # → 1
   ```
3. **Rebuild + recréer la gateway** (applique API_KEY + bind 127.0.0.1) :
   ```bash
   cd /d/Dev/CoursIA/docker-configurations/services/tts-multi && docker compose up -d --no-deps --build --force-recreate tts-gateway
   docker port tts-gateway  # doit maintenant afficher 127.0.0.1:8196 (pas 0.0.0.0)
   ```

   > ⚠️ **★★★ stale-image trap (vérifié firsthand 2026-06-28)** : `--force-recreate` **SEUL ne
   > reconstruit PAS l'image** — il réutilise l'image existante. Or l'image tts-gateway
   > était **built AVANT** que le code `setup_auth` soit ajouté à `gateway/app.py` →
   > `/app/app.py` dans le container n'avait AUCUNE référence à `setup_auth`/`API_KEY` →
   > l'auth restait **OFF silencieusement** (`/v1/models` retournait 200 au lieu de 401,
   > logs container vides). **Diagnostic** : `docker exec tts-gateway sh -c 'grep -c
   > setup_auth /app/app.py'` → `0` = image stale. **Fix** : `docker compose build
   --no-deps tts-gateway` (rebuild depuis le source courant) puis recreate. Le flag
   `--build` dans la commande ci-dessus fait les deux. `--no-deps` évite de tenter de
   démarrer tts-tada (non-déployé). Le service utilise `build:` (image locale), pas
   `image:` — tout changement au source `gateway/app.py` exige un rebuild.

4. **Vérifier la preuve** (401 sans clé, 200 avec clé, 401 mauvaise clé) :
   ```bash
   # Sans clé : doit devenir 401 APRÈS flip (200 avant).
   curl -s -o /dev/null -w "%{http_code}\n" http://localhost:8196/v1/models
   # Healthcheck (public path) reste 200 — confirme UP.
   curl -s -o /dev/null -w "%{http_code}\n" http://localhost:8196/health
   # Avec clé : 200.
   curl -s -o /dev/null -w "%{http_code}\n" -H "Authorization: Bearer $(grep TTS_GATEWAY_API_KEY /d/Dev/CoursIA/.secrets/master.env | cut -d= -f2)" http://localhost:8196/v1/models
   # Mauvaise clé : 401 (confirme que le gate ne fait pas que vérifier la présence du header).
   curl -s -o /dev/null -w "%{http_code}\n" -H "Authorization: Bearer wrongkey" http://localhost:8196/v1/models
   # Logs container doivent confirmer : "Bearer token authentication ENABLED".
   docker logs tts-gateway 2>&1 | grep -i "authentication ENABLED"
   ```
5. **Vérifier le notebook consommateur** : re-exécuter `02-5-Multi-Model-TTS-Gateway.ipynb`
   (kernel `mcp-jupyter-py310`, `--cwd` le dossier du notebook) → doit toujours
   produire l'embed kokoro (la clé est lue via `GenAI/.env`).

### Rollback tts-gateway (instantané)

Vider `TTS_GATEWAY_API_KEY=` dans `master.env` + `render_envs.py` +
`docker compose up -d --force-recreate tts-gateway` → `API_KEY` vide →
`_AUTH_ENABLED=False` → retour no-auth. Aucune donnée perdue.

> ⚠️ **Exposition publique** : `tts-multi.myia.io` (IIS → `localhost:8196`) est le
> **seul des 3 services proxifié sur Internet**. Une fois le flip fait, toute requête
> publique sans Bearer → 401. C'est précisément l'objectif (#16), mais cela signifie
> aussi qu'un consommateur externe non-mis-à-jour casserait immédiatement — d'où la
> vérification blast-radius ci-dessus (GenAI-only, tous key-aware).

---

## Durcissement futur (P3, basse priorité)

- Claudish `proxy-auth.ts:49` : remplacer la comparaison `!==` par une comparaison
  **timing-safe** (équivalent `crypto.timingSafeEqual` / `secrets.compare_digest`).
- Les 2 services restent en binding `0.0.0.0` (LAN) — le reverse-proxy IIS
  (`*.myia.io`) est une couche séparée. Aucun des 2 n'est proxifié sur Internet
  aujourd'hui (vérifié : `claudish.myia.io` / `qdrant.myia.io` n'exposent pas de
  route publique). Si exposition IIS un jour, activer l'auth **avant**.
