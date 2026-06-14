# Runbook — Flip d'authentification des services exposés (#16 P2)

**Issue** : #16 — Sécurisation des services IA exposés.
**Scope** : activation de l'authentification (Bearer/proxy-key) sur les 2 services
LAN-exposés **cross-machine** non authentifiés : `claudish-proxy` (:3000) et
`myia-qdrant` (:6333). `tts-gateway` (P1) est un blocage USER séparé (secret
manuel), non couvert ici.
**Statut** : greenlight ai-01 2026-06-14 17:14Z — **Claudish d'abord**, puis Qdrant.
**Caveat scope** : les 2 compose vivent dans d'**autres repos** (`claudish`,
`roo-extensions`), pas CoursIA. Le flip est une **op manuelle** exécutée par
l'admin (fenêtre roo-extensions ou session dédiée) sur `po-2023`. Ce document
fournit le **runbook + validation** ; l'édition des composes n'a pas lieu dans
ce dépôt.

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

## Durcissement futur (P3, basse priorité)

- Claudish `proxy-auth.ts:49` : remplacer la comparaison `!==` par une comparaison
  **timing-safe** (équivalent `crypto.timingSafeEqual` / `secrets.compare_digest`).
- Les 2 services restent en binding `0.0.0.0` (LAN) — le reverse-proxy IIS
  (`*.myia.io`) est une couche séparée. Aucun des 2 n'est proxifié sur Internet
  aujourd'hui (vérifié : `claudish.myia.io` / `qdrant.myia.io` n'exposent pas de
  route publique). Si exposition IIS un jour, activer l'auth **avant**.
