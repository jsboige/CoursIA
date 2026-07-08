# Audit de sécurisation des services IA auto-hébergés (po-2023)

**Issue** : #16 — Sécurisation des services IA exposés.
**Machine** : po-2023 (hôte GenAI du cluster).
**Date de l'audit** : 2026-06-14.
**Méthode** : recon `docker ps` (bindings) + sondes `curl` sans token (état d'auth réel)
+ lecture du code d'auth (`auth_middleware.py`, compose par service). Aucun secret
n'est reproduit ici — uniquement des **noms** de variables et des **codes HTTP**.

> Règle de preuve (#16) : un service est « sécurisé » seulement si **401 sans token
> ET 200 avec token**, vérifié en direct — jamais sur déclaration.

---

## 0. Re-audit live (2026-07-08) — delta vs état 2026-06-14

Re-sondage firsthand `docker ps` + `curl` sans token (sans/avec) le 2026-07-08 par
po-2023. **La posture s'est améliorée depuis l'audit initial** : le trou public
Internet (P1) est **fermé**.

| Service | Audit 2026-06-14 | **Live 2026-07-08** | Statut |
|---|---|---|---|
| `tts-gateway:8196` | `0.0.0.0` LAN, `/v1/models` **200 open** | **`127.0.0.1` local**, `/v1/models` **401** | ✅ **REMEDIATED** (P1 Docker + auth) |
| `tts-multi.myia.io` (public IIS) | `/v1/models` **200 open** = « le plus grave » | `/v1/models` **401** | ✅ **REMEDIATED** (P1 public) |
| `whisper-api:8190` | 401 secured | `/v1/models` **401** | ✅ stable (modèle de référence) |
| `claudish-proxy:3000` (LAN) | root **200 open** | root **200**, `/health` **200** | ⚠️ inchangé — **P2** (cross-machine) |
| `myia-qdrant:6333` (LAN) | root **200 open** | `/` **200**, `/collections` **200** | ⚠️ inchangé — **P2** (cross-machine) |

**Constat re-audit** :
- **P1 (gateway TTS publique) = FERMÉ**. Le binding Docker est passé de `0.0.0.0:8196`
  à `127.0.0.1:8196` (local-only) ET l'auth Bearer est désormais enforced (`401` sans
  token, à la fois côté Docker local et côté IIS public). La priorité de remédiation
  n°1 de l'audit initial est **résolue**.
- **Restant = 2 services LAN non authentifiés** (`claudish-proxy:3000`, `myia-qdrant:6333`),
  tous deux **consommateurs cross-machine** (P2) → gated coordination ai-01
  (cf. §5 + runbook `auth-flip-runbook.md`), inchangé depuis 2026-06-14.
- Les tables §2/§3 ci-dessous reflètent l'état **2026-06-14** (conservé pour la
  traçabilité) ; le présent §0 est la **source de vérité courante**.

---

## 1. Deux couches d'exposition (à ne pas confondre)

La surface d'attaque réelle se lit sur **deux plans distincts** :

1. **Bindings Docker hôte** — un conteneur publié sur `0.0.0.0:<port>` est joignable
   depuis tout le LAN ; sur `127.0.0.1:<port>` il n'est joignable que localement.
2. **Reverse-proxy IIS** (`*.myia.io`) — couche séparée qui réexpose certains ports
   locaux **sur Internet** (binding HTTPS wildcard `*.myia.io`). Un service en
   `127.0.0.1` côté Docker peut tout de même être public s'il est proxifié par IIS.

Un service n'est donc « interne » que s'il est **à la fois** en `127.0.0.1` côté
Docker **et** absent de la couche IIS.

---

## 2. Bindings Docker (état vérifié `docker ps`, 2026-06-14)

| Service | Binding | Portée | Auth sans token |
|---|---|---|---|
| `claudish-proxy` | `0.0.0.0:3000` | **LAN** | **HTTP 200 (ouvert)** |
| `myia-qdrant` | `0.0.0.0:6333-6334` | **LAN** | **HTTP 200 (ouvert)** |
| `tts-gateway` | `0.0.0.0:8196` | **LAN** | **HTTP 200 (ouvert)** |
| `comfyui-qwen` | `127.0.0.1:8188` | local | n/a (local) |
| `comfyui-video` | `127.0.0.1:8189` | local | n/a (local) |
| `fast-downward` | `127.0.0.1:8200` | local | n/a (local) |
| `forge-turbo` | `127.0.0.1:1111, :17861` | local | n/a (local) |
| `tts-api` (Kokoro) | `127.0.0.1:8191` | local | n/a (local) |
| `tts-fishaudio` | `127.0.0.1:8197` | local | n/a (local) |
| `whisper-api` | `127.0.0.1:8190` | local | n/a (local) |

**Constat n°1** : seuls **3 conteneurs** sont joignables depuis le LAN, et **les 3
répondent 200 sans token** (non authentifiés à ce jour).

---

## 3. Couche publique IIS (`*.myia.io`, sondes sans token)

| Domaine public | Backend | `/v1/models` sans token | État |
|---|---|---|---|
| `whisper-api.myia.io` | `whisper-api:8190` | **HTTP 401** | **sécurisé** ✓ |
| `tts-multi.myia.io` / `tts.myia.io` | `tts-gateway:8196` | **HTTP 200** | **ouvert** ✗ |
| `stt.myia.io` | `qwen-asr-api` | HTTP 404 (route absente) | à re-vérifier |

Mapping IIS confirmé dans
[setup-iis-reverse-proxy.ps1](../../docker-configurations/services/tts-multi/setup-iis-reverse-proxy.ps1)
: `tts-multi.myia.io` → `http://localhost:8196` (la gateway).

**Constat n°2 (le plus grave)** : la **gateway TTS est publique sur Internet via IIS
ET non authentifiée**. C'est la priorité de remédiation n°1.

---

## 4. Mécanisme d'authentification disponible (déjà codé)

Il existe un **middleware d'auth partagé** monté dans les conteneurs GenAI :
[auth_middleware.py](../../docker-configurations/services/shared/auth_middleware.py).

- Active le Bearer token si la variable d'env **`API_KEY`** est définie
  ([L40-L52](../../docker-configurations/services/shared/auth_middleware.py#L40)).
- `API_KEY` vide → **auth DÉSACTIVÉE** (avec warning). `AUTH_ENABLED=false` la
  désactive explicitement.
- Comparaison **timing-safe** (`secrets.compare_digest`), 401 si token absent/invalide.
- Chemins publics (sans auth) : `/health`, `/docs`, `/openapi.json`, `/redoc`, `/admin/*`.

**Conséquence** : pour la plupart des services audio, sécuriser = **définir une
variable d'env dans le `.env` gitignoré + redémarrer le conteneur**. Aucun
développement, action **réversible**.

### État du wiring par service

| Service | Middleware câblé | Variable d'env | Enforced ? |
|---|---|---|---|
| `whisper-api` | oui | `API_KEY` | **oui (401)** ✓ |
| `tts-gateway` | oui (monté `/app/shared`) | `TTS_GATEWAY_API_KEY` → `API_KEY` | **non (vide)** ✗ |
| `tts-api` (Kokoro) | oui (`setup_auth(app)`) | `API_KEY` | local-only |
| `qwen-asr-api` | oui | `API_KEY`, `TOKEN` | local-only |
| `musicgen-api` | oui | `API_KEY` | local-only |
| `demucs-api` | oui | `API_KEY` | local-only |
| `comfyui-qwen` / `comfyui-video` | **non** | — | local-only |
| `forge-turbo` / `sdnext` | **non** | — | local-only |
| `myia-qdrant` | n/a (auth native Qdrant) | `QDRANT__SERVICE__API_KEY` | **non** ✗ |
| `claudish-proxy` | à vérifier | — | **non** ✗ |

Gateway : `API_KEY=${TTS_GATEWAY_API_KEY:-}` dans
[docker-compose.yml:26](../../docker-configurations/services/tts-multi/docker-compose.yml#L26)
— le défaut **vide** est exactement la cause du trou.

---

## 5. Consommateurs cross-workspace (bloquent tout flip unilatéral)

Certains services exposés sont consommés par **d'autres machines / workspaces**.
Activer l'auth sans propager la clé **casse** ces consommateurs. À coordonner
**avant** tout flip :

| Service | Consommateurs | Risque si flip non coordonné |
|---|---|---|
| `myia-qdrant:6333` | **roo-state-manager (MCP, toutes machines)** | indexation cassée cluster-wide |
| `claudish-proxy:3000` | cluster (proxy) | cluster à l'arrêt |
| `whisper-api` (public) | NanoClaw, roo-extensions, myia-open-webui, **hermes-agent (dépôt PUBLIC)** | ASR cassé (déjà authentifié — ne pas **rotater** sans préavis) |
| `qwen-asr-api` / `stt.myia.io` | NanoClaw, roo-extensions | ASR 30-langues cassé |
| `tts-gateway` (public) | notebooks GenAI (via `qwen_tts_client`, lit déjà `TTS_GATEWAY_API_KEY`) | TTS cassé si `.env` notebooks non mis à jour |

> Mémoire opérationnelle : ne pas arrêter/roter `whisper-api` sans prévenir NanoClaw.

---

## 6. Plan de remédiation (séquencé par risque)

### P1 — Gateway TTS publique (lane GenAI, réversible) — **action user requise**

1. **[USER]** Ajouter `TTS_GATEWAY_API_KEY=<secret-fort>` au `.env` de la stack
   `tts-multi` (fichier gitignoré ; le hook `block-secrets.py` interdit l'édition
   par l'agent → édition manuelle user).
2. Propager la même clé dans `MyIA.AI.Notebooks/GenAI/.env` (var déjà lue par
   `qwen_tts_client._TTS_KEY`) — édition user également.
3. `docker compose -f docker-configurations/services/tts-multi/docker-compose.yml up -d`.
4. **Vérifier la preuve** : `curl …/v1/models` sans token → **401** ; avec
   `Authorization: Bearer <clé>` → **200**.

Réversible (vider la var + redémarrer). Endpoint **public** → confirmation user
avant flip (impacte `tts-multi.myia.io`).

### P2 — Cross-machine (NE PAS flipper seul, escalader ai-01)

- `myia-qdrant` : `QDRANT__SERVICE__API_KEY` → casse roo-state-manager sur **toutes**
  les machines. Nécessite propagation coordonnée de la clé dans la config MCP de
  chaque machine. **Décision cluster (ai-01)**, pas worker.
- `claudish-proxy` : proxy cluster → idem, coordination obligatoire.

> **Runbook opérationnel (P2)** : la procédure de flip détaillée, vérifiée contre
> le code source des 2 services, est dans [auth-flip-runbook.md](auth-flip-runbook.md).
> Greenlight ai-01 2026-06-14 : Claudish d'abord (auth déjà codée, blast contenu),
> puis Qdrant (blast cluster-wide, exige propagation `QDRANT_API_KEY` client avant
> le flip serveur).

### P3 — Défense en profondeur (priorité basse)

- Services image (`comfyui-qwen`, `comfyui-video`, `forge-turbo`, `sdnext`) : **aucun
  middleware d'auth**, mais **`127.0.0.1` local-only** → le binding EST déjà le
  contrôle. N'ajouter de l'auth que s'ils sont un jour exposés (IIS ou `0.0.0.0`).
- `stt.myia.io` 404 sur `/v1/models` : re-vérifier la route réelle exposée avant de
  conclure.

---

## 7. Synthèse

> **MAJ 2026-07-08 (cf. §0)** : l'état ci-dessous est celui de l'audit initial
> (2026-06-14). Le re-audit live confirme que **P1 (gateway TTS publique) est FERMÉ**
> (`tts-gateway` passé en `127.0.0.1` local + auth `401` enforced, public IIS `401`).
> Restant actif = `claudish:3000` + `qdrant:6333` (P2, cross-machine, inchangés).

- **3 services LAN exposés non authentifiés** : `tts-gateway:8196`, `qdrant:6333`,
  `claudish:3000`.
- **1 trou public Internet** : `tts-multi.myia.io` (gateway TTS) répond 200 sans token.
- **Le mécanisme d'auth existe déjà** (`auth_middleware.py`) — sécuriser la gateway =
  variable d'env + restart, **sans code**, **réversible**.
- **qdrant + claudish = cross-machine** → coordination ai-01 obligatoire avant flip.
- **`whisper-api` déjà sécurisé** (401) — modèle à répliquer ; ne pas rotater sans
  préavis NanoClaw.

**Bloqueur user** : le secret de la clé gateway doit être saisi **manuellement** dans
les `.env` gitignorés (hook `block-secrets.py` interdit l'édition agent). Voir P1.
