# Secrets management — central source of truth

**Objectif :** une gestion propre et durable de TOUS les secrets de l'infrastructure GenAI / CoursIA, pour que le drift (un secret édité à un endroit mais pas ailleurs) soit mécaniquement impossible.

## Architecture — `.secrets/master.env` + render

```
.secrets/master.env                    <- SOURCE UNIQUE (éditer ici)
   HF_TOKEN, OPENAI_API_KEY, COMFYUI_VIDEO_TOKEN, QDRANT_API_KEY, ... (19 clés partagées)

scripts/secrets/render_envs.py
   --bootstrap   one-shot : lit les .env éparpillés, écrit master.env
   (défaut)      sync     : propage master.env -> chaque .env (15 cibles)
   --check       gate     : exit 1 si un .env drift de master (audit local)

docker-configurations/services/*/.env  <- CONFIG service (ports, paths, GPU)
MyIA.AI.Notebooks/GenAI/.env           <- CONFIG notebooks + secrets synchronisés
```

**Principe :** `master.env` ne contient que les secrets **partagés** (un consommateur ≠, une valeur commune). La CONFIG service-spécifique (ports, chemins, GPU ids, noms de modèles, `TZ`) reste dans chaque `.env` et n'est **jamais** touchée par le render. Les mots de passe **par instance** (chaque ComfyUI / Forge a le sien) ne sont PAS centralisés — voir §"Secrets par instance".

## Rotation d'un secret (procédure canonique)

```bash
# 1. Éditer la source unique
$EDITOR .secrets/master.env          # ex: changer HF_TOKEN

# 2. Propager vers tous les .env consommateurs
python scripts/secrets/render_envs.py

# 3. Redémarrer les containers impactés (OBLIGATOIRE pour ComfyUI-Login,
#    voir §"Règle du restart ComfyUI" ci-dessous)
docker compose -f docker-configurations/services/<svc>/docker-compose.yml restart
```

Le render est **idempotent** : re-lancer ne change rien si déjà synchronisé.

## Audit / détection de drift

```bash
python scripts/secrets/render_envs.py --check
# exit 0 = tous les .env synchronisés avec master
# exit 1 = drift détéré (un .env a été édité à la main), affiche chaque écart
```

`--check` compare chaque clé secrète de chaque `.env` à `master.env`. À lancer après toute édition manuelle d'un `.env`, ou périodiquement. **Note :** c'est un outil **local** (les `.env` sont gitignored, donc absents d'un checkout CI frais) — le scanner d'inline-literals côté code committé reste gitleaks CI (cf [secrets-hygiene.md](../../.claude/rules/secrets-hygiene.md)).

## Inventaire des secrets centralisés (master.env)

| Catégorie | Clés | Consommateurs | Sensible rotation |
|-----------|------|---------------|-------------------|
| Hugging Face (aliasé) | `HF_TOKEN` = `HUGGINGFACE_TOKEN` | 5 services + notebooks | Oui (gated/quotas) |
| LLM APIs payantes | `OPENAI_API_KEY`, `ANTHROPIC_API_KEY`, `OPENROUTER_API_KEY` | notebooks | Oui (facturation) |
| Hubs / git | `CIVITAI_TOKEN`, `GITHUB_TOKEN` = `GITHUB_ACCESS_TOKEN` | services + notebooks | Oui |
| Client API keys (server↔client) | `WHISPER_API_KEY`, `VLLM_API_KEY`, `TTS_API_KEY`, `QWEN_ASR_API_KEY`, `MUSICGEN_API_KEY`, `DEMUCS_API_KEY`, `FUNASR_API_KEY` | 1 service + notebooks | Moyen |
| Qdrant vector DB (client) | `QDRANT_API_KEY` | notebooks RAG / SemanticKernel / Argument_Analysis | Moyen (flip serveur = op inter-repo roo-extensions) |
| Tokens client ComfyUI | `COMFYUI_VIDEO_TOKEN`, `COMFYUI_API_TOKEN` | notebooks → services ComfyUI | Moyen |
| Session | `SECRET_KEY` | 1 service | Oui |

**Alias :** `HF_TOKEN`/`HUGGINGFACE_TOKEN` et `GITHUB_TOKEN`/`GITHUB_ACCESS_TOKEN` désignent le MÊME secret sous deux noms (services vs notebooks). Le render écrit la même valeur des deux côtés ; le bootstrap vérifie leur cohérence (abort si divergence).

### Qdrant — convention client vs serveur (cross-repo)

Qdrant expose la **même** clé API sous **deux noms** selon le côté :

- **Serveur** Qdrant — `QDRANT__SERVICE__API_KEY` (double underscore, convention `config.yaml` Qdrant). Vit dans la compose `roo-extensions` (autre repo). **Non centralisé** ici : le flip de valeur est une op inter-repo manuelle.
- **Client** (notebooks CoursIA) — `QDRANT_API_KEY` (simple underscore, convention des clients `qdrant-client`). Vit dans `MyIA.AI.Notebooks/GenAI/.env`. **Centralisé** dans `SECRET_KEYS` (render_envs.py).

Les deux noms **doivent porter la même valeur** (sinon 401 côté client). Centraliser le côté client CoursIA permet aux notebooks de suivre la rotation sans action manuelle : `edit master.env → render_envs.py` propage vers `GenAI/.env`. Le **flip de la valeur côté serveur** (rotation effective, Qdrant redémarre avec la nouvelle clé) reste une opération manuelle inter-repo sur `roo-extensions` — tracker séparément, cf [SECURITY.md](../../docker-configurations/SECURITY.md).

## Secrets par instance (NON centralisés — config service)

Ces secrets sont légitimement **différents par instance** (un mot de passe par container). Ils restent dans le `.env` de leur service et ne sont jamais collapsés :

| Secret | Instances | Pourquoi par-instance |
|--------|-----------|----------------------|
| `COMFYUI_PASSWORD`, `COMFYUI_USERNAME` | comfyui-qwen, comfyui-video | Chaque ComfyUI a son propre login |
| `FORGE_PASSWORD`, `FORGE_USER` | forge-turbo, sd-forge-main | Chaque Forge a son propre login |
| `WHISPER_PASSWORD`/`WHISPER_USER`, `WHISPER_WEBUI_PASSWORD`/`WHISPER_WEBUI_USER` | whisper-api, whisper-webui | Logins par instance |

Leur **prévention du drift** = la règle du restart (ci-dessous) + le self-check entrypoint, PAS la centralisation.

## Règle du restart ComfyUI-Login (le piège du drift)

`ComfyUI-Login` stocke un **hash bcrypt** dans `workspace/login/PASSWORD` (bind-mount persistant). L'`entrypoint.sh` **régénère ce hash depuis `COMFYUI_PASSWORD` (env) à chaque démarrage du container** — mais **pas pendant qu'il tourne**.

Conséquence : si tu changes `COMFYUI_PASSWORD` dans le `.env` **sans restart**, le container garde un hash **périmé** jusqu'au prochain restart. Un client qui s'authentifie avec le nouveau mot de passe obtient un 401 — exactement le symptôme qui a fait croire (à tort) à une "clé perdue".

**Règle :** après tout changement de `COMFYUI_PASSWORD` (ou `COMFYUI_*_TOKEN`), `docker compose restart` le container concerné. Le render affiche un rappel.

**Self-check entrypoint :** après écriture du hash, l'entrypoint vérifie `bcrypt.checkpw(COMFYUI_PASSWORD, hash)` et logge la confirmation — donc les logs de démarrage prouvent que le hash du container courant matche le `.env` au startup.

## Incident fondateur (juin 2026)

Diagnostic erroné "drift bcrypt / plaintext perdu" sur `comfyui-video` → demande user de reset. **Vérification re-faite :** `bcrypt.checkpw(.env_password, hash) == True` — la clé n'était JAMAIS perdue. Le container avait simplement été vérifié avant son restart (hash périmé en RAM), puis restarté (hash régénéré depuis le `.env` courant). Leçon G.1/G.9 : un verdict "clé perdue" doit être vérifié **après restart**, pas sur un container au hash potentiellement périmé. Cet épisode a motivé la centralisation ci-dessus.

## À faire (phase 2, optionnel)

- Brancher `render_envs.py --check` en pre-commit local (hook `pre-commit`, pas CI — `.env` absents du checkout CI).
- Documenter la rotation `WHISPER_API_KEY` (le token du reverse-proxy IIS `whisper-api.myia.io`) dans la procédure — actuellement dans `docker-configurations/services/whisper-api/.env` + propagation cross-repos (cf mémoire `whisper-token-rotation.md`).
- Étendre `master.env` aux tokens cross-repos (roo-extensions, hermes-agent) via un master partagé si besoin.

## Voir aussi

- [.claude/rules/secrets-hygiene.md](../../.claude/rules/secrets-hygiene.md) — anti-patterns inline-literals, règle HARD content-based.
- [docs/reference/secrets-and-coord-detail.md](../reference/secrets-and-coord-detail.md) — incidents + postmortem responsable.
- [scripts/secrets/render_envs.py](../../scripts/secrets/render_envs.py) — l'outil (`--bootstrap` / sync / `--check`).
