# Hermes — Guide de Deploiement (s6-overlay)

[← Claw-Systems](../README.md) | [↑ ..](../README.md)

Ce guide documente le deploiement production d'Hermes comme conteneur Docker
long-running avec **s6-overlay** en PID 1. Hermes tourne ainsi 24/7, survive aux
redemarrages, et expose le bot Telegram + les jobs cron.

> Le contexte : Hermes tourne sur une machine Windows 11 avec Docker Desktop.
> Les patches notes ci-dessous (section [Patches Windows](#3-patches-windows-obligatoires))
> existent precisement a cause de cette combinaison Windows + s6-overlay.

## Prerequis

| Outil | Version | Usage |
|-------|---------|-------|
| Docker Desktop | recente | Runtime conteneur |
| PowerShell | 5.1+ | Lancement `docker run` (PAS Git Bash — la conversion de chemins casse les `-v`) |
| git | recent | Cloner le fork |

### Tokens requis

1. **Telegram Bot Token** — via [@BotFather](https://t.me/BotFather)
2. **GLM / z.ai API key** — cle provider LLM natif
3. **GitHub CLI token** (`gh auth`) — pour les jobs pr-review
4. **MCP auth bearer** — token du proxy MCP LAN
5. **Whisper bearer** — pour le STT cluster (optionnel)

Aucun token ne doit etre commité. Voir
[hermes.env.secrets.example](../configs/hermes.env.secrets.example).

## Conteneur

| Element | Valeur |
|----------|--------|
| **Image** | `hermes-agent:s6-20260528` (build local depuis le fork) |
| **PID 1** | `s6-svscan` (s6-overlay v3.2.3.0, remplace tini/gosu) |
| **Utilisateur** | `hermes` (UID 10000) via `s6-setuidgid` |
| **Volume** | `<home>/.hermes` → `/opt/data` (persistant entre rebuilds) |
| **Port** | `-p 9120:9119` (host 9120 → container 9119 dashboard) |

## Lancement (production)

```powershell
docker run -d --name hermes `
  --restart unless-stopped `
  -v C:\Users\<user>\.hermes:/opt/data `
  -v C:\dev\roo-extensions\mcps\internal\servers\roo-state-manager:/opt/roo-state-manager:ro `
  --add-host=host.docker.internal:host-gateway `
  -p 9120:9119 `
  hermes-agent:s6-20260528 gateway run
```

Le script complet et commenté vit dans
[`configs/docker-run-hermes.ps1.example`](../configs/docker-run-hermes.ps1.example).

> **Pas de `-e` :** tous les secrets proviennent de `/opt/data/.env.secrets`,
> charge par le script de restore au demarrage. Ne JAMAIS passer un token en
> flag `docker run -e` — il fuiterait dans l'historique des processus.

## Séquence de boot (s6-overlay, Architecture B)

```
/init (s6-svscan, PID 1)
  ├── s6-rc-compile bundle (oneshot-runner, fix-attrs)
  ├── cont-init.d/ (ordre lexicographique) :
  │   ├── 01-hermes-setup       ← stage2-hook.sh : sync des skills bundlees
  │   ├── 013-roosync-restore   ← NOTRE SHIM : invoque /opt/data/restore-config.sh
  │   ├── 015-supervise-perms   ← chown des arbres supervise/
  │   └── 02-reconcile-profiles ← enregistre le profil par defaut
  ├── services s6-rc :
  │   ├── main-hermes  ← wrapper CMD (main-wrapper.sh)
  │   └── dashboard    ← serveur dashboard web
  └── CMD = main-wrapper.sh
      └── exec s6-setuidgid hermes hermes gateway run
```

Le shim `013-roosync-restore` est le point d'injection cluster : il appelle
`/opt/data/restore-config.sh` a **chaque** demarrage conteneur, ce qui rend la
configuration idempotente et reproductible.

## Script de restore

`roosync-cluster/scripts/hermes-restore-config.sh` est copié vers
`/opt/data/restore-config.sh` sur le volume persistant. Il reconstruit la
configuration a partir des secrets a chaque boot, dans cet ordre :

1. Charge les secrets depuis `/opt/data/.env.secrets`
2. Positionne le modele (`glm-5.2`) et le provider (`zai`)
3. Supprime la contamination `provider: "auto"` et `base_url` OpenRouter
4. Ajoute la config de deploiement RooSync (providers auxiliaires, STT, MCPs, approvals)
5. **Auto-detection MCP** : sonde le proxy LAN (port 9090). Si injoignable, active le fallback local
6. Ecrit `/opt/data/.env` avec tous les tokens
7. Corrige le format `jobs.json` (list→dict, normalisation, retrait des restrictions de toolsets)
8. Installe `croniter`, `gh` CLI, `jq`
9. Configure `gh auth` (persisté dans `/opt/data/.config/gh`)
10. Patch le `SCHEMA_SQL` du kanban (index session_id avant migration)
11. Lance les verifications (PASS/FAIL)

## Fallback MCP local (quand le proxy LAN est down)

Quand le proxy MCP LAN (port 9090) est injoignable, le script active une
infrastructure MCP locale :

| Serveur | Transport | Detail |
|---------|-----------|--------|
| `roo-state-manager` | stdio direct | Volume-monté depuis roo-extensions, `.env` patché (GDrive/Qdrant désactivés), `index.js` patché (FATAL → degrade) |
| `sk-agent` | mcp-remote via proxy | `host.docker.internal:9092/sk-agent/mcp` |
| `searxng` | mcp-remote via proxy | `host.docker.internal:9092/searxng/mcp` |

**Conteneur proxy local :** `myia-mcp-proxy` (proxy Go, port 9092).

> **Regle d'or :** le script copie `/opt/roo-state-manager` vers `/tmp/` puis
> patche **la copie uniquement**. Le volume host n'est **jamais** touché
> (regression #560 — corruption du `.env` host). Le montage roo-state-manager
> est `ro` (read-only) pour la meme raison.

## 3 patches Windows (obligatoires)

Ces patches existent a cause de la combinaison checkout Windows (CRLF) +
isolation d'env s6-overlay (cassee l'heritage Docker ENV). **A ré-appliquer
apres chaque sync upstream.**

1. **Strip CRLF** — le Dockerfile ajoute `RUN find /etc/s6-overlay/s6-rc.d -type f -exec sed -i 's/\r$//' {} +` (et idem pour `/etc/cont-init.d`) apres chaque bloc `COPY`. Sans cela, `s6-rc-compile` echoue avec "invalid type".

2. **Shebang `#!/command/with-contenv sh`** sur `docker/main-wrapper.sh`. Sans cela, le CMD tourne avec seulement ~6 variables d'env (PATH, PWD...) — les `ENV` du Dockerfile et les `-e` du `docker run` **ne sont pas herités**. `with-contenv` charge depuis `/run/s6/container_environment/`.

3. **`export HOME="/opt/data"`** dans `main-wrapper.sh`. `with-contenv` injecte `HOME=/root` depuis l'env Docker, mais `s6-setuidgid hermes` ne peut pas ecrire dans `/root/`. Il faut overrider avant le `exec`.

## Drift Dockerfile (nos ajouts vs upstream)

Les **seules** lignes ajoutées au Dockerfile upstream :

```dockerfile
# Apres COPY docker/s6-rc.d/ :
RUN find /etc/s6-overlay/s6-rc.d -type f -exec sed -i 's/\r$//' {} +

# Apres COPY docker/cont-init.d/* :
COPY --chmod=0755 docker/cont-init.d/013-roosync-restore /etc/cont-init.d/013-roosync-restore
RUN find /etc/cont-init.d -type f -exec sed -i 's/\r$//' {} +
```

Plus les modifs de `docker/main-wrapper.sh` (shebang + override HOME — patches #2 et #3 ci-dessus).

## Contenu du volume persistant (survit aux rebuilds)

| Chemin | Contenu |
|--------|---------|
| `state.db` | Base de sessions SQLite |
| `sessions/` | Historique des conversations |
| `skills/` | Skills personnalisés |
| `memories/` | Mémoires de l'agent |
| `config.yaml` | Config complète (restaurée par le script) |
| `.env` | Tokens (régénérés par le script) |
| `.env.secrets` | Valeurs secrètes pour le script |
| `SOUL.md` | Personnalité de l'agent |
| `cron/jobs.json` | Jobs planifiés |
| `.config/gh/` | Auth GitHub CLI |
| `restore-config.sh` | Copie du script de restore |

**Non persistant** (réinstallé par le script a chaque boot) : `gh` CLI, `jq`, `croniter`, patch kanban.

## Provider z.ai (CRITIQUE)

Utiliser le **z.ai natif** (`provider: "zai"`, endpoint intégré
`/api/coding/paas/v4`). **NE JAMAIS** utiliser
`ANTHROPIC_BASE_URL=https://api.z.ai/api/anthropic` — la couche de compat
Anthropic perd le registre d'outils MCP apres compaction.

```yaml
auxiliary:
  compression:
    provider: "zai"
    model: "glm-4.5-air"
```

Surveiller les `tool_use_error` apres compaction — redémarrer la session si observé.

## Résilience MCP (watchdog)

**Cause racine :** `MCPServerTask.run()` dans `tools/mcp_tool.py` abandonne apres
`_MAX_RECONNECT_RETRIES = 5` tentatives. Une fois la tâche retournée, le pont est
mort jusqu'au redémarrage du process gateway.

**Watchdog :** `roosync-cluster/scripts/hermes-mcp-watchdog.ps1` tourne toutes
les 15 min via une tâche planifiée Windows. Escalade de récupération :

1. **Stage 1 :** `SIGUSR1` au PID gateway — redémarrage graceful, préserve l'état conteneur
2. **Stage 2 :** `docker restart` — reboot complet (dernier recours)

**Backoff :** exponentiel (5, 10, 15... jusqu'à 60 min). Max 10 échecs consécutifs
avant abandon. Le compteur reset sur check sain. Evite les loops de restart
(incident 2026-05-11 : 10+ restarts en 4h).

## Backup

**Auto :** le cont-init.d `012-roosync-backup` snapshot les fichiers critiques a
chaque boot (avant restore). Stocké dans `/opt/data/backups/auto-YYYYMMDD-HHmmss.tar.gz`
(max 3 rotatés, ~20 MB chacun).

**Manuel pré-rebuild :**

```powershell
.\roosync-cluster\scripts\hermes-backup.ps1 -Reason "description"
```

Stoppe le conteneur, tar le volume complet vers `C:\Users\<user>\hermes-backups\`,
redémarre. Garde les 5 derniers.

**Vérification post-op :**

```powershell
.\roosync-cluster\scripts\hermes-verify.ps1
```

12 checks : process gateway, Telegram connecté, symlinks config/env, modele, MCPs,
cron jobs, kanban inscriptible, gh auth, santé MCP.

## Rollback

Si la nouvelle image casse, restaurer l'image précédente :

```powershell
docker stop hermes
docker rm hermes
docker run -d --name hermes `
  --restart unless-stopped `
  -v C:\Users\<user>\.hermes:/opt/data `
  -v C:\dev\roo-extensions\mcps\internal\servers\roo-state-manager:/opt/roo-state-manager:ro `
  --add-host=host.docker.internal:host-gateway `
  -p 9120:9119 `
  hermes-agent:pre-sync-20260602 gateway run
```

## Troubleshooting

| Symptôme | Cause probable | Resolution |
|----------|----------------|------------|
| `s6-rc-compile: invalid type` | CRLF non strippé | Vérifier patch #1 (strip CRLF) |
| CMD tourne avec ~6 vars d'env | Shebang sans `with-contenv` | Vérifier patch #2 |
| `PermissionError: /root/...` | HOME non overriddé | Vérifier patch #3 (`export HOME=/opt/data`) |
| `tool_use_error` apres compaction | Compat Anthropic + MCP | Forcer `provider: zai`, redémarrer session |
| MCP mort apres quelques heures | Limite 5 retries | Vérifier le watchdog (SIGUSR1) |
| MCPs down si proxy LAN injoignable | Proxy 9090 down | Le fallback local doit prendre le relais |

## Liens

- [Architecture Hermes](05-Hermes-Architecture.md)
- [Hermes Coordinateur de Cluster](07-Hermes-Cluster-Coordinator-Role.md)
- Configs : [docker-run-hermes.ps1.example](../configs/docker-run-hermes.ps1.example), [hermes.env.secrets.example](../configs/hermes.env.secrets.example)
