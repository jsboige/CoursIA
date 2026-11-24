# Pile d'apprentissage CoursIA

Pli 1.5 de l'Epic [#27543](../../../../issues/27543) — issue [#27548](../../../../issues/27548).
Un `docker-compose` qui démarre l'image d'apprentissage du pli 1.2
([notebook-runner](../notebook-runner/), cible `learning` : JupyterLab, les 7
noyaux canoniques) et, **à la demande**, les services dont les carnets ont
besoin. Le patron d'un service propre est
[services/planners-fast-downward](../services/planners-fast-downward/) :
image nommée, API REST, port en boucle locale, `healthcheck`, volume de
données.

## Démarrage

```bash
cd docker-configurations/learning

# Pile de base : JupyterLab sur http://localhost:8888
# (jeton : docker compose logs learning | grep -o 'token=[a-z0-9]*')
docker compose up -d

# Pile + planificateur (CPU) :
docker compose --profile planners up -d
```

Le conteneur de la pile s'appelle `coursia-learning-pile` : le compose
[notebook-runner](../notebook-runner/) définit lui aussi un service
`learning` (conteneur `coursia-learning`, même image). La définition de **cette
pile** fait foi pour l'apprentissage (boucle locale, healthcheck, profils) ;
les noms distincts évitent la collision de conteneurs, mais les deux services
bindent le port 8888 — remapper avec `LEARNING_PORT` si les deux tournent.

Les carnets Python de Planners appellent Fast Downward via
[`fast_downward_backend.py`](../../MyIA.AI.Notebooks/SymbolicAI/Planners/fast_downward_backend.py) :
le service Docker d'abord (`FAST_DOWNWARD_URL`, par défaut
`http://fast-downward:8200` dans la pile, `http://localhost:8200` hors pile),
le paquet `up-fast-downward` en repli. Avec le profil `planners` actif, le
carnet exécuté dans JupyterLab atteint le service par le nom Docker, sans
aucune configuration.

Les variables optionnelles (ports, fuseau, URL du planificateur) vivent dans
[`.env.example`](.env.example) — aucune n'est un secret ; le jeton Jupyter est
généré par le conteneur et se lit dans les logs.

Sur un hôte qui fait déjà tourner le service `planners-fast-downward`
standalone (port 8200 occupé), remapper le port hôte —
`PLANNER_PORT=8201 docker compose --profile planners up -d` : le chemin
in-stack passe par le nom de service sur le réseau Docker, pas par le port
hôte, donc les carnets de la pile ne sont pas affectés.

## Services CPU et services GPU — table mesurée

Le discriminant est **mesuré sur les compose du dépôt** (tête de branche) :
un service est classé GPU si son compose réserve un device nvidia
(`deploy.resources.reservations.devices`), CPU sinon. Rejouer la mesure :

```bash
python - <<'PY'
import yaml, glob, os
for f in sorted(glob.glob('docker-configurations/services/*/docker-compose*.yml')):
    d = yaml.safe_load(open(f, encoding='utf-8')) or {}
    for name, svc in (d.get('services') or {}).items():
        dev = ((svc.get('deploy') or {}).get('resources') or {}) \
            .get('reservations', {}).get('devices') or []
        print(f"{name}: {'GPU' if dev or svc.get('gpus') else 'CPU'}")
PY
```

Les consommateurs sont mesurés par `grep -rlE "localhost:PORT"` sur
`MyIA.AI.Notebooks/`.

| Service | Port hôte | CPU / GPU | Carnets consommateurs |
| --- | --- | --- | --- |
| [planners-fast-downward](../services/planners-fast-downward/) | 8200 | **CPU** | Planners-01-Introduction-Csharp, Planners-04-Fast-Downward-Python, Planners-13-Mesure-Qualite-Plans-Python (via `fast_downward_backend.py`) |
| orchestrator (passerelle) | 8090 | CPU (ses services modèles sont GPU) | aucun carnet direct mesuré |
| tts-gateway ([tts-multi](../services/tts-multi/)) | 8196 | CPU (ses backends kokoro/tada/qwen sont GPU) | GenAI Audio 02-5-Multi-Model-TTS-Gateway, 04-7-TTS-Voice-Benchmark |
| [comfyui-qwen](../services/comfyui-qwen/) | 8188 | GPU | GenAI 00-1-Environment-Setup, 00-5-ComfyUI-Local-Test |
| [comfyui-video](../services/comfyui-video/) | 8189 | GPU | GenAI 00-1, Video 02-3-Wan-Video-Generation |
| orchestrator : flux-1-dev / stable-diffusion-35 / comfyui-workflows | 8189 / 8190 / 8191 | GPU | via la passerelle orchestrator |
| [whisper-api](../services/whisper-api/) | 8190 | GPU | GenAI 00-1, Audio 04-13-Audiobook-FishAudio-S2Pro |
| [tts-api](../services/tts-api/) (kokoro) | 8191 | GPU | Audio 04-10-Annotation-Prosodique, 04-11-Generation-TTS |
| [musicgen-api](../services/musicgen-api/) | 8192 | GPU | aucun consommateur mesuré |
| [demucs-api](../services/demucs-api/) | 8193 | GPU | aucun consommateur mesuré |
| [funasr-api](../services/funasr-api/) | 8194 | GPU | aucun consommateur mesuré |
| [qwen-asr-api](../services/qwen-asr-api/) | 8195 | GPU | aucun consommateur mesuré |
| tts-multi : backends kokoro / tada / qwen | — | GPU | via tts-gateway (8196) |
| [tts-fishaudio](../services/tts-fishaudio/) | 8197 | GPU | Audio 02-8-Expressive-TTS, 04-10-Annotation-Prosodique |
| [sd-forge](../services/sd-forge/) | 7860 | GPU | Image 01-4-Generation-Image-Locale-Forge, Aspire 02-Aspire-GenAiStack-Reel |
| [sdnext](../services/sdnext/) | 7861 | GPU | aucun consommateur mesuré |
| [sd-forge-main](../services/sd-forge-main/) | 7862 | GPU | aucun consommateur mesuré |
| [vllm-zimage](../services/vllm-zimage/) | 8001 | GPU | GenAI 00-6-Local-Docker-Deployment, MCP-Server consommer-vs-exposer-le-mcp |
| [whisper-webui](../services/whisper-webui/) | 36540 | GPU | aucun consommateur mesuré |

Les variantes `-hybrid` (whisper-api, tts-api, musicgen-api, demucs-api)
demandent elles aussi un device nvidia (`WHISPER_DEVICE=cuda`, etc.) : elles
restent GPU. Les `idle-monitor` sont des sidecars CPU, pas des services
d'apprentissage.

**Seul `planners-fast-downward` est câblé dans cette pile** : parmi les
services CPU du tableau, c'est le seul dont la chaîne complète — service et
carnets consommateurs — se sert sans GPU. `tts-gateway` est bien classé CPU
(aucun device réservé) mais ses backends kokoro/tada/qwen réservent un device
nvidia (mesuré dans le compose `tts-multi`) : ses carnets consommateurs
exigent une machine GPU, il n'a pas sa place dans cette pile. Les services GPU
se lancent depuis leur dossier `services/<nom>/` sur une machine GPU ; leurs
carnets consommateurs sont listés ci-dessus.
