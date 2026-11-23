# FishAudio S2-Pro TTS Service

Expressive TTS with 15000+ prosodic tags, Dual-AR architecture (Slow 4B + Fast 400M), 80+ languages.

## Requirements

- NVIDIA GPU with 24GB VRAM (RTX 3090+)
- Docker + NVIDIA Container Toolkit
- HuggingFace token (for model download)

## Setup

```bash
# 1. Copy configuration
cp .env.example .env
# Edit .env with your HuggingFace token

# 2. Download model (~11GB safetensors, official snapshot)
docker run --rm -v $(pwd)/checkpoints:/app/checkpoints \
  -e HF_TOKEN=your_token \
  fishaudio/fish-speech:latest \
  python -c "from huggingface_hub import snapshot_download; snapshot_download('fishaudio/s2-pro', local_dir='/app/checkpoints/s2-pro')"

# 3. Start service
docker compose up -d

# 4. Verify
curl http://localhost:8197/v1/health
```

## API Usage

### Generate speech

```python
import requests

response = requests.post("http://localhost:8197/v1/tts", json={
    "text": "[whisper] Bonjour tout le monde",
    "reference_id": None,  # Optional: speaker reference
})

with open("output.wav", "wb") as f:
    f.write(response.content)
```

### With voice reference

```python
response = requests.post("http://localhost:8197/v1/tts", json={
    "text": "[shout] Jamais ! cria-t-elle.",
    "reference_id": "narrator_male",  # From references/ directory
})
```

## Expressive Tags

FishAudio S2-Pro supports inline tags in text:
- `[whisper]`, `[shout]`, `[laugh]`, `[pause]`, `[breath]`
- `[cold]`, `[timid]`, `[indignant]`, `[onctuous]`
- `[professional broadcast tone]`, `[slow]`, `[fast]`
- 15000+ tags for fine-grained prosody control

## VRAM Management

Mesures du 2026-10-29 sur la RTX 3090 (24 Go) de `po-2023` :

| Poids | VRAM | Source |
|---|---|---|
| fp16 (`--half`, la configuration du compose) | **~20,3 Go** | warm-up mesuré le 2026-10-06 |
| NF4 quantifié | **5,0 Go de fichiers**, cible annoncée « 12 Go+ » | `groxaxo/s2-pro-BnB-4Bits` |

Le `--half` du compose n'aboutit donc pas au « ~12 Go » annoncé auparavant : le service occupe ~20,3 Go, soit la quasi-totalité d'une carte de 24 Go et aucune carte de 16 Go. Arrêter `tts-qwen` ne libère pas 12 Go.

### Checkpoints quantifiés existants

Tailles mesurées via l'API HuggingFace (`?blobs=true`) :

| Dérivé | Total | Remarque |
|---|---|---|
| `groxaxo/s2-pro-BnB-4Bits` | 5,00 Go | NF4 — **exige le fork**, voir ci-dessous |
| `scarxity/fish-speech-s2-pro-nf4` | 5,00 Go | NF4 |
| `baicai1145/s2-pro-w4a16` | 6,13 Go | safetensors |
| `drbaph/s2-pro-fp8` | 8,05 Go | fp8 |

**Piège vérifié** : ajouter `bitsandbytes` et `accelerate` à l'image officielle ne suffit pas. Les deux paquets y sont absents (`ModuleNotFoundError` sur chacun), mais surtout le loader officiel construit des couches fp16 et ne sait pas lire un state dict préquantifié — le model card le dit explicitement : « not a legacy int4 or int8 export », « meant to be loaded through the fork's `bnb4` path ». Il faut `groxaxo/fish-speech-int4-patch`, dont `tools/api_server.py` transmet `bnb4=self.args.bnb4`.

### Sleep

Le sidecar `idle-monitor` **arrête** le conteneur, il ne l'endort pas : au redémarrage, les ~20 Go sont rechargés. Pour un usage ponctuel, c'est ce régime qu'il faut remplacer (cf [la politique d'hébergement et le sleep](../../../docs/genai/genai-services.md), § « Politique d'hébergement — le plus petit quant, et le sleep »).

## Variante int4

Le compose canonique ci-dessus est la route fp16 (`--half`, ~20,3 Go). La **variante int4** est le mode qui héberge en pratique sur la RTX 3090 partagée : checkpoint quantifié int4 weight-only (route amont `tools/llama/quantize.py`, cf `quantize_int4.py`) servi par `serve_int4.py`, **sans** `--half` (le noyau int4 exige que les buffers `scales_and_zeros` restent bfloat16 ; `--half` les passerait en float16 et produirait du garbage). Elle vit dans `docker-compose.int4.yml`.

### Pourquoi le conteneur crash-loopait, et le correctif bf16

`from_pretrained` (dans `tools/llama.py`) instancie le modèle **full-size en RAM, sous le dtype fp32 par défaut, AVANT** d'appliquer la conversion int4. Le pic de chargement est donc celui du modèle fp32, pas de l'int4 :

| Phase | Pic RAM mesuré |
|---|---|
| init en fp32 (sans correctif) | **14 120 MiB** |
| init en bf16 (`set_default_dtype(bfloat16)` autour de `init_model`) | **10 352 MiB** |

> Le **10 352 MiB** du tableau est la probe d'init bf16 isolée ; le **10 536 MiB** cité dans `docker-compose.int4.yml` est le pic de chargement complet mesuré sous la borne 12 g. Ce sont deux mesures distinctes (probe isolée vs chargement sous borne) — d'où l'écart de 184 MiB entre les deux chiffres, et non une incohérence.

Avec le pic fp32 à 14 120 MiB, **toute** borne mémoire de 6 g / 8 g / 12 g / 14 g tue le démarrage : le conteneur est OOM-killé (exit 137) toutes les ~30 s (`docker events` : `oom` + `die` en boucle, RestartCount dans les milliers). Le service ne survivait avant #303 que parce qu'il n'avait **aucune** borne.

Le correctif, porté dans `serve_int4.py` : `torch.set_default_dtype(torch.bfloat16)` autour de l'appel `init_model`, restauré en `finally`. Ça divise le pic (14 120 → 10 352 MiB) **sans changer le modèle servi** : le `load_state_dict(assign=True)` final remplace tous les tenseurs par ceux du checkpoint int4, le dtype d'init n'a d'effet que sur le transitoire de chargement. Après correctif, sous une borne 12 g : poids « All keys matched successfully », `/v1/health` 200, chargement ~3,5 min ; l'état stationnaire reste ~2,8-3 GiB, swap désactivé.

### Démarrer la variante

```bash
# .env : LLAMA_CHECKPOINT_PATH=checkpoints/fs-1.2-int4-g128-<timestamp>
docker compose -f docker-compose.int4.yml up -d
curl http://localhost:8197/v1/health
```

La borne de 12 g (swap off, pids 256) est la plus petite borne qui survit au transitoire une fois l'init passé en bf16.

## Integration

This service integrates with the audiobook pipeline (`04-6-Audiobook-Pipeline.ipynb`) as P4 TTS engine, providing expressive tag support that Kokoro cannot leverage.

Port: 8197 | GPU: 1 (RTX 3090) | Network: host (tts-network bridge optional)
