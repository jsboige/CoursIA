# Quant le plus petit + sleep — pour tous nos modèles auto-hébergés

S'applique à **tout service qui charge un modèle sur un GPU** de la flotte (ComfyUI/Qwen, vLLM, Whisper, FishAudio, pile TTS, embeddings, vidéo). Source : mandat user direct du 2026-10-29 (séance EPF APP3), énoncé en deux temps puis élargi : « la consigne est d'héberger nos modèles avec les quants les plus petits, int8 ou int4 si possible, pour faire de la place », « les modèles doivent passer en sleep quand ils ne sont pas utilisés », puis « on fait ça pour tous nos modèles ».

Le but est explicite et il est le critère d'arbitrage : **récupérer de la capacité GPU**, pas maximiser la fidélité d'un service.

## Règle HARD 1 — le plus petit quant disponible, y compris communautaire

Un modèle s'héberge dans la **plus petite quantification qui tient le service**. fp16/bf16 est un dernier recours documenté, jamais le point de départ.

**Chercher le quant communautaire AVANT de conclure qu'un modèle ne rentre pas.** L'absence de flag `--quantization` dans une image ne dit rien de ce que la communauté a publié — c'est une limite d'outillage, pas une impossibilité du modèle.

```bash
# dérivés quantifiés d'un modèle donné
curl -s "https://huggingface.co/api/models?other=base_model:quantized:<org>/<model>&limit=50"
# recherche large, puis filtrer int4|int8|awq|gptq|gguf|nf4|w4a16|fp8|bnb
curl -s "https://huggingface.co/api/models?search=<model>&limit=60"
# tailles réelles, fichier par fichier — le nom du repo n'est pas une mesure
curl -s "https://huggingface.co/api/models/<repo>?blobs=true"
```

- Mesurer la **taille totale** (`siblings[].size`) et retenir le plus petit dérivé qui fait le travail.
- **Écarter les dérivés MLX** (Apple) : nos machines sont NVIDIA.
- Distinguer un `.pth`/`.safetensors` BnB d'un **GGUF** (runtime llama.cpp) : ce sont deux chemins d'exécution différents.
- Un checkpoint quantifié peut exiger une dépendance absente de l'image : c'est **une couche à ajouter**, pas un moteur à reconstruire. Vérifier avant de déclarer un chantier :
  `docker run --rm --entrypoint /app/.venv/bin/python <image> -c "import bitsandbytes"`

**Mesure fondatrice** — `fishaudio/s2-pro`, 2026-10-29 : fp16 = 20,3 Go (la conclusion « ça ne rentre pas sur la 3090 » en découlait) ; `groxaxo/s2-pro-BnB-4Bits` et `scarxity/fish-speech-s2-pro-nf4` = **5,0 Go** ; `baicai1145/s2-pro-w4a16` = 6,1 Go ; `drbaph/s2-pro-fp8` = 8,1 Go. Le facteur 4 change la question posée, il ne l'ajuste pas.

## Règle HARD 2 — inactif = sleep, pas résidence

Un modèle chargé qui ne sert pas consomme la ressource qu'il prétend économiser. Le régime attendu est **chargement à la demande, endormissement ensuite**, l'usage restant ponctuel (séances, démonstrations).

| Pile | Mécanisme de sleep attendu |
|---|---|
| vLLM | `--enable-sleep-mode` (+ `POST /sleep`, `/wake_up`) |
| ComfyUI | `/free` piloté par `comfyui_idle_monitor.py` |
| Autres serveurs sans sleep | à signaler comme **limite mesurée** — un idle-monitor qui *arrête* le conteneur n'est pas un sleep : rechargement complet à chaque usage |

Un service GenAI livré sans sleep est **incomplet**, pas « optimisé plus tard ».

## Règle HARD 3 — un chiffre fp16 n'est pas un dimensionnement

Annoncer « il faut 20 Go » pour refuser un hébergement, sans avoir cherché le quant, transforme une limite d'outillage en arbitrage de matériel et fait remonter à l'user une décision qui n'avait pas lieu d'être. Le chiffre à citer est celui du **quant retenu**, et il se mesure.

## Audit de la flotte — ce qui est dû

Pour chaque service GPU : quant actuel · plus petit quant disponible · capacité de sleep · gain de VRAM estimé. L'état de départ (relevé du 2026-10-29) : la 3090 de `po-2023` tient à 23 419 / 24 576 MiB, avec `vllm-zimage` en fp8, `tts-fishaudio` en fp16 (`--half`), la pile `tts-multi`, Whisper et un serveur d'embeddings. Chaque ligne de cette table est une question, pas une fatalité.

## Voir aussi

- [sota-not-workaround.md](sota-not-workaround.md) — Prong A : vrai outil, jamais workaround dégradé ; checklist 6 axes avant `INTRINSIC`
- [../../docs/genai/genai-services.md](../../docs/genai/genai-services.md) — inventaire des services, quantifications et idle management
- [../../docs/reference/cluster-agents.md](../../docs/reference/cluster-agents.md) — GPU par machine
