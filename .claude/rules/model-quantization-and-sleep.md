---
paths: docker-configurations/**, scripts/genai-stack/**, docs/genai/**
---

# Quant le plus petit + sleep — la pile GenAI de CoursIA

S'applique aux services de `docker-configurations/` qui chargent un modèle sur un GPU (ComfyUI/Qwen, vLLM, Whisper, FishAudio, pile TTS, embeddings, vidéo). Source : mandat user direct du 2026-10-29 (séance EPF APP3), énoncé en deux temps puis élargi : « la consigne est d'héberger nos modèles avec les quants les plus petits, int8 ou int4 si possible, pour faire de la place », « les modèles doivent passer en sleep quand ils ne sont pas utilisés », puis « on fait ça pour tous nos modèles ».

Le but est explicite et il est le critère d'arbitrage : **récupérer de la capacité GPU**, pas maximiser la fidélité d'un service.

**Périmètre.** La règle couvre la pile GenAI portée par ce dépôt. Un modèle hébergé par un **autre workspace** — le vLLM Swift d'ai-01 (`vllm`, GPU 0 et 1) sert le harnais des agents — s'applique **par demande à son propriétaire** (règle globale « Infra d'un autre workspace : se demande, ne s'applique pas »). Pour un modèle qui sert les agents, le critère n'est d'ailleurs pas le même : la qualité et la latence de réveil à chaque tour priment sur le gain de VRAM.

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

Le facteur entre le fp16 et le quant retenu **change la question posée**, il ne l'ajuste pas : sur un modèle mesuré dans ce dépôt, il divise l'empreinte par 4 et fait tomber un refus d'hébergement. Les chiffres, la table des dérivés et l'état relevé service par service vivent dans [`docs/genai/genai-services.md`](../../docs/genai/genai-services.md).

## Règle HARD 2 — inactif = sleep, pas résidence

Un modèle chargé qui ne sert pas consomme la ressource qu'il prétend économiser. Le régime attendu est **chargement à la demande, endormissement ensuite**, l'usage restant ponctuel (séances, démonstrations).

| Pile | Mécanisme de sleep attendu |
|---|---|
| vLLM | `--enable-sleep-mode`, puis `POST /sleep` et `/wake_up` |
| ComfyUI | `/free` piloté par `comfyui_idle_monitor.py` |
| Autres serveurs sans sleep | à signaler comme **limite mesurée** — un idle-monitor qui *arrête* le conteneur n'est pas un sleep : rechargement complet à chaque usage |

### vLLM — trois précautions, pas une

1. **Les endpoints n'existent qu'en mode dev.** `POST /sleep` et `/wake_up` ne sont servis qu'avec `VLLM_SERVER_DEV_MODE=1`, que la [doc vLLM](https://docs.vllm.ai/en/latest/features/sleep_mode.html) qualifie d'endpoints à ne pas exposer aux utilisateurs. Nos services sont publiés derrière des URLs `*.myia.io` : ils se pilotent **derrière le proxy**, jamais exposés.
2. **Le niveau décide de ce qu'on libère, pas seulement de combien.**
   - **niveau 1** décharge les poids **en RAM CPU** — la doc demande explicitement d'avoir « enough CPU memory » ;
   - **niveau 2** les jette.
3. **Le critère de choix est la RAM hôte, pas la VRAM.** Un sommeil de niveau 1 sur une machine dont la mémoire est déjà tendue **déplace la pression au lieu de la libérer** : il rend la carte et dépose le modèle dans la RAM que les runners ou le moteur voisin réclament. Choisir le niveau sur la marge de RAM hôte mesurée, pas sur la seule libération de VRAM.

Un service GenAI livré sans sleep est **incomplet**, pas « optimisé plus tard ».

## Règle HARD 3 — un chiffre fp16 n'est pas un dimensionnement

Annoncer « il faut 20 Go » pour refuser un hébergement, sans avoir cherché le quant, transforme une limite d'outillage en arbitrage de matériel et fait remonter à l'user une décision qui n'avait pas lieu d'être. Le chiffre à citer est celui du **quant retenu**, et il se mesure.

## Audit de la flotte — ce qui est dû

Pour chaque service GPU : quant actuel · plus petit quant disponible · capacité de sleep · gain de VRAM estimé. L'état relevé service par service se met à jour dans [`docs/genai/genai-services.md`](../../docs/genai/genai-services.md) ; le harnais ne le recopie pas.

## Voir aussi

- [sota-not-workaround.md](sota-not-workaround.md) — Prong A : vrai outil, jamais workaround dégradé ; checklist 6 axes avant `INTRINSIC`
- [../../docs/genai/genai-services.md](../../docs/genai/genai-services.md) — inventaire des services, quantifications, idle management, mesures datées
- [../../docs/reference/cluster-agents.md](../../docs/reference/cluster-agents.md) — GPU par machine
