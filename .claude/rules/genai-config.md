---
paths: MyIA.AI.Notebooks/GenAI/**/*
---

# GenAI Configuration Rules

**Documentation complète** (services, modèles, VRAM, quantizations par service, GPU allocation, ComfyUI Qwen Phase 29) : [docs/genai-services.md](../../docs/genai/genai-services.md).

## Règles HARD

- API keys dans `MyIA.AI.Notebooks/GenAI/.env` (template `.env.example`)
- Variables requises : `OPENAI_API_KEY`, `ANTHROPIC_API_KEY`, `COMFYUI_API_TOKEN` (alias `COMFYUI_AUTH_TOKEN`), `HUGGINGFACE_TOKEN`
  - Note historique : `COMFYUI_BEARER_TOKEN` est l'ancien nom pré-#14382, **non géré** par `render_envs.py` (résout vide). Ne plus l'utiliser. Le bearer bcrypt côté serveur vit dans `.secrets/qwen-api-user.token`, voir [docs/genai/secrets-management.md](../../docs/genai/secrets-management.md).
- Lancer `/validate-genai` ou `python scripts/genai-stack/genai.py validate --full` AVANT exécution de notebooks GenAI
- Hook `block-secrets.py` bloque les `.env` — demander au user d'éditer manuellement
- Sécurisation des services exposés (audit + plan, #16) : [docs/transients/2026-06-14-genai-service-security-audit.md](../../docs/transients/2026-06-14-genai-service-security-audit.md)

## Cibles de chat des carnets

Consigne du mainteneur suivie par #22783 : aucune exécution de chat ne cible un modèle obsolète. Avant migration, classer l'occurrence en **EXECUTION**, **DOCUMENTATION** ou **SPECIFIQUE** ; ne jamais remplacer globalement une famille de noms. La cible par défaut est Swift via vLLM ; un repli vers le modèle courant du mapping est annoncé explicitement, jamais silencieux. Les sorties réelles nomment le modèle utilisé ; changer la cible implique une réexécution complète, pas une retouche des sorties.

Les citations historiques restent possibles avec obsolescence et cible recommandée explicites. Les modèles TTS, transcription et embeddings sont hors de cette migration de chat ; un carnet Audio qui appelle une API de chat n'en est pas exempté. Routes locales/distantes, alias servi et procédure : [mapping des modèles](../../docs/genai/model-mapping-openai.md#politique-dexécution-du-chat).

## ComfyUI Qwen — Architecture critique (Phase 29)

Diffère du SDXL standard. À ne PAS modifier sans test :
- VAE : 16 channels (NOT SDXL standard) — `EmptySD3LatentImage`
- Scheduler : `beta` (mandatory)
- CFG : 1.0 (uses `CFGNorm`, not classic CFG)
- `ModelSamplingAuraFlow` : `shift=3.0`
- Loaders séparés : `VAELoader` + `CLIPLoader(type=sd3)` + `UNETLoader` (NOT `CheckpointLoaderSimple`)
- Text encoding : `TextEncodeQwenImageEdit` (NOT `CLIPTextEncode`), negative : `ConditioningZeroOut`

Pipeline complet et workflow JSON : [docs/genai-services.md](../../docs/genai/genai-services.md).

## Scripts validation

Tous dans `scripts/genai-stack/` (preferer le script wrapper `genai.py`) :
- `genai.py docker status` — état services
- `genai.py validate --full` — validation complète
- `genai.py validate --notebooks` — exec notebooks
