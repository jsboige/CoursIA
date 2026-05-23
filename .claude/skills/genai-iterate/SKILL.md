---
name: genai-iterate
description: Iterate on a GenAI notebook against the self-hosted stack via the genai-stack CLI (config dirs, auth, subdomains, quantization, GPU/VRAM). Arguments: <notebook|service> [--service comfyui|forge|vllm] [--quant int4|fp8] [--validate] [--bg]
---

# GenAI Iterate

Iterer sur un notebook GenAI (`MyIA.AI.Notebooks/GenAI/`) contre la stack auto-hebergee, en pilotant le CLI `scripts/genai-stack/genai.py`. Couvre l'Epic #1385 (GenAI series + hosting). Pour les cycles batch, deleguer a l'agent `genai-iterator` en async.

## Arguments

- `<notebook|service>` : chemin notebook ou nom de service (`comfyui-qwen`, `forge-turbo`, `vllm-zimage`).
- `--service comfyui|forge|vllm` : service cible si ambigu.
- `--quant int4|fp8` : forcer une quantization (Nunchaku INT4 ~4GB / FP8 ~29GB).
- `--validate` : lancer la validation stack (`genai.py validate` + skill `validate-genai`).
- `--bg` : iteration en background.

## Process

### Phase 0 — Config & secrets (HARD)
- `.env` reel = `MyIA.AI.Notebooks/GenAI/.env` (**gitignored**) ; template `.env.example` (carte sous-domaines).
- Secrets uniquement dans `.env`. Jamais de literal inline, jamais `os.getenv("KEY","<fallback>")`, jamais imprimer une valeur de token (cf [.claude/rules/secrets-hygiene.md](../../rules/secrets-hygiene.md)).

### Phase 1 — Pre-flight (CLI genai-stack)
```
python genai.py docker        # service up ?
python genai.py auth          # token present + correct (Bearer comfyui / Basic forge / none vllm) ?
python genai.py gpu           # VRAM libre sur le GPU cible ?
python genai.py quant summary # bonne quant chargee ?
```
- comfyui-qwen : GPU0 ~20GB, Bearer (`COMFYUI_BEARER_TOKEN`). forge-turbo : GPU1 ~8GB, Basic (`FORGE_USER`/`FORGE_PASSWORD`). vllm-zimage : GPU1 ~15GB, no auth.

### Phase 2 — Quantization (arbitrage VRAM)
- GPU 8GB => `genai.py quant apply qwen` (Nunchaku INT4 ~4GB) obligatoire.
- GPU haut de gamme => FP8 possible (`genai.py quant apply zimage`).
- Simuler d'abord : `genai.py quant apply <service> --dry-run`.

### Phase 3 — Iteration notebook
- Moderniser libs/APIs obsoletes (deleguer `notebook-modernizer`).
- Executer via MCP Jupyter (deleguer `notebook-executor`).
- Valider structure/exec/pedagogie (deleguer `notebook-validator`).

### Phase 4 — Commit (regle C.2)
- Notebook AVEC outputs reels. Pas de markdown en remplacement d'execution.
- **Pas de leak `LOCAL_MODE`** dans les outputs committes (re-executer en remote propre).
- Pas d'URL placeholder `yourdomain.com` — vrai sous-domaine.

## FLAGS connus (inventaire 2026-05-23)
- `yourdomain.com` dans `Image/04-4-Cross-Stitch-Legacy`, `Texte/10_LocalLlama`.
- `02-5-Multi-Model-TTS-Gateway` 401.
- `LOCAL_MODE` leak dans outputs de `02-4-Z-Image-Lumina2`, `02-1-Qwen-Image-Edit-2509`.
- Naming `COMFYUI_BEARER_TOKEN` vs `COMFYUI_AUTH_TOKEN` a harmoniser.

## Anti-patterns interdits
- Literal de secret inline / `os.getenv` avec fallback secret / imprimer un token.
- Empiler deux gros modeles au-dela de la VRAM d'un GPU (OOM).
- Committer avec `LOCAL_MODE` actif ou sans outputs reels.
- Script ad-hoc au lieu du CLI `genai.py`.

## Voir aussi
- [.claude/agents/genai-iterator.md](../../agents/genai-iterator.md) — orchestrateur async
- [.claude/skills/validate-genai/SKILL.md](../validate-genai/SKILL.md) — validation stack
- [docs/genai-services.md](../../../docs/genai-services.md) — architectures, scripts, mappings
- [.claude/rules/genai-config.md](../../rules/genai-config.md) — Docker config, GPU, .env
