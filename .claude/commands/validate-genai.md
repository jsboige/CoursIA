Validate the GenAI stack: $ARGUMENTS

Use the `validate-genai` skill for service mapping and configuration details.

Targets: `[all|services|auth|models|notebooks|vram] [--local] [--remote] [--quick]`

Scripts (in `scripts/genai-stack/`):
```bash
python scripts/genai-stack/validate_stack.py       # Full validation
python scripts/genai-stack/validate_notebooks.py   # Notebook execution
python scripts/genai-stack/check_vram.py           # GPU check
python scripts/genai-stack/list_models.py          # Model inventory
python scripts/genai-stack/list_nodes.py           # ComfyUI nodes
python scripts/genai-stack/docker_manager.py       # Docker management
```

Configuration: `MyIA.AI.Notebooks/GenAI/.env` (template: `.env.example`)
Required: `OPENAI_API_KEY`, `ANTHROPIC_API_KEY`, `COMFYUI_BEARER_TOKEN`, `HUGGINGFACE_TOKEN`
