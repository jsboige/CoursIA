#!/usr/bin/env python3
"""Migration des consommateurs docker-compose vers MyIA-Keys (#17558, phase 4).

Lit un `.env` cible, extrait les cles partagees (celles du coffre), et ecrit
un `.env` minimal contenant UNIQUEMENT les cles par instance + config service.
Les cles partagees sont retirees du fichier : elles viennent desormais du
coffre via `agent_keyring.py run -- <cmd>` au moment de l'appel.

Usage : python scripts/secrets/migrate_env_to_keyring.py <path.env> [--apply]
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

# Clefs partagees (dans le coffre MyIA-Keys, c.1526) -- a retirer des .env
SHARED_KEYS = frozenset({
    "ANTHROPIC_API_KEY", "CIVITAI_TOKEN", "CLAUDISH_PROXY_KEY",
    "COMFYUI_API_TOKEN", "COMFYUI_AUTH_TOKEN", "COMFYUI_VIDEO_TOKEN",
    "DEMUCS_API_KEY", "FUNASR_API_KEY", "GITHUB_ACCESS_TOKEN", "GITHUB_TOKEN",
    "HF_TOKEN", "HUGGINGFACE_TOKEN", "MINIMAX_GENAI_API_KEY",
    "MUSICGEN_API_KEY", "OPENAI_API_KEY", "OPENAI_BASE_URL",
    "OPENROUTER_API_KEY", "QDRANT_API_KEY", "QWEN_API_KEY", "QWEN_API_TOKEN",
    "QWEN_ASR_API_KEY", "SECRET_KEY", "TTS_API_KEY", "TTS_GATEWAY_API_KEY",
    "VLLM_API_KEY", "VLLM_API_KEY_MEDIUM", "WHISPER_API_KEY",
})


def migrate(env_path: Path, apply: bool = False) -> dict:
    """Extrait les cles partagees, ecrit le .env minimal si apply."""
    lines = env_path.read_text(encoding="utf-8").splitlines()
    shared_found = []
    kept_lines = []
    for line in lines:
        stripped = line.strip()
        if not stripped or stripped.startswith("#"):
            kept_lines.append(line)
            continue
        if "=" in stripped:
            key = stripped.split("=", 1)[0].strip()
            if key in SHARED_KEYS:
                shared_found.append(key)
                continue  # retire la cle partagee du fichier
        kept_lines.append(line)

    result = {
        "path": str(env_path),
        "shared_removed": sorted(shared_found),
        "shared_count": len(shared_found),
        "lines_kept": len(kept_lines),
        "lines_removed": len(lines) - len(kept_lines),
    }
    if apply:
        env_path.write_text("\n".join(kept_lines) + "\n", encoding="utf-8")
        result["written"] = True
    else:
        result["written"] = False
    return result


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(
        description="Migration .env -> MyIA-Keys (#17558 phase 4)")
    parser.add_argument("env_file", type=Path)
    parser.add_argument("--apply", action="store_true",
                        help="ecrit le fichier (sinon dry-run)")
    args = parser.parse_args(argv)

    if not args.env_file.exists():
        print(f"ERREUR: {args.env_file} non trouve", file=sys.stderr)
        return 1

    result = migrate(args.env_file, apply=args.apply)
    mode = "ECRIT" if result["written"] else "DRY-RUN"
    print(f"{mode}: {result['path']}")
    print(f"  {result['shared_count']} cles partagees retirees: "
          f"{result['shared_removed']}")
    print(f"  {result['lines_kept']} lignes conservees "
          f"({result['lines_removed']} retirees)")
    if not args.apply:
        print("  Relancer avec --apply pour ecrire le fichier.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
