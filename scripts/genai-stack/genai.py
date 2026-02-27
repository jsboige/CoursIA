#!/usr/bin/env python3
"""
genai.py - CLI unifie pour la gestion de la stack GenAI

Point d'entree unique pour gerer les services Docker, valider la stack,
telecharger les modeles, et verifier l'infrastructure GPU.

Usage:
    python scripts/genai-stack/genai.py docker status [--remote]
    python scripts/genai-stack/genai.py docker start comfyui-qwen
    python scripts/genai-stack/genai.py validate --full
    python scripts/genai-stack/genai.py validate --notebooks --group qwen
    python scripts/genai-stack/genai.py notebooks [target]
    python scripts/genai-stack/genai.py models download-qwen
    python scripts/genai-stack/genai.py models list-nodes
    python scripts/genai-stack/genai.py gpu [--detailed]
    python scripts/genai-stack/genai.py auth audit
"""

import sys
import logging
from pathlib import Path

# Ajouter le repertoire du script au path
_script_dir = Path(__file__).resolve().parent
sys.path.insert(0, str(_script_dir))


def main():
    import argparse

    parser = argparse.ArgumentParser(
        description="GenAI Stack CLI - Gestion unifiee de l'infrastructure GenAI",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Exemples:
  genai.py docker status              Statut de tous les services
  genai.py docker start all           Demarrer tous les services
  genai.py validate --full            Validation complete ComfyUI
  genai.py validate --nunchaku        Test Nunchaku INT4 Lightning
  genai.py validate --notebooks       Validation syntaxe notebooks
  genai.py notebooks                  Validation Papermill notebooks
  genai.py models download-qwen       Telecharger modeles Qwen FP8
  genai.py models list-nodes          Lister custom nodes ComfyUI
  genai.py gpu                        Verification VRAM
  genai.py auth audit                 Audit securite tokens
        """
    )

    parser.add_argument('--verbose', '-v', action='store_true',
                       help='Mode verbeux')

    subparsers = parser.add_subparsers(dest='command', help='Commandes disponibles')

    # Enregistrer toutes les sous-commandes
    from commands import docker, validate, notebooks, models, gpu, auth, audio_apis

    docker.register(subparsers)
    validate.register(subparsers)
    notebooks.register(subparsers)
    models.register(subparsers)
    gpu.register(subparsers)
    auth.register(subparsers)
    audio_apis.register(subparsers)

    args = parser.parse_args()

    # Configuration logging
    log_level = logging.DEBUG if args.verbose else logging.INFO
    logging.basicConfig(
        level=log_level,
        format='%(asctime)s - %(levelname)s - %(message)s',
        handlers=[logging.StreamHandler(sys.stdout)],
    )

    # Dispatch
    if args.command == 'docker':
        sys.exit(docker.execute(args))
    elif args.command == 'validate':
        sys.exit(validate.execute(args))
    elif args.command == 'notebooks':
        sys.exit(notebooks.execute(args))
    elif args.command == 'models':
        sys.exit(models.execute(args))
    elif args.command == 'gpu':
        sys.exit(gpu.execute(args))
    elif args.command == 'auth':
        sys.exit(auth.execute(args))
    elif args.command == 'audio-apis':
        sys.exit(audio_apis.execute(args))
    else:
        parser.print_help()
        sys.exit(0)


if __name__ == "__main__":
    main()
