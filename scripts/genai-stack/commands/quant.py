#!/usr/bin/env python3
"""
commands/quant.py - Gestion de la quantification GenAI

Sous-commandes:
    genai.py quant summary       Afficher le résumé des configurations
    genai.py quant apply         Appliquer toutes les configurations
    genai.py quant apply zimage  Configurer Z-Image avec FP8
    genai.py quant apply qwen    Configurer Qwen avec Nunchaku INT4
    genai.py quant --dry-run     Voir les changements sans appliquer
"""

import sys
from pathlib import Path

_script_dir = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(_script_dir))

from configure_max_quantization import (
    QUANTIZATION_CONFIGS,
    configure_zimage,
    configure_qwen,
    show_summary
)


def register(subparsers):
    """Enregistre les sous-commandes de quantification."""
    parser = subparsers.add_parser('quant',
                                   help='Gestion de la quantification maximale')

    sub = parser.add_subparsers(dest='quant_action', help='Actions disponibles')

    # Summary
    sub.add_parser('summary', help='Afficher le résumé des configurations')

    # Apply
    apply_parser = sub.add_parser('apply', help='Appliquer les configurations')
    apply_parser.add_argument('service', nargs='?', const='all',
                             choices=['all', 'zimage', 'qwen'],
                             help='Service à configurer (default: all)')
    apply_parser.add_argument('--dry-run', action='store_true',
                             help='Voir les changements sans appliquer')


def execute(args):
    """Exécute la commande de quantification."""
    if not hasattr(args, 'quant_action'):
        show_summary()
        return 0

    if args.quant_action == 'summary':
        show_summary()
        return 0

    if args.quant_action == 'apply':
        project_root = Path(__file__).resolve().parent.parent.parent.parent
        service = args.service if args.service else 'all'
        dry_run = getattr(args, 'dry_run', False)

        print("\n🔧 Configuration de quantification maximale GenAI")
        print(f"Mode: {'DRY RUN' if dry_run else 'APPLICATION'}\n")

        success_count = 0

        if service in ['all', 'zimage']:
            env_file = project_root / "docker-configurations/services/vllm-zimage/.env"
            if configure_zimage(env_file, dry_run):
                success_count += 1

        if service in ['all', 'qwen']:
            if configure_qwen(dry_run):
                success_count += 1

        if service == 'all':
            print("\n" + "="*70)
            print("Services déjà configurés (pas d'action requise):")
            for key in ['whisper', 'musicgen', 'hunyuan', 'forge']:
                config = QUANTIZATION_CONFIGS[key]
                print(f"  ✅ {config['name']}: {config['notes']}")

        print(f"\n{'='*70}")
        if dry_run:
            print("DRY RUN terminé. Utilisez --apply pour appliquer les changements.")
        else:
            print(f"Configuration terminée: {success_count} service(s) configuré(s)")

        return 0

    return 0


def main():
    """Point d'entrée standalone."""
    import argparse
    parser = argparse.ArgumentParser(description="Configuration quantification GenAI")
    register(parser.add_subparsers(dest='quant_action'))
    args = parser.parse_args()
    sys.exit(execute(args))


if __name__ == "__main__":
    main()
