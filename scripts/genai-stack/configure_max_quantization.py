#!/usr/bin/env python3
"""
configure_max_quantization.py - Configuration de quantification maximale GenAI

CE SCRIPT CONSOLIDE TOUTES LES CONFIGURATIONS DE QUANTIFICATION OPTIMISÉES
POUR LES SERVICES GENAI. IL PERMET DE RESTAURER LES PARAMÈTRES OPTIMAUX
EN UNE SEULE COMMANDE.

Documentation: https://github.com/jsboige/CoursIA/tree/main/GenAI_Series

Usage:
    python configure_max_quantization.py           # Appliquer toutes les configs
    python configure_max_quantization.py --dry-run # Voir les changements sans appliquer
    python configure_max_quantization.py --service zimage  # Un service spécifique

Services supportés:
    - zimage: Z-Image vLLM (FP8)
    - qwen: Qwen Image Edit (Nunchaku INT4)
    - whisper: Whisper API (INT8)
    - musicgen: MusicGen API (INT8)
    - all: Tous les services (default)
"""

import os
import sys
import argparse
from pathlib import Path

_script_dir = Path(__file__).resolve().parent
sys.path.insert(0, str(_script_dir))

# =============================================================================
# CONFIGURATIONS DE QUANTIFICATION MAXIMALE (07/03/2026)
# Ces valeurs ont été validées et testées. NE PAS MODIFIER sans tests.
# =============================================================================

QUANTIZATION_CONFIGS = {
    "zimage": {
        "name": "Z-Image vLLM",
        "description": "Z-Image text-to-image avec vLLM",
        "docker_compose": "docker-configurations/services/vllm-zimage/docker-compose.yml",
        "env_file": "docker-configurations/services/vllm-zimage/.env",
        "env_vars": {
            "VLLM_QUANTIZATION": "fp8"  # bfloat16 -> fp8 (-50% VRAM)
        },
        "vram_before": "10GB",
        "vram_after": "5GB",
        "savings": "-50%",
        "restart_required": True,
        "notes": "FP8 via vLLM native quantization"
    },
    "qwen": {
        "name": "Qwen Image Edit (Nunchaku)",
        "description": "Qwen Image Edit avec quantization INT4 Nunchaku",
        "docker_compose": "docker-configurations/services/comfyui-qwen/docker-compose.yml",
        "models": [
            "svdq-int4_r128-qwen-image-edit-lightningv1.0-4steps.safetensors"
        ],
        "workflow": "scripts/genai-stack/workflows/workflow_qwen_nunchaku_t2i.json",
        "download_command": "genai.py models download-nunchaku --model lightning-4step-r128",
        "validate_command": "genai.py validate --nunchaku",
        "vram_before": "29GB",
        "vram_after": "4GB",
        "savings": "-86%",
        "restart_required": False,
        "notes": "Nunchaku INT4 via SVDQuant, 4-step Lightning"
    },
    "whisper": {
        "name": "Whisper API",
        "description": "Whisper STT avec INT8 quantization",
        "status": "already_configured",
        "notes": "INT8 via bitsandbytes, lazy loading activé",
        "vram_before": "3GB",
        "vram_after": "1GB",
        "savings": "-67%"
    },
    "musicgen": {
        "name": "MusicGen API",
        "description": "MusicGen avec INT8 quantization",
        "status": "already_configured",
        "notes": "INT8 via bitsandbytes, lazy loading activé",
        "vram_before": "4GB",
        "vram_after": "1.5GB",
        "savings": "-62%"
    },
    "hunyuan": {
        "name": "HunyuanVideo",
        "description": "HunyuanVideo avec FP8 quantization",
        "status": "already_configured",
        "notes": "FP8 E4M3FN native",
        "vram_before": "20GB",
        "vram_after": "10GB",
        "savings": "-50%"
    },
    "forge": {
        "name": "Forge Turbo",
        "description": "SDXL Lightning 4-step",
        "status": "no_quantization",
        "notes": "FP16 natif, pas de quantization supérieure disponible",
        "vram": "6.5GB"
    }
}

# =============================================================================
# FONCTIONS DE CONFIGURATION
# =============================================================================

def configure_zimage(env_file: Path, dry_run: bool = False) -> bool:
    """Configure Z-Image avec FP8 quantization."""
    print(f"\n{'='*70}")
    print(f"Configuration: {QUANTIZATION_CONFIGS['zimage']['name']}")
    print(f"{'='*70}")
    print(f"Description: {QUANTIZATION_CONFIGS['zimage']['description']}")
    print(f"VRAM: {QUANTIZATION_CONFIGS['zimage']['vram_before']} → {QUANTIZATION_CONFIGS['zimage']['vram_after']} ({QUANTIZATION_CONFIGS['zimage']['savings']})")
    print(f"Notes: {QUANTIZATION_CONFIGS['zimage']['notes']}")

    if not env_file.exists():
        print(f"⚠️  Fichier non trouvé: {env_file}")
        return False

    # Lire le fichier actuel
    content = env_file.read_text()

    # Vérifier si déjà configuré
    if "VLLM_QUANTIZATION=fp8" in content and "# VLLM_QUANTIZATION=bfloat16" in content:
        print("✅ Déjà configuré avec FP8")
        return True

    # Appliquer la configuration
    new_content = content.replace("VLLM_QUANTIZATION=bfloat16", "# VLLM_QUANTIZATION=bfloat16")
    new_content = new_content.replace("# VLLM_QUANTIZATION=fp8", "VLLM_QUANTIZATION=fp8")

    if dry_run:
        print("\n[DRY RUN] Changements qui seraient appliqués:")
        print("- VLLM_QUANTIZATION=bfloat16 → # VLLM_QUANTIZATION=bfloat16")
        print("- # VLLM_QUANTIZATION=fp8 → VLLM_QUANTIZATION=fp8")
        return True

    env_file.write_text(new_content)
    print("✅ Configuration appliquée: VLLM_QUANTIZATION=fp8")

    if QUANTIZATION_CONFIGS['zimage']['restart_required']:
        print("\n🔄 Redémarrage du container requis:")
        print("   cd docker-configurations/services/vllm-zimage && docker compose restart")

    return True


def configure_qwen(dry_run: bool = False) -> bool:
    """Configure Qwen avec Nunchaku INT4."""
    print(f"\n{'='*70}")
    print(f"Configuration: {QUANTIZATION_CONFIGS['qwen']['name']}")
    print(f"{'='*70}")
    print(f"Description: {QUANTIZATION_CONFIGS['qwen']['description']}")
    print(f"VRAM: {QUANTIZATION_CONFIGS['qwen']['vram_before']} → {QUANTIZATION_CONFIGS['qwen']['vram_after']} ({QUANTIZATION_CONFIGS['qwen']['savings']})")
    print(f"Notes: {QUANTIZATION_CONFIGS['qwen']['notes']}")

    print("\n📥 Commandes pour télécharger les modèles Nunchaku:")
    print(f"   {QUANTIZATION_CONFIGS['qwen']['download_command']}")

    print("\n✅ Commande pour valider la configuration:")
    print(f"   {QUANTIZATION_CONFIGS['qwen']['validate_command']}")

    print("\n📁 Workflow Nunchaku:")
    print(f"   {QUANTIZATION_CONFIGS['qwen']['workflow']}")

    if dry_run:
        print("\n[DRY RUN] Pas de téléchargement en mode dry-run")
        return True

    # Demander confirmation pour le téléchargement
    response = input("\nTélécharger les modèles Nunchaku maintenant? (y/N): ")
    if response.lower() == 'y':
        print("\n📥 Téléchargement des modèles...")
        # TODO: Implémenter le téléchargement automatique
        print("   Utilisez: genai.py models download-nunchaku --model lightning-4step-r128")
        return True
    else:
        print("⏭️  Téléchargement skipé. Configurez manuellement plus tard.")
        return True


def show_summary():
    """Affiche le résumé de toutes les configurations."""
    print(f"\n{'='*70}")
    print(f"RÉSUMÉ DES CONFIGURATIONS DE QUANTIFICATION MAXIMALE")
    print(f"GenAI Series - CoursIA (07/03/2026)")
    print(f"{'='*70}\n")

    total_before = 0
    total_after = 0

    for key, config in QUANTIZATION_CONFIGS.items():
        if config.get("status") == "no_quantization":
            print(f"📦 {config['name']}")
            print(f"   {config['description']}")
            print(f"   VRAM: {config['vram']} (natif, pas de quantization)")
            print(f"   Notes: {config['notes']}\n")
        else:
            vram_before = float(config['vram_before'].replace('GB', ''))
            vram_after = float(config['vram_after'].replace('GB', ''))
            total_before += vram_before
            total_after += vram_after

            status_icon = "✅" if config.get("status") == "already_configured" else "⚙️"
            print(f"{status_icon} {config['name']}")
            print(f"   {config['description']}")
            print(f"   VRAM: {config['vram_before']} → {config['vram_after']} ({config['savings']})")
            print(f"   Notes: {config['notes']}")

            if config.get("restart_required"):
                print(f"   ⚠️  Redémarrage requis")
            print()

    print(f"{'='*70}")
    print(f"VRAM TOTALE (services quantifiables)")
    print(f"  Avant: {total_before}GB")
    print(f"  Après:  {total_after}GB")
    print(f"  Économie: {total_before - total_after}GB ({100*(1-total_after/total_before):.0f}%)")
    print(f"{'='*70}\n")


# =============================================================================
# MAIN
# =============================================================================

def main():
    parser = argparse.ArgumentParser(
        description="Configuration de quantification maximale GenAI",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Exemples:
  %(prog)s                    # Afficher le résumé
  %(prog)s --apply           # Appliquer toutes les configurations
  %(prog)s --apply zimage    # Configurer Z-Image uniquement
  %(prog)s --dry-run         # Voir les changements sans appliquer
        """
    )

    parser.add_argument('--apply', metavar='SERVICE', nargs='?', const='all',
                        help='Appliquer les configurations (all|zimage|qwen)')
    parser.add_argument('--dry-run', action='store_true',
                        help='Montrer les changements sans les appliquer')
    parser.add_argument('--summary', action='store_true',
                        help='Afficher le résumé des configurations')

    args = parser.parse_args()

    # Afficher le résumé par défaut
    if not args.apply and not args.summary:
        show_summary()
        return

    if args.summary:
        show_summary()
        return

    # Appliquer les configurations
    print("\n🔧 Configuration de quantification maximale GenAI")
    print(f"Mode: {'DRY RUN' if args.dry_run else 'APPLICATION'}\n")

    project_root = Path(__file__).resolve().parent.parent.parent
    success_count = 0

    if args.apply in ['all', 'zimage']:
        env_file = project_root / "docker-configurations/services/vllm-zimage/.env"
        if configure_zimage(env_file, args.dry_run):
            success_count += 1

    if args.apply in ['all', 'qwen']:
        if configure_qwen(args.dry_run):
            success_count += 1

    if args.apply == 'all':
        print("\n" + "="*70)
        print("Services déjà configurés (pas d'action requise):")
        for key in ['whisper', 'musicgen', 'hunyuan', 'forge']:
            config = QUANTIZATION_CONFIGS[key]
            print(f"  ✅ {config['name']}: {config['notes']}")

    print(f"\n{'='*70}")
    if args.dry_run:
        print("DRY RUN terminé. Utilisez --apply pour appliquer les changements.")
    else:
        print(f"Configuration terminée: {success_count} service(s) configuré(s)")


if __name__ == "__main__":
    main()
