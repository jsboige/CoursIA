#!/usr/bin/env python3
"""
commands/auth.py - Facade vers core/auth_manager.py

Sous-commandes :
    genai.py auth init              # Initialiser les tokens
    genai.py auth sync              # Synchroniser les environnements
    genai.py auth audit             # Audit de securite
    genai.py auth get-token         # Afficher le token actif
    genai.py auth reconstruct-env   # Reconstruire le .env
"""

import sys
from pathlib import Path

# Ajouter le parent au path pour les imports core/
_script_dir = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(_script_dir))

from core.auth_manager import GenAIAuthManager


def register(subparsers):
    """Enregistre la sous-commande auth."""
    parser = subparsers.add_parser('auth', help='Gestion authentification')
    parser.add_argument('action',
                       choices=['init', 'sync', 'audit', 'get-token', 'reconstruct-env'],
                       help='Action a executer')
    parser.add_argument('--force', action='store_true',
                       help='Forcer la regeneration (pour init)')
    parser.add_argument('--json', action='store_true',
                       help='Sortie JSON (pour audit)')
    parser.add_argument('--raw', action='store_true',
                       help='Token brut (pour get-token)')


def execute(args) -> int:
    """Execute la commande auth en delegant a GenAIAuthManager."""
    manager = GenAIAuthManager()

    if args.action == 'init':
        if manager.config_file.exists() and not args.force:
            print("Configuration existante. Utilisez --force pour ecraser.")
            return 1
        manager.create_unified_config()
        manager.synchronize_credentials()
        return 0

    elif args.action == 'sync':
        result = manager.synchronize_credentials()
        return 0 if result else 1

    elif args.action == 'audit':
        report = manager.audit_security()
        if args.json:
            import json
            print(json.dumps(report.to_dict(), indent=2))
        else:
            print(f"\nRAPPORT D'AUDIT ({report.timestamp})")
            print("=" * 60)
            for loc in report.locations:
                status = "OK" if loc.is_valid else "FAIL" if loc.exists else "MISSING"
                print(f"[{status}] {loc.description}")
                print(f"   Path: {loc.path}")
            if report.inconsistencies:
                print("\nINCOHERENCES DETECTEES!")
                for inc in report.inconsistencies:
                    print(f" - {inc['path']}: {inc['issue']}")
            else:
                print("\nTous les systemes sont coherents.")
        return 0

    elif args.action == 'get-token':
        config = manager.load_config()
        if not config:
            print("Aucune configuration trouvee. Executez 'genai.py auth init'.")
            return 1
        if args.raw:
            token = config.get('raw_token', '')
        else:
            token = config.get('bcrypt_hash', '')
        if token:
            print(token)
            return 0
        print("Token non disponible.")
        return 1

    elif args.action == 'reconstruct-env':
        result = manager.reconstruct_env_file()
        return 0 if result else 1

    return 1


def main():
    """Point d'entree standalone."""
    import argparse
    parser = argparse.ArgumentParser(description="Gestion authentification GenAI")
    parser.add_argument('action',
                       choices=['init', 'sync', 'audit', 'get-token', 'reconstruct-env'])
    parser.add_argument('--force', action='store_true')
    parser.add_argument('--json', action='store_true')
    parser.add_argument('--raw', action='store_true')
    args = parser.parse_args()
    sys.exit(execute(args))


if __name__ == "__main__":
    main()
