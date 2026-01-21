#!/usr/bin/env python3
"""
test_nunchaku_generation.py - Wrapper pour validation Nunchaku INT4 Lightning

DEPRECATION: Ce script est maintenant un alias vers validate_stack.py --nunchaku
Pour une utilisation directe, executez:

    python validate_stack.py --nunchaku

Ce wrapper est conserve pour retrocompatibilite et tests rapides.
"""

import subprocess
import sys
from pathlib import Path

def main():
    script_dir = Path(__file__).resolve().parent
    validate_script = script_dir / "validate_stack.py"

    # Construire la commande
    cmd = [sys.executable, str(validate_script), "--nunchaku"]

    # Ajouter prompt custom si fourni en argument
    if len(sys.argv) > 1:
        # Si l'utilisateur a passe un prompt, on ne peut pas le passer directement
        # car validate_stack.py ne supporte pas les prompts custom
        print(f"Note: Le prompt custom sera ignore. Utilisez le workflow directement dans ComfyUI.")
        print(f"      Prompt fourni: {' '.join(sys.argv[1:])}")
        print()

    print("=" * 70)
    print("TEST NUNCHAKU INT4 LIGHTNING via validate_stack.py")
    print("=" * 70)
    print(f"Commande: {' '.join(cmd)}")
    print()

    # Executer validate_stack.py --nunchaku
    result = subprocess.run(cmd)
    sys.exit(result.returncode)


if __name__ == "__main__":
    main()
