"""Auto-installer safe_ssl — bootstrap for Windows cert-store defense.

Module : scripts/genai-stack/core/sitecustomize.py
Statut : MED/tooling, see issue #12068 (suite c.452, PR #12289)

## Objet

Bootstrap automatique du module `safe_ssl` au démarrage Python dans l'env conda
`coursia-ml-training` (le kernel Jupyter qui execute les notebooks GenAI Audio,
IIT/ICT-Series, RL). Detourne la necessite d'avoir un monkeypatch inline dans
chaque notebook (cf ICT-25 cell[32] + rlpt_3 cell[2] + ICT-25 cell[29]).

## Le contrat

- Charge `safe_ssl.install_safe_windows_store()` au demarrage Python, AVANT tout
  import utilisateur (`datasets`, `aiohttp`, `httpx`, etc.).
- Idempotent : `safe_ssl.install_safe_windows_store()` est lui-meme idempotent.
- No-op sur Linux/macOS : `install_safe_windows_store()` retourne False sans
  modifier le contexte SSL. Pas d'effet de bord.
- Tolerable : si `safe_ssl` n'est pas importable (env differente), le bootstrap
  echoue silencieusement et le notebook continue comme avant.

## Pourquoi sitecustomize et pas usercustomize

`sitecustomize.py` est charge par Python au demarrage (cf PEP 370), automatiquement,
avant tout autre code utilisateur. C'est le hook canonique pour bootstrap env-wide.

## Le câblage (HOWTO)

1. **Symlink ou copier** ce fichier dans le site-packages de l'env conda cible :

   ```
   ln -s /c/dev/CoursIA-2/scripts/genai-stack/core/sitecustomize.py \
         /c/Users/jsboi/miniconda3/envs/mcp-jupyter-py310/Lib/site-packages/sitecustomize.py
   ```

   Ou, pour eviter le symlink, copier le fichier dans le site-packages.

2. **Verification** : demarrer un kernel `coursia-ml-training`, executer :

   ```python
   from scripts.genai_stack.core import safe_ssl
   safe_ssl.is_patched()  # True si Windows, False si Linux/macOS
   ```

3. **Ou utiliser un `.pth`** (alternative au symlink) :

   ```
   # Fichier /c/Users/jsboi/miniconda3/envs/mcp-jupyter-py310/Lib/site-packages/safe_ssl.pth
   import sys, os
   sys.path.insert(0, "/c/dev/CoursIA-2/scripts/genai-stack")
   ```

## Le test

`scripts/tests/test_sitecustomize_safe_ssl.py` verifie que :
- importer `sitecustomize` declenche l'install (si Windows)
- sur Linux/macOS, `is_patched()` reste False
- l'install est re-essayable apres un disable()

## Reference

- Issue : #12068 (Garde SSL Windows dupliquee dans les notebooks)
- PR organe : #12289 (PR c.452 safe_ssl module + 9 tests)
- PR câblage : c.453 (cette PR)
- Origine du pattern : ICT-25 cell[32] (commit 11323), rlpt_3 cell[2], ICT-25 cell[29]
- Cause machine : entree malformee dans le magasin de certificats Windows
- Regle secrets-hygiene rule 2 : JAMAIS verify=False / CERT_NONE / check_hostname disable
"""

from __future__ import annotations

import os
import sys


def _bootstrap_safe_ssl() -> None:
    """Active le monkeypatch safe_ssl si disponible. Echec silencieux sinon."""
    # Ne rien faire si SSL_SAFE_BOOTSTRAP_DISABLED est set explicitement.
    if os.environ.get("SAFE_SSL_BOOTSTRAP_DISABLED") == "1":
        return
    # Si on n'est pas dans l'env coursia-ml-training, ne rien faire non plus.
    # (Permet a d'autres envs d'utiliser Python sans le monkeypatch.)
    conda_env = os.environ.get("CONDA_DEFAULT_ENV", "")
    if conda_env and conda_env != "mcp-jupyter-py310":
        # Note : `coursia-ml-training` utilise l'env `mcp-jupyter-py310` (cf
        # `kernel.json` du kernel Jupyter `coursia-ml-training`). On filtre
        # par env conda pour eviter de polluer les autres envs.
        return
    try:
        # Ajouter le chemin `scripts/genai-stack` au sys.path si necessaire.
        scripts_genai = os.path.join(
            os.path.dirname(os.path.abspath(__file__)),  # scripts/genai-stack/core
            "..",  # scripts/genai-stack
        )
        scripts_genai = os.path.abspath(scripts_genai)
        if scripts_genai not in sys.path:
            sys.path.insert(0, scripts_genai)
        from core import safe_ssl  # type: ignore  # noqa: E402, I001
        safe_ssl.install_safe_windows_store()
    except Exception:
        # Bootstrap optionnel : si safe_ssl n'est pas importable (env differente,
        # chemin non-resolvable, etc.), le notebook continue comme avant.
        # JAMAIS d'effet de bord visible.
        pass


_bootstrap_safe_ssl()
