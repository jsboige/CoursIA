"""Safe SSL Context loader — Windows cert store defense.

Module : scripts/genai-stack/core/safe_ssl.py
Statut : MED/tooling, see issue #12068

## Le probleme

Sur certaines machines du cluster (ai-01, po-2024 observe en premier),
le magasin de certificats Windows contient une entree malformee qui leve
`ssl.SSLError` au premier appel de `ssl.SSLContext._load_windows_store_certs`
(typiquement declenche par l'import de `datasets` / `aiohttp` / `httpx`).
La machine est inutilisable en l'etat pour tout notebook qui charge
des donnees via HTTPS, alors qu'aucune desactivation de verification
n'est desiree (regle secrets-hygiene rule 2 : JAMAIS verify=False,
CERT_NONE, check_hostname disable).

## La solution

Wrap `ssl.SSLContext._load_windows_store_certs` dans une fonction qui :
1. Tente l'appel original.
2. Catch UNIQUEMENT `ssl.SSLError` (les erreurs de parsing du store).
3. Retourne `[]` (liste vide = pas de cert supplementaire du store Windows,
    comportement safe).
4. NE TOUCHE PAS au reste du contexte SSL (verify, check_hostname,
    CERT_REQUIRED, etc. sont preserves).

## Le contrat

- Idempotent : appliquer le patch deux fois ne le double pas.
- Reversible : `disable_safe_windows_store()` restaure la version d'origine.
- Testable : `is_patched()` retourne un booleen, `force_raise`
  permet de simuler un store malforme pour les tests.
- Pas d'effet de bord sur Linux/Mac : `_load_windows_store_certs` existe sur
    TOUTES les plateformes CPython (no-op hors Windows), donc la detection de
    plateforme se fait par `sys.platform`, PAS par `hasattr`. Sur les autres OS,
    `sys.platform != 'win32'` et le patch est un no-op documente.

## L'usage

Trois formes d'usage, par preference :

1. **Auto via env conda `coursia-ml-training`** : ajouter ce module a
   `site-packages/sitecustomize.py` (ou un `.pth`) — le patch est applique
   au demarrage Python, sans modifier un seul notebook.
2. **Manuel debut de notebook** : `from scripts.genai_stack.core.safe_ssl import install_safe_windows_store; install_safe_windows_store()`.
3. **Auto-via-import** : appeler `install_safe_windows_store()` une seule fois
   au top d'un script d'init.

## Reference

- Issue : #12068 (Garde SSL Windows dupliquee dans les notebooks)
- Origine du pattern : ICT-25 cell[32] (commit 11323), rlpt_3 cell[2]
- Cause machine : entree malformee dans le magasin de certificats Windows
- Regle secrets-hygiene rule 2 : JAMAIS verify=False / CERT_NONE / check_hostname disable
"""

from __future__ import annotations

import ssl
import sys
from typing import Callable, List

__all__ = [
    "install_safe_windows_store",
    "disable_safe_windows_store",
    "is_patched",
    "force_raise",
]


_original_load: Callable[..., List] | None = None
_force_raise_active: bool = False


def _safe_load(self: ssl.SSLContext, *args, **kwargs):  # noqa: ANN001
    """Wrap ssl.SSLContext._load_windows_store_certs with SSLError catch.

    Catch UNIQUEMENT `ssl.SSLError` : erreurs de parsing du store Windows
    (entree malformee, format invalide). Toute autre exception (TypeError,
    AttributeError, ...) propage normalement, sans etre masquee.

    Returns an empty list on SSLError : comportement safe (le contexte
    peut toujours fonctionner avec ses certs statiques).

    En mode test (`force_raise=True`), leve systematiquement `ssl.SSLError`
    AVANT d'appeler l'original, simulant un store Windows malforme. Ce
    test hook vit dans `_safe_load` lui-meme (et non dans `_patched_load`)
    pour que le wrapper catch SON PROPRE SSLError simule — pas besoin
    de deux niveaux d'indirection.
    """
    if _original_load is None:
        raise RuntimeError("safe_ssl non initialise — appeler install_safe_windows_store() d'abord")
    try:
        if _force_raise_active:
            raise ssl.SSLError("simulated malformed Windows cert store (force_raise=True)")
        return _original_load(self, *args, **kwargs)
    except ssl.SSLError:
        return []


def force_raise(activate: bool = True) -> None:
    """Active ou desactive le mode test force_raise.

    En mode test, l'appel natif leve systematiquement `ssl.SSLError`,
    simulant un store Windows malforme. Permet de tester le wrapper
    sans dependre d'une machine reellement cassee.

    Args:
        activate: True pour activer le mode test, False pour le desactiver.
    """
    global _force_raise_active
    _force_raise_active = bool(activate)


def _patched_load(self: ssl.SSLContext, *args, **kwargs):  # noqa: ANN001
    """Point d'entree du monkeypatch sur ssl.SSLContext._load_windows_store_certs.

    Delegue a `_safe_load` quiporte la logique de catch + le hook de test.
    Separe les responsabilites : _patched_load est la cible du monkeypatch,
    _safe_load est la logique reelle (testable isolement).
    """
    return _safe_load(self, *args, **kwargs)


def install_safe_windows_store() -> bool:
    """Installe le wrapper safe sur `ssl.SSLContext._load_windows_store_certs`.

    Idempotent : si deja patche, ne fait rien. Hors Windows
    (`sys.platform != 'win32'`), no-op documente — `_load_windows_store_certs`
    existe aussi hors Windows mais n'a pas d'effet (la detection par `hasattr`
    serait donc fausse et patcherait incorrectement).

    Returns:
        True si le patch a ete applique (ou etait deja applique).
        False si la plateforme n'expose pas la methode.
    """
    global _original_load
    if not sys.platform.startswith("win"):
        return False
    if _original_load is not None:
        return True
    _original_load = ssl.SSLContext._load_windows_store_certs
    ssl.SSLContext._load_windows_store_certs = _patched_load
    return True


def disable_safe_windows_store() -> bool:
    """Retire le wrapper et restaure la methode d'origine.

    Returns:
        True si le wrapper a ete retire, False s'il n'etait pas installe.
    """
    global _original_load
    if _original_load is None:
        return False
    ssl.SSLContext._load_windows_store_certs = _original_load
    _original_load = None
    force_raise(False)
    return True


def is_patched() -> bool:
    """Retourne True si le wrapper est actuellement actif."""
    return _original_load is not None
