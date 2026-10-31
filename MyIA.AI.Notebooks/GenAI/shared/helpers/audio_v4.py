"""Localisation du paquet ``v4`` de la serie Audio, sans dependre du repertoire courant.

Le paquet ``v4`` vit dans ``<GenAI>/Audio/04-Applications/v4``. Deux carnets de la
serie le chargeaient par une remontee depuis ``Path.cwd()``, si bien que le
bootstrap ne resolvait que si le noyau tournait dans ``04-Applications`` ou un
descendant : depuis ``GenAI/Audio`` la meme cellule levait
``ModuleNotFoundError: No module named 'v4'`` (issue #23179).

Ce module est le point unique de resolution. Les carnets appellent
``ensure_v4_on_path()`` une seule fois, au lieu de recopier la remontee.

Candidats, essayes dans cet ordre :

1. remontee depuis le repertoire de depart (``Path.cwd()`` par defaut) -- cas
   papermill ``--cwd 04-Applications`` et noyau Jupyter lance dans le dossier du
   carnet ;
2. ancre ``GenAI`` : remonter jusqu'a un ancetre de ce nom, puis
   ``Audio/04-Applications`` -- couvre un noyau lance dans ``Audio/`` ou ``GenAI/`` ;
3. descente depuis le depart, sur les deux profondeurs connues du depot :
   ``<depart>/GenAI/Audio/04-Applications`` (noyau lance dans
   ``MyIA.AI.Notebooks``) et ``<depart>/MyIA.AI.Notebooks/GenAI/Audio/04-Applications``
   (noyau lance a la racine du depot).

Si aucun candidat n'aboutit, l'erreur nomme les chemins essayes plutot que de
laisser un ``ModuleNotFoundError: No module named 'v4'`` nu, qui ne dit pas ou le
paquet etait attendu.
"""

from __future__ import annotations

import sys
from pathlib import Path

#: Marqueur d'un dossier racine de paquet ``v4`` : le module partage de la serie.
V4_MARKER = ("v4", "narration.py")

#: Chemin relatif du paquet depuis la racine ``GenAI``.
APPLICATIONS_RELATIVE = ("Audio", "04-Applications")

#: Descentes connues depuis un repertoire quelconque du depot.
DESCENT_PATHS = (
    ("GenAI", *APPLICATIONS_RELATIVE),
    ("MyIA.AI.Notebooks", "GenAI", *APPLICATIONS_RELATIVE),
)


def is_v4_root(path: Path) -> bool:
    """Vrai si ``path`` contient le paquet ``v4`` (marqueur ``v4/narration.py``)."""
    return path.joinpath(*V4_MARKER).is_file()


def v4_candidates(start: Path | None = None) -> list[Path]:
    """Chemins candidats, dans l'ordre de resolution, sans doublon."""
    origin = Path(start).resolve() if start is not None else Path.cwd().resolve()

    candidates: list[Path] = []

    def _add(path: Path) -> None:
        if path not in candidates:
            candidates.append(path)

    # 1. remontee depuis le depart
    for parent in (origin, *origin.parents):
        _add(parent)

    # 2. ancre GenAI : le premier ancetre qui porte ce nom
    for parent in (origin, *origin.parents):
        if parent.name == "GenAI":
            _add(parent.joinpath(*APPLICATIONS_RELATIVE))
            break

    # 3. descente depuis le depart (noyau lance au-dessus du dossier Audio)
    for relative in DESCENT_PATHS:
        _add(origin.joinpath(*relative))

    return candidates


def find_v4_root(start: Path | None = None) -> Path:
    """Rend la racine du paquet ``v4``, ou leve en nommant les chemins essayes."""
    candidates = v4_candidates(start)
    for candidate in candidates:
        if is_v4_root(candidate):
            return candidate

    origin = Path(start).resolve() if start is not None else Path.cwd().resolve()
    detail = "\n".join(f"    - {candidate}" for candidate in candidates)
    raise ModuleNotFoundError(
        "paquet v4 introuvable : aucun candidat ne contient v4/narration.py.\n"
        f"  depart : {origin}\n"
        f"  chemins essayes :\n{detail}\n"
        "  attendu : <GenAI>/Audio/04-Applications/v4/narration.py"
    )


def ensure_v4_on_path(start: Path | None = None) -> Path:
    """Place la racine du paquet ``v4`` sur ``sys.path`` et la rend.

    Idempotent : un second appel ne reeinsere pas le meme chemin.
    """
    root = find_v4_root(start)
    entry = str(root)
    if entry not in sys.path:
        sys.path.insert(0, entry)
    return root
