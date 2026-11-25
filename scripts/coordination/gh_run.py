"""Le lanceur de process des lectures de masse — et le jeton sous lequel il sort.

Ce module ne fait qu'une chose : lancer un processus, et dire sous quel jeton il
part. La question du jeton n'est pas une question de *lecture GitHub* mais
d'identite de lane (#17437 P1) : le seau GraphQL est par UTILISATEUR, et toutes
les lanes sortant sous `jsboige` vident le meme. L'ecriture n'est pas concernee :
elle resout son jeton explicitement (`post_dossier.resolve_write_token`).

Le module est distinct de `gh_bulk.py` pour une raison de taille : `gh_bulk`
tient son plafond de lignes, et la resolution du jeton n'est pas de la lecture
de donnees — c'est la seule chose que ce module sait faire.
"""
from __future__ import annotations

import subprocess
import sys
from collections.abc import Callable
from pathlib import Path

try:
    import gh_identity
except ImportError:  # pragma: no cover - `scripts/ci` hors du sys.path
    sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))
    import gh_identity  # noqa: PLC0415

#: Le lanceur injecte dans les lectures : `(argv, timeout) -> sortie`.
Run = Callable[[list[str], int], str]


def run_defaut(argv: list[str], timeout: int) -> str:
    """`subprocess.run` borne ; un code non nul leve `CalledProcessError`.

    L'environnement de lecture est copie, jamais modifie : l'ecriture garde le
    jeton qu'elle a resolu.
    """
    return subprocess.run(argv, capture_output=True, text=True, encoding="utf-8",
                          timeout=timeout, check=True,
                          env=gh_identity.read_env()).stdout
