"""narration.py — parseur de script de narration multi-voix (organe partage).

Pourquoi ce module existe (issue #22901, arbitrage B de #22528)
--------------------------------------------------------------
`parse_narration_script` etait defini **deux fois** dans la serie, avec la meme
docstring et le meme corps a trois lignes pres :

    +---------------------------+----------------------------------+----------------------------------+
    |                           | 04-1 cellule 14                  | 04-6 cellule 12                  |
    +---------------------------+----------------------------------+----------------------------------+
    | motif de role             | \\[(NARRATEUR|EXPERT)\\]          | \\[(NARRATEUR|PERSONNAGE_\\d+)\\]  |
    | role par defaut           | "DEFAULT"                        | "NARRATEUR"                      |
    | garde de texte vide       | if text:                         | if text and text != '...'        |
    +---------------------------+----------------------------------+----------------------------------+

Deux consequences mesurees, pas supposees :

1. **04-1 ne savait pas segmenter un script de la chaine audiobook.** Le prompt
   de 04-6 demande des marqueurs ``[PERSONNAGE_1]`` ; passes au parseur de 04-1,
   ils tombaient dans le texte courant et restaient attribues au role precedent.
2. **04-1 envoyait « ... » a l'API payante.** Un segment dont le seul contenu est
   ``[PAUSE]`` donne ``text == '...'``, valeur vraie pour ``if text:`` : il etait
   ajoute aux segments puis synthetise par ``client.audio.speech.create``.

Ce module porte l'union des deux comportements : les trois familles de marqueurs,
le role par defaut ``NARRATEUR`` (les deux carnets retombent de toute facon sur la
voix du narrateur pour un role inconnu), et la garde qui ecarte un segment reduit
a une pause.

Ce qui n'est **pas** extrait ici : la boucle de synthese (``voice_mapping`` +
``client.audio.speech.create``). Les deux carnets n'ont pas la meme gestion
d'erreur par segment — 04-6 encapsule chaque appel dans un ``try/except`` et
poursuit, 04-1 laisse remonter — et unifier ce comportement changerait ce qu'une
panne partielle produit dans chacun. La decision est celle de l'issue #22901,
acceptance 5.

Aucune dependance externe : la bibliotheque standard suffit.
"""
from __future__ import annotations

import re
from typing import Dict, List

#: Marqueurs de role reconnus par le parseur — union des deux copies d'origine.
ROLE_MARKER_RE = re.compile(r"\[(NARRATEUR|EXPERT|PERSONNAGE_\d+)\]")

#: Marqueur de pause, remplace dans le texte par ``PAUSE_TEXT``.
PAUSE_MARKER = "[PAUSE]"

#: Ce que devient une pause dans le texte envoye au moteur TTS.
PAUSE_TEXT = "..."

#: Role attribue au texte qui precede le premier marqueur.
DEFAULT_ROLE = "NARRATEUR"


def parse_narration_script(
    script: str, default_role: str = DEFAULT_ROLE
) -> List[Dict[str, str]]:
    """Decoupe un script a marqueurs ``[ROLE]`` en segments ``{"role", "text"}``.

    Le texte qui precede le premier marqueur prend ``default_role``. Un segment
    dont le texte est vide, ou reduit a une pause, n'est pas emis : il n'y a rien
    a synthetiser.

    Args:
        script: script complete, une ligne par bloc, marqueurs en debut de ligne.
        default_role: role des lignes qui precedent le premier marqueur.

    Returns:
        La liste des segments, dans l'ordre du script.
    """
    segments: List[Dict[str, str]] = []
    current_role = default_role
    current_text: List[str] = []

    def _flush() -> None:
        if not current_text:
            return
        text = re.sub(re.escape(PAUSE_MARKER), PAUSE_TEXT, " ".join(current_text).strip())
        if text and text != PAUSE_TEXT:
            segments.append({"role": current_role, "text": text})

    for line in script.split("\n"):
        line = line.strip()
        if not line:
            continue

        role_match = ROLE_MARKER_RE.match(line)
        if role_match:
            _flush()
            current_role = role_match.group(1)
            remaining = line[role_match.end():].strip()
            current_text = [remaining] if remaining else []
        else:
            current_text.append(line)

    _flush()
    return segments
