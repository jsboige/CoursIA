"""test_narration.py — garde-fou de l'organe `v4/narration.py` (issue #22901).

Les trois premiers cas epinglent les **divergences mesurees** entre les deux
copies de `parse_narration_script` que la serie portait (04-1 cellule 14 et 04-6
cellule 12), chacune etant un defaut reel :

* 04-1 ne reconnaissait pas `[PERSONNAGE_1]` — un script produit par 04-6 se
  faisait avaler par le role precedent ;
* 04-6 ne reconnaissait pas `[EXPERT]` — symetriquement ;
* 04-1 emettait un segment reduit a `'...'` pour une ligne `[PAUSE]` seule, et le
  faisait donc synthetiser par l'API payante.

Le dernier cas est statique : il lit les deux carnets et refuse qu'une copie de
la fonction y reapparaisse. Une consolidation qui ne se mesure pas se defait.

Execution, depuis `04-Applications/` :

    python -m pytest v4/tests/test_narration.py -v
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

_V4 = Path(__file__).resolve().parent.parent
if str(_V4.parent) not in sys.path:
    sys.path.insert(0, str(_V4.parent))

from v4.narration import (  # noqa: E402  (apres l'insertion de sys.path)
    DEFAULT_ROLE,
    PAUSE_MARKER,
    PAUSE_TEXT,
    parse_narration_script,
)

_APPS = _V4.parent
_NOTEBOOKS = (
    "04-1-Educational-Audio-Content.ipynb",
    "04-6-Audiobook-Pipeline.ipynb",
)


def test_segmente_un_marqueur_personnage():
    """04-1 ne reconnaissait pas `[PERSONNAGE_n]` : le texte restait au role precedent."""
    script = (
        "[NARRATEUR] Il faisait nuit sur la ville.\n"
        "[PERSONNAGE_1] Vous partez deja ?\n"
        "[PERSONNAGE_2] A l'aube.\n"
    )
    segments = parse_narration_script(script)
    assert [s["role"] for s in segments] == ["NARRATEUR", "PERSONNAGE_1", "PERSONNAGE_2"]
    assert segments[1]["text"] == "Vous partez deja ?"


def test_segmente_un_marqueur_expert():
    """04-6 ne reconnaissait pas `[EXPERT]` : le texte restait au role precedent."""
    script = "[EXPERT] Le theoreme tient sous hypothese de log-concavite.\n"
    segments = parse_narration_script(script)
    assert len(segments) == 1
    assert segments[0]["role"] == "EXPERT"


def test_un_segment_reduit_a_une_pause_n_est_pas_emis():
    """04-1 envoyait `'...'` a l'API : un segment sans texte propre ne produit rien.

    Une ligne `[PAUSE]` qui suit du texte **allonge** le segment courant (« Un.
    ... ») — ce n'est pas le cas vise. Le cas vise est celui ou la pause arrive
    alors qu'aucun texte n'attend : apres un marqueur de role muet, ou en tete de
    script. Le texte du segment vaut alors `'...'`, valeur vraie pour `if text:`,
    et la copie de 04-1 le faisait synthetiser.
    """
    script = "[PERSONNAGE_1] [PAUSE]\n[NARRATEUR] Un.\n[PAUSE]\n[NARRATEUR] Deux.\n"
    segments = parse_narration_script(script)
    assert [s["role"] for s in segments] == ["NARRATEUR", "NARRATEUR"]
    assert [s["text"] for s in segments] == ["Un. ...", "Deux."]
    assert all(s["text"] != PAUSE_TEXT for s in segments)


def test_le_texte_avant_le_premier_marqueur_prend_le_role_par_defaut():
    """Les deux copies differaient ici (`DEFAULT` contre `NARRATEUR`) ; l'union tranche."""
    segments = parse_narration_script("Une ligne sans marqueur.\n[EXPERT] Puis une autre.\n")
    assert segments[0] == {"role": DEFAULT_ROLE, "text": "Une ligne sans marqueur."}
    assert segments[1]["role"] == "EXPERT"


def test_une_pause_au_milieu_du_texte_devient_des_points_de_suspension():
    """Comportement commun aux deux copies, conserve."""
    segments = parse_narration_script("[NARRATEUR] Il se tut. [PAUSE] Puis reprit.\n")
    assert segments[0]["text"] == f"Il se tut. {PAUSE_TEXT} Puis reprit."


def test_les_carnets_importent_l_organe_au_lieu_de_le_redefinir():
    """Garde statique : aucune copie de la fonction ne doit revenir dans les carnets."""
    for name in _NOTEBOOKS:
        nb = json.loads((_APPS / name).read_text(encoding="utf-8"))
        source = "\n".join("".join(cell["source"]) for cell in nb["cells"])
        assert "def parse_narration_script" not in source, f"{name} redefinit le parseur"
        assert "from v4.narration import" in source, f"{name} n'importe pas l'organe"
