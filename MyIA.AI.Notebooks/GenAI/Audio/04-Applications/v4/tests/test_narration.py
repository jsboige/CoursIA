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
    find_out_of_grammar_markers,
    parse_narration_script,
)

_APPS = _V4.parent
_NOTEBOOKS = (
    "04-1-Educational-Audio-Content.ipynb",
    "04-Audiobook/04-6-Audiobook-Pipeline.ipynb",
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


def _script_committe_04_6() -> str:
    """Relit le script que la cellule 12 de 04-6 a reellement produit.

    Le script n'est pas fige dans une fixture : c'est la **sortie committee** qui
    est mesuree, donc celle que le lecteur du carnet voit. Une fixture se
    desynchronise du carnet sans que rien ne le signale.
    """
    nb = json.loads((_APPS / "04-Audiobook/04-6-Audiobook-Pipeline.ipynb").read_text(encoding="utf-8"))
    for cell in nb["cells"]:
        for out in cell.get("outputs", []):
            text = out.get("text") or (out.get("data", {}) or {}).get("text/plain") or []
            text = "".join(text)
            if "--- Script multi-voix ---" in text:
                body = text.split("--- Script multi-voix ---", 1)[1]
                return body.split("--- Fin du script ---", 1)[0].strip()
    raise AssertionError(
        "script committe introuvable dans 04-6 : la cellule 12 doit imprimer son "
        "script entre les reperes '--- Script multi-voix ---' et '--- Fin du script ---'"
    )


def test_le_script_committe_de_04_6_respecte_la_grammaire():
    """Le vrai script, pas un cas synthetique : c'est lui qui a revele le defaut.

    Mesure du 2026-10-27 : le LLM avait ecrit ``[BOULE_DE_SUIF]`` la ou le prompt
    demandait ``[PERSONNAGE_1]``. Le parseur ne le reconnaissait pas, la replique
    restait au role precedent et ``voice_mapping`` la lisait avec la voix du
    narrateur — sans erreur, sans trace.
    """
    script = _script_committe_04_6()
    assert script, "le script committe est vide"

    inconnus = find_out_of_grammar_markers(script)
    assert inconnus == [], f"marqueurs hors grammaire dans le script committe : {inconnus}"

    segments = parse_narration_script(script)
    assert segments, "un script non vide doit produire au moins un segment"

    replique = [s for s in segments if "Tenez, messieurs" in s["text"]]
    assert replique, "la replique de Boule de Suif doit se retrouver dans un segment"
    assert replique[0]["role"] != DEFAULT_ROLE, (
        "la seule replique du texte ne doit pas etre lue par la voix du narrateur : "
        f"role mesure = {replique[0]['role']}"
    )


def test_un_marqueur_hors_grammaire_est_signale_et_reste_au_role_precedent():
    """Le defaut mesure, epingle : le detecteur le nomme, le parseur ne l'invente pas.

    On n'elargit **pas** la grammaire a tout token majuscule : ``[MUSIQUE]`` ou
    ``[BRUIT]`` en deviendraient des personnages. On rend le defaut visible.
    """
    script = (
        "[NARRATEUR] Boule de Suif offrit son panier aux voyageurs affames.\n"
        "[BOULE_DE_SUIF] Tenez, messieurs, je vous en prie.\n"
    )
    assert find_out_of_grammar_markers(script) == ["[BOULE_DE_SUIF]"]

    segments = parse_narration_script(script)
    assert len(segments) == 1
    assert segments[0]["role"] == DEFAULT_ROLE
    assert "Tenez, messieurs" in segments[0]["text"]


def test_un_script_conforme_ne_signale_rien():
    """Controle negatif du detecteur : sans lui, il signalerait tout et ne dirait rien."""
    script = (
        "[NARRATEUR] Il faisait nuit.\n"
        "[PAUSE]\n"
        "[PERSONNAGE_1] Vous partez deja ?\n"
        "[EXPERT] Le theoreme tient.\n"
    )
    assert find_out_of_grammar_markers(script) == []

