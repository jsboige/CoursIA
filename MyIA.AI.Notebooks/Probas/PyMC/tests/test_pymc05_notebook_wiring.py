"""Gate anti-derive du cablage PyMC-05 -> pymc_causal_organs (acceptance 2 et 4 de #14051).

Ce que ce fichier verifie, et pourquoi il existe
------------------------------------------------

L'acceptance 2 de #14051 demande que le notebook natif **importe** son module
canonique au lieu de redefinir les organes. Une telle exigence, laissee en
prose, est invisible : rien n'empeche une edition ulterieure de recoller un
``def enumerate_scm`` dans la cellule 5, et le notebook continuerait de
s'executer sans erreur. C'est precisement le mode de defaillance que
l'issue #14051 decrit pour ``ict.bridges`` -- une copie qui derive en
silence pendant que tout reste vert.

Les gates N1-N3 verrouillent donc la **forme** du cablage (import, pas
definition), et N4 verrouille sa **consequence numerique** : les nombres
publies dans les sorties committees du notebook doivent etre ceux que le
module canonique calcule aujourd'hui. Si ``pymc_causal_organs.py`` change
ses CPT ou son estimateur, N4 rougit -- ce qui est exactement le sens du
mot « anti-derive » de l'acceptance 4.

Note de lecture : N4 lit les **sorties committees** (le livrable
pedagogique, cf C.2), pas une re-execution. Un test qui re-executerait le
notebook mesurerait l'environnement du runner, pas la coherence du
livrable ; et il exigerait ``pymc`` en CI la ou ces organes n'en ont aucun
besoin (``enumerate_scm`` est une sommation exhaustive sans RNG).
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

import pytest

_PYMC_DIR = Path(__file__).resolve().parent.parent
if str(_PYMC_DIR) not in sys.path:
    sys.path.insert(0, str(_PYMC_DIR))

import pymc_causal_organs as pco  # noqa: E402

_NOTEBOOK = _PYMC_DIR / "PyMC-05-Causal-Inference.ipynb"


def _code_cells() -> list[str]:
    nb = json.loads(_NOTEBOOK.read_text(encoding="utf-8"))
    return ["".join(c["source"]) for c in nb["cells"] if c["cell_type"] == "code"]


def _cell_outputs_text(predicate) -> str:
    """Texte concatene des sorties de la premiere cellule code satisfaisant `predicate`."""
    nb = json.loads(_NOTEBOOK.read_text(encoding="utf-8"))
    for cell in nb["cells"]:
        if cell["cell_type"] != "code":
            continue
        if not predicate("".join(cell["source"])):
            continue
        chunks = []
        for out in cell.get("outputs", []):
            chunks.append("".join(out.get("text", [])))
        return "".join(chunks)
    raise AssertionError("aucune cellule ne satisfait le predicat")


# ---------------------------------------------------------------------------
# N1-N3 : la FORME du cablage -- importer, ne pas redefinir
# ---------------------------------------------------------------------------

def test_n1_engine_is_imported_not_defined():
    """N1 -- le moteur d'enumeration est importe du module, pas redefini."""
    cells = _code_cells()
    assert any("from pymc_causal_organs import enumerate_scm" in c for c in cells), (
        "la cellule 5 doit importer enumerate_scm depuis le module canonique"
    )
    offenders = [i for i, c in enumerate(cells) if re.search(r"^def enumerate_scm\(", c, re.M)]
    assert not offenders, (
        f"enumerate_scm est redefini dans le notebook (cellules code {offenders}) : "
        "c'est la duplication que #14051 supprime"
    )


def test_n2_front_door_scm_and_helper_are_imported():
    """N2 -- le SCM front-door et P(Y|M,X) viennent du module."""
    cells = _code_cells()
    assert any("from pymc_causal_organs import FRONT_SCM as front_scm" in c for c in cells), (
        "la cellule 20 doit importer FRONT_SCM depuis le module canonique"
    )
    redefined_scm = [i for i, c in enumerate(cells) if re.search(r"^front_scm\s*=\s*\[", c, re.M)]
    assert not redefined_scm, (
        f"front_scm est redeclare en litteral (cellules {redefined_scm}) : deux definitions "
        "peuvent diverger sans que rien ne rougisse"
    )
    redefined_fn = [i for i, c in enumerate(cells) if re.search(r"^def p_y_given_m_x\(", c, re.M)]
    assert not redefined_fn, f"p_y_given_m_x est redefini (cellules {redefined_fn})"


def test_n3_no_organ_is_shadowed_anywhere():
    """N3 -- aucune cellule, meme d'exercice, ne redefinit un organe canonique.

    Gate large a dessein : les cellules d'exercice (31, 32) invitent le lecteur
    a reutiliser ``enumerate_scm``. Si l'une d'elles finissait par en recoller
    une copie, la propriete « une seule definition » tomberait sans bruit.
    """
    for name in ("enumerate_scm", "p_y_given_m_x"):
        offenders = [i for i, c in enumerate(_code_cells()) if re.search(rf"^def {name}\(", c, re.M)]
        assert not offenders, f"{name} redefini dans les cellules {offenders}"


# ---------------------------------------------------------------------------
# N4 : la CONSEQUENCE -- les nombres publies sont ceux du module
# ---------------------------------------------------------------------------

def test_n4_published_numbers_match_the_canonical_module():
    """N4 -- anti-derive : les sorties committees == ce que le module calcule.

    C'est le gate qui donne son sens a « cross-engine » : il echoue si le
    module derive de ce que le notebook publie, dans un sens comme dans
    l'autre.
    """
    text = _cell_outputs_text(lambda s: "Front-door  P(Cancer | do(Smoke))" in s)

    def published(pattern: str) -> float:
        m = re.search(pattern, text)
        assert m, f"motif absent des sorties committees : {pattern}\n--- sorties ---\n{text}"
        return float(m.group(1))

    p_x1 = pco.enumerate_scm(pco.FRONT_SCM, "smoke")
    p_m1 = pco.enumerate_scm(pco.FRONT_SCM, "tar", evidence={"smoke": True})
    do_direct = pco.enumerate_scm(pco.FRONT_SCM, "cancer", do_vars={"smoke": True})

    p_m0 = 1 - p_m1
    inner_m1 = pco.p_y_given_m_x(True, True) * p_x1 + pco.p_y_given_m_x(True, False) * (1 - p_x1)
    inner_m0 = pco.p_y_given_m_x(False, True) * p_x1 + pco.p_y_given_m_x(False, False) * (1 - p_x1)
    front_door = p_m1 * inner_m1 + p_m0 * inner_m0

    # Les sorties sont formatees en .3f : on compare a cette precision.
    assert published(r"P\(X=smoke\) marginal = ([0-9.]+)") == pytest.approx(p_x1, abs=5e-4)
    assert published(r"P\(M=1\|X=1\) = ([0-9.]+)") == pytest.approx(p_m1, abs=5e-4)
    assert published(r"Front-door  P\(Cancer \| do\(Smoke\)\) = ([0-9.]+)") == pytest.approx(
        front_door, abs=5e-4
    )
    assert published(r"do\(X=1\) direct \(mutilation\)       = ([0-9.]+)") == pytest.approx(
        do_direct, abs=5e-4
    )


def test_n5_front_door_identity_holds_on_the_published_scm():
    """N5 -- la propriete que la section 6 demontre tient sur le SCM importe.

    Complement de N4 : N4 verifie l'accord notebook/module ; N5 verifie que
    ce sur quoi ils s'accordent est bien l'identite front-door de Pearl.
    """
    p_x1 = pco.enumerate_scm(pco.FRONT_SCM, "smoke")
    p_m1 = pco.enumerate_scm(pco.FRONT_SCM, "tar", evidence={"smoke": True})
    inner_m1 = pco.p_y_given_m_x(True, True) * p_x1 + pco.p_y_given_m_x(True, False) * (1 - p_x1)
    inner_m0 = pco.p_y_given_m_x(False, True) * p_x1 + pco.p_y_given_m_x(False, False) * (1 - p_x1)
    front_door = p_m1 * inner_m1 + (1 - p_m1) * inner_m0
    do_direct = pco.enumerate_scm(pco.FRONT_SCM, "cancer", do_vars={"smoke": True})
    assert front_door == pytest.approx(do_direct, abs=1e-12)
