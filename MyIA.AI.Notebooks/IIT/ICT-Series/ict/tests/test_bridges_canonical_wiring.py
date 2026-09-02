"""Gates anti-derive : le pont observe-t-il l'organe natif, ou une copie ?

Acceptance 4 de l'issue #14051 -- *"Un test anti-derive : si le module
canonique change sa sortie, le pont rougit. C'est ce qui manque aujourd'hui
et qui donne son sens au mot cross-engine."*

Ce que les gates B1-B6 de ``test_bridges.py`` verifient deja : que le verdict
tri-etat tombe juste. Ce qu'ils ne pouvaient PAS voir : **sur quoi** le
verdict est cable. Avant la tranche 3 de #14051, ``quasi_experimental.py``
redeclarait localement ``make_panel_did`` et ``iv_replay`` ; les gates B1-B6
passaient donc au vert en comparant ``ict.causal_attribution`` a une
reproduction de l'organe natif, et non a l'organe natif. Un changement
d'estimateur dans ``Quasi-Experimental.ipynb`` les aurait laisses verts.

Les gates W1-W6 ci-dessous ferment exactement cet angle mort.

Note de conception -- pourquoi l'IDENTITE et non un ``monkeypatch``
-------------------------------------------------------------------
``from causal_organs import make_panel_did`` lie une *reference* au moment de
l'import. Reassigner ``causal_organs.make_panel_did`` apres coup ne changerait
donc pas ``quasi_experimental.make_panel_did`` -- un test bati sur ce
monkeypatch passerait au vert sans rien prouver, et serait precisement le
genre de gate qui ne peut pas rougir que #14051 denonce.

L'invariant qui a un sens est l'**identite d'objet** : tant que le pont et le
module canonique designent le meme objet fonction, toute evolution du corps
canonique est, mecaniquement, celle du pont. Une copie reintroduite casse
l'identite (W1-W3), casse ``__module__`` (W4), et se voit dans la source
(W5). W6 verrouille l'accord du module canonique avec l'arithmetique de la
cellule native elle-meme.
"""

from __future__ import annotations

import os
import sys

import pytest

_HERE = os.path.dirname(os.path.abspath(__file__))
_ROOT = os.path.dirname(_HERE)
if _ROOT not in sys.path:
    sys.path.insert(0, _ROOT)

from ict.bridges import quasi_experimental as qe  # noqa: E402

# `causal_organs` est rendu importable par le bootstrap sys.path de
# `quasi_experimental` lui-meme : l'importer ICI apres coup verifie, en
# passant, que ce bootstrap fonctionne hors du module qui le pose.
import causal_organs as co  # noqa: E402


# ---------------------------------------------------------------------------
#  W1-W3 : identite d'objet -- le pont ne detient aucune copie                #
# ---------------------------------------------------------------------------
@pytest.mark.parametrize("name", ["make_panel_did", "iv_replay", "panel_did_two_by_two"])
def test_bridge_exposes_the_canonical_object_itself(name):
    """W1-W3 -- ``qe.<f>`` EST ``causal_organs.<f>``, pas une reimplementation.

    Gate falsifiable : re-coller un ``def make_panel_did(...)`` dans
    ``quasi_experimental.py`` rebind le nom sur un objet local et rougit
    immediatement.
    """
    bridged = getattr(qe, name)
    canonical = getattr(co, name)
    assert bridged is canonical, (
        f"{name} : le pont expose un objet distinct du module canonique -- "
        "une copie a probablement ete reintroduite"
    )


# ---------------------------------------------------------------------------
#  W4 : provenance declaree                                                   #
# ---------------------------------------------------------------------------
@pytest.mark.parametrize("name", ["make_panel_did", "iv_replay", "panel_did_two_by_two"])
def test_bridged_callables_declare_the_canonical_module(name):
    """W4 -- ``__module__`` nomme l'organe canonique.

    Complementaire de W1-W3 : attrape le cas ou une copie serait aliasee de
    facon a preserver l'identite apparente sans venir du module canonique.
    """
    assert getattr(qe, name).__module__ == "causal_organs"


# ---------------------------------------------------------------------------
#  W5 : aucune redefinition residuelle dans la source du pont                 #
# ---------------------------------------------------------------------------
def test_bridge_source_defines_no_estimator_of_its_own():
    """W5 -- la source du pont ne (re)definit aucun des organes natifs.

    Gate structurel : il rougit sur un copier-coller meme si l'auteur pense a
    reassigner le nom apres. Les seuls ``def`` legitimes ici sont les
    adaptateurs ``adapt_*``.
    """
    import inspect

    src = inspect.getsource(qe)
    for forbidden in (
        "def make_panel_did",
        "def iv_replay",
        "def panel_did_two_by_two",
        "def _panel_did_two_by_two",
        "def _iv_2sls_scalaire",
    ):
        assert forbidden not in src, (
            f"{forbidden!r} redefini dans le pont : l'organe natif doit etre "
            "importe depuis causal_organs, pas reimplemente (acceptance 3 de #14051)"
        )


# ---------------------------------------------------------------------------
#  W6 : l'organe canonique reproduit l'arithmetique de la cellule native      #
# ---------------------------------------------------------------------------
def test_canonical_two_by_two_matches_the_notebook_cell_arithmetic():
    """W6 -- ``panel_did_two_by_two`` == la double difference de la cellule 5.

    La cellule 5 de ``Quasi-Experimental.ipynb`` calcule les quatre moyennes
    en ligne avec ``.query()`` et garde volontairement cette forme deroulee
    (montrer les quatre cellules 2x2 EST le geste pedagogique). Ce gate rejoue
    cette arithmetique-la, telle qu'elle est ecrite dans le notebook, et exige
    l'egalite EXACTE avec la forme appelable du module.

    C'est le maillon qui relie le module canonique a son organe natif : si
    l'une des deux formes derive, il rougit.
    """
    df = co.make_panel_did(0.0)

    # Transcription litterale de la cellule 5 (n_pre = 5 y est en dur).
    m_t_pre = df.query("group == 1 and period < 5").y.mean()
    m_t_post = df.query("group == 1 and period >= 5").y.mean()
    m_c_pre = df.query("group == 0 and period < 5").y.mean()
    m_c_post = df.query("group == 0 and period >= 5").y.mean()
    tau_cellule = (m_t_post - m_t_pre) - (m_c_post - m_c_pre)

    assert co.panel_did_two_by_two(df, n_pre=5) == pytest.approx(tau_cellule, abs=1e-12)


# ---------------------------------------------------------------------------
#  W7 : l'adaptateur restitue ce que l'organe canonique calcule              #
# ---------------------------------------------------------------------------
def test_adapter_did_equals_the_canonical_pipeline():
    """W7 -- gate au niveau SORTIE, complementaire des gates structurels.

    On rejoue le pipeline entierement depuis ``causal_organs`` et on exige que
    le ``did`` publie par l'adaptateur soit exactement celui-la. Une copie
    dont le corps aurait derive casserait cette egalite meme si elle trompait
    W1-W5.
    """
    for pretrend in (0.0, 0.5):
        expected = co.panel_did_two_by_two(
            co.make_panel_did(differential_pretrend=pretrend), n_pre=5
        )
        res = qe.adapt_panel_did_to_backdoor(differential_pretrend=pretrend)
        assert res["did"] == pytest.approx(expected, abs=1e-12), (
            f"pretrend={pretrend} : l'adaptateur ne publie pas la sortie de "
            "l'organe canonique"
        )
