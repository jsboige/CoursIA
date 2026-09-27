"""Tests unitaires du module partage frozen_campaigns (#17040).

Le module est charge par importlib (meme convention que
test_check_adjoint_prevalidation et test_merge_ready) : aucun reseau, aucun gh.
Les trois titres reels ci-dessous sont les titres mesures qui fondent
l'exemption de redressement -- ils ne se devinent pas.
"""

import importlib.util
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
MODULE_PATH = HERE.parent / "coordination" / "frozen_campaigns.py"
_spec = importlib.util.spec_from_file_location("frozen_campaigns_under_test", MODULE_PATH)
fc = importlib.util.module_from_spec(_spec)
sys.modules["frozen_campaigns_under_test"] = fc
_spec.loader.exec_module(fc)

# Titres reels (2026-09-23/24) : les deux premiers reparent les degats de la
# campagne densite et citent le parapluie -- ils doivent rester mergeables.
REVERT_TITLE = (
    "revert(density,#17040): App-1-NQueens + App-14b-ConnectFour "
    "restaures avant #17021 (remplissage sous veto)"
)
REDRESSEMENT_TITLE = (
    "fix(semanticweb,#17066): redressement critique de SW-4-CSharp-SPARQL "
    "-- reference de campagne"
)
FROZEN_TITLE = "Densite Lab13-Web-Search-SOTA (#13410)"


def test_the_three_real_titles():
    assert fc.frozen_umbrella_exclusion(REVERT_TITLE, "See #13410") is None
    assert fc.frozen_umbrella_exclusion(REDRESSEMENT_TITLE, "See #13410") is None
    assert (
        fc.frozen_umbrella_exclusion(FROZEN_TITLE, None)
        == "frozen:#13410(veto #17040)"
    )


def test_prefix_number_not_matched():
    # #134100 ne vaut pas #13410 -- le garde-fou (?!\d) couvre le parapluie
    # ET le numero du veto.
    assert fc.frozen_umbrella_exclusion("fix: #134100", "voir #134101") is None
    assert fc.frozen_umbrella_exclusion("fix(x,#170400): titre", "See #13410") is not None


def test_exemption_is_title_only():
    # Le mot redressement dans le BODY ne suffit pas : l'exemption se lit sur
    # le titre seul, sinon n'importe quelle PR de campagne s'exempterait en
    # ecrivant le mot dans son body.
    assert (
        fc.frozen_umbrella_exclusion("fix(x): ordinaire", "redressement, voir #13410")
        is not None
    )


def test_exemption_is_case_insensitive():
    assert fc.frozen_umbrella_exclusion("REVERT(density): restaures", "See #13410") is None
    assert fc.frozen_umbrella_exclusion("Fix: REDRESSEMENT SW-4", "See #13410") is None


def test_branch_prefix_stays_frozen_despite_exempt_title():
    # Les branches wt/vibe-* sont des relais de campagne : aucune exemption,
    # meme sur un titre de redressement.
    assert (
        fc.frozen_umbrella_exclusion(REVERT_TITLE, None, "wt/vibe-g62-density-9")
        == "frozen:#13410(veto #17040,branch wt/vibe-*)"
    )


def test_umbrella_in_body_freezes_despite_ordinary_title():
    assert (
        fc.frozen_umbrella_exclusion("fix(x): ordinaire", "See #11601 (densite QC).")
        == "frozen:#11601(veto #17040)"
    )
