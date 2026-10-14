"""Tests unitaires du module partage frozen_campaigns (#17040).

Le module est charge par importlib (meme convention que
test_check_adjoint_prevalidation et test_merge_ready) : aucun reseau, aucun gh.

Etat depuis la reouverture user du 2026-10-07 : #13410 (campagne densite
carnets) est ROUVERT, seule #11601 (densite QC round 2) reste gelee. Les
mecanismes de gel par prefixe de branche et de levee par campagne autorisee
ne sont plus exerces par les donnees de production : ils restent couverts par
les tests a donnees injectees (``_simulated_veto``) pour que le prochain veto
herite d'un mecanisme prouve.
"""

import contextlib
import importlib.util
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
MODULE_PATH = HERE.parent / "coordination" / "frozen_campaigns.py"
_spec = importlib.util.spec_from_file_location("frozen_campaigns_under_test", MODULE_PATH)
fc = importlib.util.module_from_spec(_spec)
sys.modules["frozen_campaigns_under_test"] = fc
_spec.loader.exec_module(fc)

# Titres reels (2026-09-23/24) : les deux premiers reparent les degats d'une
# campagne gelee et citent le parapluie -- ils doivent rester mergeables.
REVERT_TITLE = (
    "revert(density,#17040): App-1-NQueens + App-14b-ConnectFour "
    "restaures avant #17021 (remplissage sous veto)"
)
REDRESSEMENT_TITLE = (
    "fix(semanticweb,#17066): redressement critique de SW-4-CSharp-SPARQL "
    "-- reference de campagne"
)
FROZEN_TITLE = "enrich(qc,#11601): densite QC-Py-06b"
# Titre reel d'une PR de la campagne densite, releve avant la reouverture :
# la citation de #13410 ne gele plus depuis le 2026-10-07.
REOPENED_TITLE = "Densite Lab13-Web-Search-SOTA (#13410)"


def test_the_three_real_titles():
    assert fc.frozen_umbrella_exclusion(REVERT_TITLE, "See #11601") is None
    assert fc.frozen_umbrella_exclusion(REDRESSEMENT_TITLE, "See #11601") is None
    assert (
        fc.frozen_umbrella_exclusion(FROZEN_TITLE, None)
        == "frozen:#11601(veto #17040)"
    )


def test_13410_reopened_by_user_decision():
    # Reouverture user du 2026-10-07 : la citation du parapluie (titre OU
    # body) ne gele plus, et les relais wt/vibe-* non plus. Les lecons du
    # gel vivent au fil de #13410 ; #11601 reste gelee, elle.
    assert fc.frozen_umbrella_exclusion(REOPENED_TITLE, None) is None
    assert fc.frozen_umbrella_exclusion("fix(x): ordinaire", "See #13410", None) is None
    assert (
        fc.frozen_umbrella_exclusion(
            "fix(search,g77): relocate 12 lectures", None, "wt/vibe-g77-search-26"
        )
        is None
    )


def test_prefix_number_not_matched():
    # #116010 ne vaut pas #11601 -- le garde-fou (?!\d) couvre le parapluie
    # ET le numero du veto.
    assert fc.frozen_umbrella_exclusion("fix: #116010", "voir #116011") is None
    assert fc.frozen_umbrella_exclusion("fix(x,#170400): titre", "See #11601") is not None


def test_exemption_is_title_only():
    # Le mot redressement dans le BODY ne suffit pas : l'exemption se lit sur
    # le titre seul, sinon n'importe quelle PR de campagne s'exempterait en
    # ecrivant le mot dans son body.
    assert (
        fc.frozen_umbrella_exclusion("fix(x): ordinaire", "redressement, voir #11601")
        is not None
    )


def test_exemption_is_case_insensitive():
    assert fc.frozen_umbrella_exclusion("REVERT(density): restaures", "See #11601") is None
    assert fc.frozen_umbrella_exclusion("Fix: REDRESSEMENT SW-4", "See #11601") is None


def test_umbrella_in_body_freezes_despite_ordinary_title():
    assert (
        fc.frozen_umbrella_exclusion("fix(x): ordinaire", "See #11601 (densite QC).")
        == "frozen:#11601(veto #17040)"
    )


# --- Mecanismes de relais, a donnees injectees ---------------------------------
#
# Depuis la reouverture de #13410, aucune donnee de production n'exerce le
# gel par prefixe de branche : on rejoue ici l'etat d'avant (13410 gele +
# relais wt/vibe-*, campagne autorisee 17636) pour garder le mecanisme prouve.

# Titre reel de #18283 (2026-09-28) : relais wt/vibe-* d'une campagne
# autorisee apres le veto, sans aucune citation de #13410.
RELEASED_TITLE = (
    "fix(prose,#17636): Tweety g2d -- 27 mesures d'artefact resorbees en "
    "prose markdown, 3 KEEP (recit fige PR #10450)"
)


@contextlib.contextmanager
def _simulated_veto():
    saved = (
        fc.FROZEN_UMBRELLAS,
        fc.FROZEN_BRANCH_PREFIXES,
        fc.BRANCH_PREFIX_RELEASES,
    )
    fc.FROZEN_UMBRELLAS = {"13410": "17040", "11601": "17040"}
    fc.FROZEN_BRANCH_PREFIXES = {"wt/vibe-": "13410"}
    fc.BRANCH_PREFIX_RELEASES = {"wt/vibe-": ("17636",)}
    try:
        yield
    finally:
        (
            fc.FROZEN_UMBRELLAS,
            fc.FROZEN_BRANCH_PREFIXES,
            fc.BRANCH_PREFIX_RELEASES,
        ) = saved


def test_branch_prefix_freezes_despite_exempt_title():
    # Les branches wt/vibe-* sont des relais de campagne : aucune exemption,
    # meme sur un titre de redressement.
    with _simulated_veto():
        assert (
            fc.frozen_umbrella_exclusion(REVERT_TITLE, None, "wt/vibe-g62-density-9")
            == "frozen:#13410(veto #17040,branch wt/vibe-*)"
        )


def test_authorized_campaign_title_releases_vibe_branch():
    with _simulated_veto():
        assert (
            fc.frozen_umbrella_exclusion(RELEASED_TITLE, "See #17636", "wt/vibe-g2d-tweety")
            is None
        )


def test_release_falls_when_a_frozen_umbrella_is_cited():
    # Le body cite la campagne gelee : la branche regele la PR.
    with _simulated_veto():
        assert (
            fc.frozen_umbrella_exclusion(RELEASED_TITLE, "suite de #13410", "wt/vibe-g2d-tweety")
            == "frozen:#13410(veto #17040,branch wt/vibe-*)"
        )


def test_release_is_title_only():
    # #17636 dans le body seul ne libere pas un relais muet.
    with _simulated_veto():
        assert (
            fc.frozen_umbrella_exclusion("Densite Lab13", "See #17636", "wt/vibe-g62-density-9")
            == "frozen:#13410(veto #17040,branch wt/vibe-*)"
        )


def test_release_needs_exact_campaign_number():
    with _simulated_veto():
        assert (
            fc.frozen_umbrella_exclusion("fix(prose,#176360): x", None, "wt/vibe-g2x")
            == "frozen:#13410(veto #17040,branch wt/vibe-*)"
        )
