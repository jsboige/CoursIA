"""Tests de l'organe de secheresse de substance (#13086).

L'organe qui manquait a G-VAR-1 : le picker ponderait le genre CONTENU du
CANDIDAT mais n'avait aucune MEMOIRE de l'histoire de la lane. Ces tests
verrouillent les deux directions d'erreur -- sous-compter (une lane en
secheresse passe) ET sur-accuser (une lane saine est accusee) -- parce qu'un
garde se valide par ses faux negatifs autant que par ses hits.
"""
import sys
import pathlib

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))

from pick_idle_grain import (  # noqa: E402
    CONTENU,
    META,
    DROUGHT_RUN_DEFAULT,
    substance_drought,
)


def _g(number, lane, genre, merged="2026-08-31T00:00:00Z"):
    """Grain tel que `fetch_merged_grains` le rend (genre deja canonicalise)."""
    return {"number": number, "title": f"pr {number}", "lane": lane,
            "genre_raw": genre, "genre": genre, "mergedAt": merged}


LANE = "myia-po-2026:CoursIA"


# --- CONTROLE POSITIF : le defaut que l'organe existe pour attraper --------

def test_alternating_meta_genres_trips_the_drought():
    """Le profil exact de l'incident : guard -> tooling -> docs -> test.

    Aucun de ces quatre ne declenche GENRE-RUN de `variation_light_cap`
    (les genres different a chaque fois), et pourtant la lane produit zero
    contenu. C'est la faille que l'organe ferme -- si ce test passe au vert
    sans l'organe, l'organe ne sert a rien.
    """
    grains = [_g(1, LANE, "guard"), _g(2, LANE, "tooling"),
              _g(3, LANE, "docs"), _g(4, LANE, "test")]
    d = substance_drought(LANE, grains, DROUGHT_RUN_DEFAULT)
    assert d["triggered"] is True
    assert d["run"] == 4
    assert [p["number"] for p in d["run_prs"]] == [1, 2, 3, 4]
    assert d["last_content"] is None


def test_run_counts_only_since_the_last_content_grain():
    grains = [_g(1, LANE, "guard"), _g(2, LANE, "lean"),
              _g(3, LANE, "docs"), _g(4, LANE, "test"), _g(5, LANE, "guard")]
    d = substance_drought(LANE, grains, DROUGHT_RUN_DEFAULT)
    assert d["run"] == 3
    assert d["triggered"] is True
    assert d["last_content"]["number"] == 2


# --- CONTRE-ACCUSATION : les cas ou l'organe doit se taire -----------------

def test_healthy_lane_below_threshold_is_not_accused():
    """Calibrage mesure : la lane la plus saine de la flotte (po-2025:CoursIA,
    41 CONTENU / 45 merges au 2026-08-31) ne depasse jamais un run de 2.
    Le seuil de 3 doit donc rester muet sur deux META consecutifs."""
    grains = [_g(1, LANE, "lean"), _g(2, LANE, "guard"), _g(3, LANE, "docs")]
    d = substance_drought(LANE, grains, DROUGHT_RUN_DEFAULT)
    assert d["run"] == 2
    assert d["triggered"] is False


def test_a_content_merge_resets_the_run():
    grains = [_g(1, LANE, "guard"), _g(2, LANE, "docs"), _g(3, LANE, "test"),
              _g(4, LANE, "notebook-python")]
    d = substance_drought(LANE, grains, DROUGHT_RUN_DEFAULT)
    assert d["run"] == 0
    assert d["triggered"] is False
    assert d["last_content"]["number"] == 4


def test_other_lanes_do_not_contaminate_the_run():
    """Le run est PAR LANE : les META d'une autre lane ne comptent pas."""
    other = "myia-po-2023:CoursIA"
    grains = [_g(1, LANE, "lean"), _g(2, other, "guard"), _g(3, other, "docs"),
              _g(4, other, "test"), _g(5, LANE, "guard")]
    d = substance_drought(LANE, grains, DROUGHT_RUN_DEFAULT)
    assert d["run"] == 1
    assert d["triggered"] is False
    assert d["lane_merges"] == 2


def test_lane_with_no_merges_is_not_accused():
    """Une lane absente du corpus a un run de 0, pas une secheresse.

    Sans ce verrou, toute lane neuve serait accusee des son premier appel."""
    d = substance_drought("myia-po-9999:CoursIA", [_g(1, LANE, "guard")],
                          DROUGHT_RUN_DEFAULT)
    assert d["run"] == 0
    assert d["triggered"] is False
    assert d["lane_merges"] == 0


# --- Lecture ratee : jamais une ardoise propre ----------------------------

def test_unreadable_history_never_reports_a_clean_slate():
    """Un organe qui n'a pas pu mesurer doit le DIRE, pas rendre un zero
    indiscernable d'une lane saine (lecon `instrument-must-name-what-it-
    measured`). Il ne declenche pas non plus -- il ne sait rien."""
    d = substance_drought(LANE, [], DROUGHT_RUN_DEFAULT, error="gh exit 1")
    assert d["measured"] is False
    assert d["error"] == "gh exit 1"
    assert d["triggered"] is False


# --- Genres non resolus : fail-CLOSED, mais NOMMES ------------------------

def test_unresolved_genre_counts_non_content_but_is_named():
    """Politique #13475 reprise : l'inconnu compte contre la lane (un silence
    qui relache le garde ne prouve rien), mais il est nomme pour que la lane
    puisse contester en re-taguant."""
    grains = [_g(1, LANE, "guard"), _g(2, LANE, "diagnostic"),
              _g(3, LANE, "analysis")]
    d = substance_drought(LANE, grains, DROUGHT_RUN_DEFAULT)
    assert d["run"] == 3
    assert d["triggered"] is True
    assert [u["genre"] for u in d["unresolved"]] == ["diagnostic", "analysis"]


def test_partition_is_exhaustive_and_disjoint():
    """CONTENU et META partitionnent l'enumeration close : aucun genre ne peut
    etre dans les deux, et le nombre total est celui de variation-protocol."""
    assert CONTENU & META == set()
    assert len(CONTENU) == 9
    assert len(META) == 7


def test_threshold_is_configurable():
    grains = [_g(1, LANE, "guard"), _g(2, LANE, "docs")]
    assert substance_drought(LANE, grains, 2)["triggered"] is True
    assert substance_drought(LANE, grains, 3)["triggered"] is False
