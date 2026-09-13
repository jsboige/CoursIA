"""Contrats de check_trivial_diff (#15740) -- verdicts ancres sur les controles fondateurs.

Les valeurs ne sont pas symboliques : ce sont les nombres MESURES des PRs
nommees par l'acceptance de #15740. Un test qui echoue ici signifie que
l'organe a derive d'un verdict fonde par le user :

  #15630  1 fichier, +9/-0    « une PR de la taille d'une tranche de Mortadelle » -> TRIVIAL
  #15724  4 fichiers, +18/-2  « fine comme du papier a cigarette » (tete 8dfcd3942) -> TRIVIAL
  #15737  26 fichiers, +737/-19  la fournée demandée (x37,8 en lignes)          -> OK
  fix 2 lignes d'un bug critique (contre-exemple VERBATIM du user)              -> OK
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from check_trivial_diff import (  # noqa: E402
    TRIVIAL_CHANGED_LINES,
    assess,
    find_written_exception,
)

BODY_TRIVIAL_DOCS = (
    "## Sweep\n\n"
    "Grain: LIGHT/docs — lane myia-po-2025:CoursIA — prev: LIGHT/docs #15723\n\n"
    "Repare les headers orphelins des fichiers X et Y.\n"
)

BODY_TRIVIAL_LOW = (
    "Grain: LOW/docs — lane myia-po-2025:CoursIA — prev: LOW/docs #15617\n"
)

BODY_BUGFIX_2LINES = (
    "## Fix\n\n"
    "Grain: MED/tooling — lane myia-po-2023:CoursIA — prev: MED/tooling #15728\n\n"
    'Corrige le guard mort : len(probleme["tests"]) etait evalue avant le if probleme is None.\n'
)

BODY_EXCEPTION_15719 = (
    "## Sweep ORPHAN_TABLE_ROW\n\n"
    "Grain: LIGHT/docs — lane myia-po-2025:CoursIA — prev: LIGHT/docs #15723\n\n"
    "Repare les 2 derniers fichiers du scanner.\n\n"
    "Exception : residu final mesure — il ne reste que ces 2 fichiers, recensement joint.\n"
)


def _verdict(body, a, d, c=1):
    return assess(body, a, d, c)


# --- contrôles positifs (acceptance #15740) ---------------------------------

def test_control_positif_15630_mortadelle():
    """#15630 : 1 fichier, +9/-0, LOW/docs -- le user l'a nommee triviale."""
    out = _verdict(BODY_TRIVIAL_LOW, 9, 0, 1)
    assert out["verdict"] == "trivial"
    assert out["signals"]["genre_meta"] and out["signals"]["small_volume"]


def test_control_positif_15724_papier_cigarette():
    """#15724 tete 8dfcd3942 : 4 fichiers, +18/-2, LIGHT/docs -- trivial."""
    out = _verdict(BODY_TRIVIAL_DOCS, 18, 2, 4)
    assert out["verdict"] == "trivial"
    assert out["changed_lines"] == 20


# --- contrôles négatifs (acceptance #15740) ---------------------------------

def test_control_negatif_user_fix_2lignes_bug_reel():
    """Le contre-exemple VERBATIM du user : 2 lignes sur un bug critique passent.

    L'échappement se fait par la jambe GENRE (tooling n'est pas META) --
    SANS mécanisme d'exception. C'est le seul faux positif qui coûterait cher.
    """
    out = _verdict(BODY_BUGFIX_2LINES, 2, 1, 1)
    assert out["verdict"] == "ok"
    assert out["signals"]["genre_meta"] is False


def test_control_negatif_volume_15737_fournee():
    """#15737 : 26 fichiers, +737/-19 -- la fournée demandée, même tag LIGHT/docs."""
    out = _verdict(BODY_TRIVIAL_DOCS, 737, 19, 26)
    assert out["verdict"] == "ok"
    assert out["signals"]["small_volume"] is False


def test_control_negatif_genre_notebook():
    """Un petit diff notebook-python n'est jamais trivial par cet organe."""
    body = BODY_TRIVIAL_DOCS.replace("LIGHT/docs", "MED/notebook-python")
    out = _verdict(body, 9, 0, 1)
    assert out["verdict"] == "ok"


# --- exception écrite (#15719) ----------------------------------------------

def test_exception_ecrite_eteint_et_est_citee():
    """La forme « résidu final mesuré » éteint le warning ET l'organe cite la phrase."""
    out = _verdict(BODY_EXCEPTION_15719, 6, 2, 2)
    assert out["verdict"] == "ok"
    quoted = out["signals"]["written_exception"]
    assert quoted is not None
    assert "residu final mesure" in quoted.lower() or "résidu final mesuré" in quoted
    assert "èteint" in out["reason"] or "eteint" in out["reason"]


def test_exception_sans_portee_ne_compte_pas():
    """« résidu » seul (sans final/mesuré/restant) n'est pas une exception déclarée."""
    body = BODY_TRIVIAL_DOCS + "\nIl reste un résidu.\n"
    out = _verdict(body, 6, 2, 2)
    assert out["verdict"] == "trivial"


def test_find_written_exception_accents_et_null():
    assert find_written_exception(None) is None
    assert find_written_exception("rien ici") is None
    got = find_written_exception("Exception seulement résidu final mesuré (recensement joint).")
    assert got is not None and "résidu final mesuré" in got


# --- états unknown (jamais de verdict sur absence de donnée, #14849) --------

def test_unknown_sans_tag_grain():
    out = _verdict("pas de tag ici", 5, 0, 1)
    assert out["verdict"] == "unknown"


def test_unknown_sans_stats():
    out = assess(BODY_TRIVIAL_DOCS, None, None, None)
    assert out["verdict"] == "unknown"


# --- ancrage du seuil --------------------------------------------------------

def test_barre_ancree_entre_les_controles_fondateurs():
    """Le bar doit séparer le plus gros trivial-verdicté (20) du plus petit batch (756)."""
    assert 20 < TRIVIAL_CHANGED_LINES < 756
