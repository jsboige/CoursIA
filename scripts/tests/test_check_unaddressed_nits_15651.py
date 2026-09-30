"""#15651 — le timing d'une levee n'est pas une reserve (« avant merge »).

Fondateur (#15648, les deux commentaires etaient du coordinateur, dont
celui qui LEVE) :

    « Le commentaire precedent enregistrait une reserve ; voici sa levée,
     avant merge et nommée. »

comptait comme une NOUVELLE reserve via le marqueur de prose « avant merge »
— classe #13030 (« pose, pas cite ») transposee a la prose : une levee qui
PARLE du merge s'auto-incrimine, le gate ne peut jamais atteindre rc=0, et
la lane est tentee de reformuler sa levee pour le verdir (fabrication de
vert, l'exact contraire du but de B.0).

Le fix ancre les trois marqueurs TEMPORELS : une occurrence en apposition
d'un lexeme de levee + ponctuation (« levee, » / « lifted, ») est morte.
La ponctuation est le discriminant — sans elle, negation et infinitif
restent vivants (garde-fous ci-dessous, niveau marqueur : ces corps ne
blocquent pas tous via classify a cause du piege has_live_lift preexistant,
qui ne relève pas de ce grain).
"""

import importlib.util
import sys
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
CHECK_PATH = HERE.parent / "check_unaddressed_nits.py"

spec = importlib.util.spec_from_file_location("check_unaddressed_nits_15651", CHECK_PATH)
mod = importlib.util.module_from_spec(spec)
sys.modules["check_unaddressed_nits_15651"] = mod
spec.loader.exec_module(mod)

MARKERS = tuple(mod.CONCERN_MARKERS)


FOUNDER_LIFT = (
    "Le commentaire precedent enregistrait une reserve ; voici sa levée, "
    "avant merge et nommée."
)


# --- Fondateur : le timing de la levee ne pose pas de reserve -------------

def test_founder_lift_timing_not_a_concern():
    assert mod.classify("myia-ai-01", FOUNDER_LIFT) is None


def test_founder_variants_marker_level():
    """Niveau marqueur (la ou le fix vit) : les trois temporels meurent
    en apposition, toutes langues et casses confondues."""
    assert mod.has_live_marker(FOUNDER_LIFT, MARKERS) is False
    assert mod.has_live_marker("Point lifted, before merge.", MARKERS) is False
    assert mod.has_live_marker("Voici sa levée, avant de merger.", MARKERS) is False
    # Casse du lexeme en tete de phrase : le regex est IGNORECASE.
    assert mod.has_live_marker("Levée, avant merge — tout est couvert.", MARKERS) is False


def test_apposition_neutralizes_only_temporal_markers():
    """Pin du scope : l'apposition ne neutralise QUE les temporels. Un
    vereditf pose juste apres une levee reste vivant — #14682, le filet
    ne s'elargit pas."""
    assert mod.has_live_marker(
        "Voici ma levée, CONCERNS sur le scope restent ouverts.",
        MARKERS) is True


# --- Garde-fous : ce qui doit rester VIVANT (niveau marqueur) -------------

def test_posed_temporal_still_live_and_blocks():
    """Le marqueur POSE (pas d'apposition de levee) reste une reserve,
    au niveau marqueur ET au niveau classify."""
    body = "Le scope des notebooks est a revoir avant merge."
    assert mod.has_live_marker(body, MARKERS) is True
    assert mod.classify("jsboige", body) == "BOT-CONCERN"


def test_negated_lift_before_merge_stays_dead_as_before():
    """« n'est pas leve avant merge » : deja morte sur main via _is_cited
    (negation dans la fenetre de citation) — le fix ne l'affaiblit ni ne
    la renforce : elle reste morte, sans ponctuation d'apposition."""
    assert mod.has_live_marker("Le point 2 n'est pas leve avant merge.", MARKERS) is False


def test_infinitive_lever_before_merge_still_live():
    """L'infinitif (« a lever avant merge ») est une EXIGENCE : le lexeme
    \\bleve(?:e|es)?\\b ne matche pas « lever »."""
    assert mod.has_live_marker("Il reste un point a lever avant merge.", MARKERS) is True


def test_participle_without_punctuation_still_live():
    """Residu assume (#15651, sur-bloquant donc sans danger) : participe
    SANS ponctuation — la virgule est le discriminant qui separe le
    timing d'une negation voisine ; sans elle on ne neutralise pas."""
    assert mod.has_live_marker("Le point 3 doit etre leve avant merge.", MARKERS) is True


# --- Comportement : la phrase de levee ne bloque PLUS toute seule ---------

def test_lift_timing_no_longer_adds_a_spurious_concern():
    """Delta comportemental mesure sur le scenario fondateur : avant le
    fix, la phrase de levee etait une 2e entree BLOCKING ; apres, elle ne
    bloque plus (elle part en `unevaluated`, advisory). Le nit reel de
    19 h reste, lui, bien bloque — ce grain ne touche pas a la detection
    de levée (« voici sa levée » n'est pas un lexeme reconnu par
    has_live_lift : gap preexistant, hors scope)."""
    at = lambda h: f"2026-09-11T{h:02d}:00:00Z"  # noqa: E731
    MERGED = datetime(2026, 9, 11, 23, 0, tzinfo=timezone.utc)
    data = {
        "number": 15648,
        "title": "t",
        "author": {"login": "jsboige"},
        "comments": [
            {"author": {"login": "jsboige"}, "createdAt": at(19),
             "body": "Attention : il va falloir revoir l'attribution."},
            {"author": {"login": "myia-ai-01"}, "createdAt": at(21),
             "body": FOUNDER_LIFT},
        ],
        "reviews": [],
        "commits": [{"committedDate": at(19)}],
    }
    result = mod.analyse(data, [], MERGED)
    assert result["blocked"] is True
    assert len(result["blocking"]) == 1
    assert result["blocking"][0]["author"] == "jsboige"
