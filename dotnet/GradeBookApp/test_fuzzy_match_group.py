"""Tests for GradeBookApp/gradebook.py::fuzzy_match_group.

Guards its heavy deps (pandas/rapidfuzz/...) via ``pytest.importorskip`` so the
suite skips cleanly in CI (no GradeBookApp Python env) but runs on any machine
that has the grading-engine deps installed.

Covers the regression fixed alongside this test: commit 3a612f85c wired a
configurable ``group_match_threshold`` and a 3-arg call site (gradebook.py
l.1137) but never updated ``fuzzy_match_group``'s signature -- so the 3-arg
call raised ``TypeError`` and the threshold was dead config. The fix restores
the author's documented intent via a backward-compatible ``threshold=90``
default.
"""
import os
import sys

import pytest

# Make ``gradebook`` (sibling file) importable regardless of invocation cwd,
# since the repo root pytest.ini uses ``--import-mode importlib`` and does not
# put GradeBookApp/ on sys.path.
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

pd = pytest.importorskip("pandas")
pytest.importorskip("rapidfuzz")

from gradebook import fuzzy_match_group  # noqa: E402  (after importorskip guards)


def test_three_arg_call_no_longer_crashes():
    """Regression: l.1137 passes 3 args; the old 2-param signature raised TypeError."""
    # Exact pair -> Cas 1 -> True, at any threshold. Point: 3-arg call must be callable.
    assert fuzzy_match_group("projet alpha", "projet alpha", 90) is True
    assert fuzzy_match_group("projet alpha", "projet alpha", 100) is True


def test_threshold_governs_cas2_borderline():
    """Cas 2 admission follows the configurable threshold, not a hardcoded 90.
    Derives the assertion from the actual fuzz ratio (no brittle magic number)."""
    from rapidfuzz import fuzz

    a = "projet machine learning"
    b = "projet machine learnig"  # 1-char typo -> ratio < 100, reaches Cas 2
    ratio = fuzz.ratio(a, b)
    assert ratio < 100, "fixture must not be exact (would short-circuit at Cas 1)"
    assert 50 < ratio < 100, f"fixture ratio {ratio} outside the expected band"
    # Admitted at/under the measured ratio, rejected strictly above it.
    assert fuzzy_match_group(a, b, threshold=int(ratio)) is True
    assert fuzzy_match_group(a, b, threshold=100) is False


def test_two_arg_backward_compat_default_90():
    """Existing 2-arg callers (l.742, l.853) keep the historical default-90 behavior."""
    a = "projet machine learning"
    b = "projet machine learnig"
    assert fuzzy_match_group(a, b) == fuzzy_match_group(a, b, 90)


def test_cas0_distinct_group_codes_never_match():
    """Cas 0 dominates: distinct leading codes must not match, even at a low threshold."""
    assert fuzzy_match_group("a1 - projet", "a2 - projet", threshold=10) is False
    # Same code matches regardless of a strict threshold.
    assert fuzzy_match_group("a1 - projet", "a1 - projet", threshold=100) is True


# --- Gate d'ambiguité (issue #8606, PRIVACY.md §6) -------------------------


@pytest.fixture
def journal():
    """Journal isolé, pour ne pas dépendre du journal de module partagé."""
    from gradebook import AmbiguityJournal

    return AmbiguityJournal()


def _borderline_pair():
    """Paire dont le ratio tombe strictement entre 50 et 100 (atteint le Cas 2)."""
    from rapidfuzz import fuzz

    a, b = "projet machine learning", "projet machine learnig"
    ratio = fuzz.ratio(a, b)
    assert 50 < ratio < 100, f"fixture ratio {ratio} hors bande attendue"
    return a, b, ratio


def test_score_in_band_is_recorded_but_still_refused(journal):
    """Bande d'ambiguité : consignée pour arbitrage, et **non créditée** (§6 règle 4)."""
    a, b, ratio = _borderline_pair()
    # Seuil juste au-dessus du ratio -> refus, et score dans [seuil - marge, seuil[.
    threshold = int(ratio) + 1
    assert fuzzy_match_group(a, b, threshold, journal=journal) is False
    assert len(journal) == 1, "le litige doit être consigné"
    entry = journal.entries[0]
    assert entry["decision"] == "non_credite_arbitrage_requis"
    assert entry["seuil"] == threshold


def test_score_below_band_is_not_recorded(journal):
    """Sous la bande : refus franc, rien à arbitrer — le journal reste vide."""
    # Deux libellés très dissemblables : ratio loin sous (seuil - marge).
    assert fuzzy_match_group("alpha", "zzzzzzzzzzzz", 90, journal=journal) is False
    assert len(journal) == 0


def test_accepted_match_is_not_recorded(journal):
    """Au-dessus du seuil : accepté, donc hors bande d'ambiguité."""
    assert fuzzy_match_group("projet alpha", "projet alpha", 90, journal=journal) is True
    assert len(journal) == 0


def test_journal_holds_no_nominative_data(journal):
    """PRIVACY.md §5 : le journal ne porte que des condensés, jamais les libellés."""
    a, b, ratio = _borderline_pair()
    fuzzy_match_group(a, b, int(ratio) + 1, journal=journal)
    serialized = str(journal.entries)
    assert a not in serialized and b not in serialized
    assert "machine" not in serialized and "learning" not in serialized
    # Condensé stable et tronqué (non réversible par simple lecture).
    assert len(journal.entries[0]["groupe_evalue"]) == 12


def test_two_close_students_neither_credited(journal):
    """§6 règle 4 : confusion entre deux étudiants -> aucun crédité automatiquement."""
    evaluation = "projet vision par ordinateur - dupont"
    student_a = "projet vision par ordinateur - dupond"   # noms quasi identiques
    student_b = "projet vision par ordinateur - dupontt"

    matched = [s for s in (student_a, student_b)
               if fuzzy_match_group(evaluation, s, threshold=100, journal=journal)]

    assert matched == [], "aucun des deux étudiants ne doit être crédité automatiquement"
    assert journal.has_ambiguities, "la confusion doit être tracée pour arbitrage"


def test_cas4_inclusion_still_matches_on_token_boundary():
    """Cas 4 conserve son intention : un libellé étendu par un segment distinct
    reste le même projet (« projet alpha » ⊂ « projet alpha - groupe 3 »)."""
    assert fuzzy_match_group(
        "projet alpha", "projet alpha - groupe 3", threshold=100, journal=False) is True


def test_cas4_glued_inclusion_no_longer_bypasses_threshold():
    """Régression : « ... dupont » ⊂ « ... dupontt » n'est pas une inclusion de
    projet mais une confusion de patronymes. Cas 4 court-circuitait le seuil et
    créditait automatiquement l'un des deux (PRIVACY.md §6 règle 4)."""
    assert fuzzy_match_group(
        "projet vision - dupont", "projet vision - dupontt",
        threshold=100, journal=False) is False


def test_journal_false_disables_recording():
    """``journal=False`` coupe tout enregistrement (appels utilitaires, sondes)."""
    from gradebook import get_ambiguity_journal, reset_ambiguity_journal

    reset_ambiguity_journal()
    a, b, ratio = _borderline_pair()
    assert fuzzy_match_group(a, b, int(ratio) + 1, journal=False) is False
    assert len(get_ambiguity_journal()) == 0
    reset_ambiguity_journal()


def test_default_journal_used_when_unspecified():
    """Sans ``journal``, le journal de module reçoit le litige : le gate est actif
    par défaut, sans câblage par l'appelant."""
    from gradebook import get_ambiguity_journal, reset_ambiguity_journal

    reset_ambiguity_journal()
    a, b, ratio = _borderline_pair()
    fuzzy_match_group(a, b, int(ratio) + 1)
    assert len(get_ambiguity_journal()) == 1
    reset_ambiguity_journal()
    assert len(get_ambiguity_journal()) == 0


def test_write_produces_json_without_nominative_data(tmp_path, journal):
    """Le journal écrit est un JSON exploitable, sans PII."""
    import json

    a, b, ratio = _borderline_pair()
    fuzzy_match_group(a, b, int(ratio) + 1, journal=journal)
    target = tmp_path / "ambiguites.json"
    assert journal.write(str(target)) == str(target)

    payload = json.loads(target.read_text(encoding="utf-8"))
    assert payload["nb_rapprochements_ambigus"] == 1
    assert a not in target.read_text(encoding="utf-8")


def test_write_returns_none_when_no_ambiguity(tmp_path, journal):
    """Rien à arbitrer -> aucun fichier créé (pas de journal vide qui traîne)."""
    target = tmp_path / "ambiguites.json"
    assert journal.write(str(target)) is None
    assert not target.exists()
