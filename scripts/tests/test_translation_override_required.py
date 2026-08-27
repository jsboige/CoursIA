#!/usr/bin/env python3
"""Unit tests for ``translation_override_required.py`` (#10332).

The script is a pure decision over (labels, comments) -> verdict. Fetchers are
default ``gh``-based and injectable; these tests pass dict-based fixtures so
the test runner never touches the network.

Coverage map (mirrors the acceptance criteria of #10332):
  - test_override_pass_label_and_marker       : pass / override_applied True
  - test_override_fail_label_only             : label present, no marker -> fail
  - test_override_fail_marker_only            : marker present, no label -> fail
  - test_override_fail_neither                : nothing -> fail (cliquet)
  - test_override_fail_empty_motif            : marker present but empty motif
  - test_override_pass_picks_first_marker     : multiple markers -> first wins
  - test_override_motif_extraction            : regex anchoring (not in prose)
  - test_override_label_case_sensitive        : case-sensitive label match
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from ci.translation_override_required import (  # noqa: E402
    OVERRIDE_LABEL,
    _extract_marker,
    check,
)


def test_override_pass_label_and_marker():
    """Dual-key satisfied: pass with the motif journalised in the verdict."""
    verdict = check(
        pr_number=999,
        comment_bodies=["[TRANSLATION-OVERRIDE] hand-edit finetuning.csv ligne 42-44\n"],
        label_names=[OVERRIDE_LABEL, "other-label"],
    )
    assert verdict["guard_pass"] is True, verdict
    assert verdict["override_applied"] is True
    assert verdict["label_present"] is True
    assert verdict["marker_present"] is True
    assert verdict["motif"] == "hand-edit finetuning.csv ligne 42-44"


def test_override_fail_label_only():
    """Label without marker: the dual-key is unsatisfied -> fail."""
    verdict = check(
        pr_number=999,
        comment_bodies=["This is just a comment without the marker."],
        label_names=[OVERRIDE_LABEL],
    )
    assert verdict["guard_pass"] is False
    assert verdict["override_applied"] is False
    assert verdict["label_present"] is True
    assert verdict["marker_present"] is False
    assert verdict["motif"] is None
    assert "label" in verdict["reason"].lower()
    assert "marker" in verdict["reason"].lower()


def test_override_fail_marker_only():
    """Marker without label: dual-key unsatisfied -> fail."""
    verdict = check(
        pr_number=999,
        comment_bodies=["[TRANSLATION-OVERRIDE] legitimate override #10299"],
        label_names=["unrelated-label"],
    )
    assert verdict["guard_pass"] is False
    assert verdict["override_applied"] is False
    assert verdict["label_present"] is False
    assert verdict["marker_present"] is True
    assert verdict["motif"] == "legitimate override #10299"
    assert "label" in verdict["reason"].lower()


def test_override_fail_neither():
    """No label, no marker: cliquet non disarmé -> fail (criterion 4 of #10332)."""
    verdict = check(
        pr_number=999,
        comment_bodies=["Some unrelated comment", "Another one"],
        label_names=["random-label"],
    )
    assert verdict["guard_pass"] is False
    assert verdict["override_applied"] is False
    assert verdict["label_present"] is False
    assert verdict["marker_present"] is False
    assert verdict["motif"] is None


def test_override_fail_empty_motif():
    """A marker line whose motif is whitespace-only: fail (no journalable decision)."""
    verdict = check(
        pr_number=999,
        comment_bodies=["[TRANSLATION-OVERRIDE]    \n"],
        label_names=[OVERRIDE_LABEL],
    )
    # The regex requires \S after the marker -- a whitespace-only motif does
    # not match. marker_present should be False; dual-key unsatisfied -> fail.
    assert verdict["guard_pass"] is False
    assert verdict["override_applied"] is False
    assert verdict["marker_present"] is False


def test_override_pass_picks_first_marker():
    """Two marker comments: the FIRST one is the override decision."""
    verdict = check(
        pr_number=999,
        comment_bodies=[
            "[TRANSLATION-OVERRIDE] first decision (motif A)",
            "[TRANSLATION-OVERRIDE] second decision (motif B)",
        ],
        label_names=[OVERRIDE_LABEL],
    )
    assert verdict["guard_pass"] is True
    assert verdict["motif"] == "first decision (motif A)"


def test_override_motif_extraction():
    """The marker must appear on its own LINE -- mid-prose markers do not count."""
    # The regex anchors with ^ + MULTILINE. A marker buried in prose does not
    # match because the line starts with prose text.
    body = (
        "Long paragraph that mentions [TRANSLATION-OVERRIDE] in passing "
        "but the marker is not on its own line.\n"
    )
    assert _extract_marker(body) is None

    # But a marker on its own line, with leading whitespace tolerated, matches.
    body2 = "   [TRANSLATION-OVERRIDE]   motif with leading and trailing\n"
    assert _extract_marker(body2) == "motif with leading and trailing"


def test_override_label_case_sensitive():
    """Label match is case-sensitive -- 'Translation-Override' != 'translation-override'."""
    verdict = check(
        pr_number=999,
        comment_bodies=["[TRANSLATION-OVERRIDE] motif"],
        label_names=["Translation-Override"],  # capitalised, NOT the canonical form
    )
    assert verdict["guard_pass"] is False
    assert verdict["label_present"] is False
    assert verdict["marker_present"] is True


def test_12773_translation_guard_paths_filter_includes_translations_dir():
    """Miroir du paths-filter de `translation-guard.yml` (#12773 tranche 1b,
    amende par Hermes REQUEST_CHANGES sur #13196) : le filtre DOIT inclure
    `translations/**`, sinon le garde est desarme sur sa cible principale
    (Hermes a compte 86 fichiers `translations/**` sur `main`). Les fichiers
    rendus `*_<lang>.ipynb` doivent aussi etre couverts ; la coquille
    `_fa.pdf` doit etre `_fa.ipynb`. Le filtre ne doit PLUS mentionner
    `MyIA.AI.Notebooks/**/translation_*.csv` (matche 0 fichier sur `main`,
    entree inerte qui masque le gap reel).

    Verrou : parse le YAML, assert inclusion / exclusion / absence de
    coquille. Si un futur editeur reintroduit l'une des trois deviations,
    ce test rougit.
    """
    import re
    from pathlib import Path

    wf_path = (
        Path(__file__).resolve().parent.parent.parent
        / ".github" / "workflows" / "translation-guard.yml"
    )
    text = wf_path.read_text(encoding="utf-8")

    # Extract the `paths:` block under `pull_request`
    pull_req_block = re.search(
        r"pull_request:\s*\n(?P<inner>(?:[ ]+[^\n]+\n)+)workflow_dispatch",
        text,
    )
    assert pull_req_block, "Le bloc pull_request doit exister dans translation-guard.yml"
    inner = pull_req_block.group("inner")
    paths_block = re.search(
        r"paths:\s*\n((?:[ \t]+-[^\n]+\n)+)",
        inner,
    )
    assert paths_block, "Le paths-filter doit exister sous pull_request"
    normalized = " ".join(line.strip() for line in paths_block.group(1).splitlines())

    # Acceptance #1 — translations/** present (Hermes ecart principal)
    assert "translations/**" in normalized, (
        f"`translations/**` absent du paths-filter — Hermes ecart #1 "
        f"(86 fichiers derives sur main). Restoration requise. Observed: {normalized!r}"
    )

    # Acceptance #2 — *_<lang>.ipynb presents, _fa.pdf est une coquille
    for lang in ("en", "es", "ar", "zh", "ru", "pt"):
        assert f"*_{lang}.ipynb" in normalized, (
            f"`MyIA.AI.Notebooks/**/*_{lang}.ipynb` absent du paths-filter. "
            f"Rend de cette langue non couvert. Observed: {normalized!r}"
        )
    assert "*_fa.ipynb" in normalized, (
        f"`*_fa.ipynb` absent — Hermes a releve une coquille `_fa.pdf` "
        f"qui ne matche aucun fichier sur main. Observed: {normalized!r}"
    )
    # Coquille inversee : _fa.pdf NE doit PAS etre present
    assert "*_fa.pdf" not in normalized, (
        f"Coquille `*_fa.pdf` toujours presente (Hermes ecart #3). "
        f"Corrigez en `*_fa.ipynb`. Observed: {normalized!r}"
    )

    # Acceptance #3 — translation_*.csv sous notebooks doit etre absent
    # (Hermes a compte 0 fichier `MyIA.AI.Notebooks/**/translation_*.csv`
    # sur main ; entree inerte qui masque le gap reel)
    assert "MyIA.AI.Notebooks/**/translation_*.csv" not in normalized, (
        f"`MyIA.AI.Notebooks/**/translation_*.csv` toujours present — Hermes "
        f"ecart #2 (matche 0 fichier sur main, entree inerte). Retirer. "
        f"Observed: {normalized!r}"
    )
