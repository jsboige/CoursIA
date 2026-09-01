#!/usr/bin/env python3
"""Regression tests for the read-only EPIC body staleness analyzer."""

from __future__ import annotations

import importlib.util
import json
import sys
from pathlib import Path

import pytest

_SCRIPT = Path(__file__).resolve().parent.parent / "epic_body_staleness.py"
_SPEC = importlib.util.spec_from_file_location("epic_body_staleness", _SCRIPT)
assert _SPEC and _SPEC.loader
_MODULE = importlib.util.module_from_spec(_SPEC)
sys.modules[_SPEC.name] = _MODULE
_SPEC.loader.exec_module(_MODULE)

Epic = _MODULE.Epic
MergedPullRequest = _MODULE.MergedPullRequest
analyze_epics = _MODULE.analyze_epics
build_payload = _MODULE.build_payload


def _pr(number: int, body: str, *, title: str = "delivery") -> MergedPullRequest:
    return MergedPullRequest(
        number=number,
        title=title,
        body=body,
        merged_at=f"2026-08-{number % 28 + 1:02d}T12:00:00Z",
    )


def test_1210_before_correction_triggers_both_signals():
    """Positive control from #13906: stale stance plus unrecorded delivery."""
    epic = Epic(
        1210,
        "[Epic / priority-low / background] Semantic fleet",
        "Pas pour maintenant.\n\n## Objectif\nConstruire la flotte.",
    )
    finding = analyze_epics(
        [epic],
        [_pr(6542, "See #1210"), _pr(5672, "Part of #1210")],
    )[0]

    assert finding.number == 1210
    assert finding.unrecorded_merged == (6542, 5672)
    assert finding.stance_contradicted is True
    assert finding.stance_pattern == "pas pour maintenant"


def test_up_to_date_epic_has_no_signal():
    epic = Epic(
        42,
        "[EPIC] Runtime",
        "## Livré\n- #101 — runtime initial\n- #102 — tests",
    )

    assert analyze_epics(
        [epic],
        [_pr(101, "See #42"), _pr(102, "See #42")],
    ) == []


def test_quoted_dormant_stance_is_not_live():
    epic = Epic(
        1210,
        "[EPIC] Semantic fleet",
        (
            "> Pas pour maintenant.\n\n"
            "Cette ancienne posture est désormais dépassée.\n"
            "Livré : #6542."
        ),
    )

    assert analyze_epics([epic], [_pr(6542, "See #1210")]) == []


@pytest.mark.parametrize(
    "correction",
    [
        "Statut corrigé : ce fut un oubli, pas une position.",
        "Statut corrigé. Ce n'était pas une position, juste un oubli.",
    ],
)
def test_explicit_corrected_status_overrides_preserved_historical_prose(correction):
    epic = Epic(
        1210,
        "[EPIC] Semantic fleet",
        (
            f"**{correction}**\n\n"
            "**Pas pour maintenant.** Texte historique conservé.\n"
            "Livré : #6542."
        ),
    )

    assert analyze_epics([epic], [_pr(6542, "See #1210")]) == []


@pytest.mark.parametrize(
    ("body", "expected"),
    [
        ("## Statut : BACKLOG INDEXÉ", "backlog indexé"),
        ("Cette issue n'est pas à démarrer.", "ne pas démarrer"),
        ("Une issue à ouvrir, pas forcément à traiter maintenant.", "pas à traiter maintenant"),
    ],
)
def test_strong_dormant_statuses_are_detected(body, expected):
    epic = Epic(7265, "[EPIC] Heritage", body)

    finding = analyze_epics([epic], [_pr(13466, "See #7265")])[0]

    assert finding.stance_contradicted is True
    assert finding.stance_pattern == expected


def test_quoted_and_code_passages_do_not_recreate_dormant_stance():
    epic = Epic(
        7,
        "[EPIC] Active",
        (
            "La chaîne `priority-low` documente l'ancien label.\n"
            "> Contexte historique :\n"
            "en veille depuis 2025, sans action.\n\n"
            "~~~text\nplus tard\n~~~\n"
            "    pas pour maintenant\n"
            "Livré : #70."
        ),
    )

    assert analyze_epics([epic], [_pr(70, "See #7")]) == []


def test_broad_words_require_declarative_status_context():
    epic = Epic(
        8,
        "[EPIC] Active",
        (
            "Le worker tourne en background pendant le build.\n"
            "Les métriques détaillées arrivent plus tard dans ce document.\n"
            "Livré : #80."
        ),
    )

    assert analyze_epics([epic], [_pr(80, "See #8")]) == []


def test_contextual_status_and_pattern_variants_are_detected():
    epics = [
        Epic(8, "[EPIC / priority: low] Active", ""),
        Epic(9, "[EPIC] Indexed", "## Statut : backlog indexées"),
    ]
    prs = [_pr(80, "See #8"), _pr(90, "See #9")]

    findings = analyze_epics(epics, prs)

    assert findings[0].stance_pattern == "priority-low"
    assert findings[1].stance_pattern == "backlog indexé"


def test_unrecorded_pr_list_is_sorted_and_finding_order_is_triageable():
    epics = [
        Epic(1, "[EPIC] One", ""),
        Epic(2, "[EPIC / plus tard] Two", ""),
        Epic(3, "[EPIC] Three", ""),
    ]
    prs = [
        _pr(15, "See #1 and #2"),
        _pr(12, "See #1"),
        _pr(20, "See #1"),
        _pr(11, "See #3"),
    ]

    findings = analyze_epics(epics, prs)

    assert [finding.number for finding in findings] == [1, 2, 3]
    assert findings[0].unrecorded_merged == (20, 15, 12)
    assert findings[1].stance_contradicted is True


def test_incidental_citation_remains_visible_as_signal_not_verdict():
    epic = Epic(42, "[EPIC] Target", "")
    finding = analyze_epics(
        [epic],
        [_pr(900, "Unrelated delivery; compare the process in #42")],
    )[0]

    assert finding.unrecorded_merged == (900,)


def test_payload_reports_corpus_even_when_findings_are_empty():
    epic = Epic(42, "[EPIC] Current", "Delivered by #101")
    pr = _pr(101, "See #42")

    payload = build_payload([epic], [pr])

    assert payload["finding_count"] == 0
    assert payload["findings"] == []
    assert payload["corpus"] == {
        "open_epics_examined": 1,
        "merged_prs_examined": 1,
        "merged_window_start": pr.merged_at,
        "merged_window_end": pr.merged_at,
    }
    assert "read-only" in payload["limitations"][3]


def test_is_epic_accepts_title_or_label_and_rejects_plain_issue():
    assert _MODULE.is_epic({"title": "[EPIC] X", "labels": []})
    assert _MODULE.is_epic({"title": "EPIC: X", "labels": []})
    assert _MODULE.is_epic({"title": "Tracker", "labels": [{"name": "EPIC"}]})
    assert _MODULE.is_epic({"title": "Tracker", "labels": [{"name": "epic-ict"}]})
    assert not _MODULE.is_epic({"title": "Epictetus notes", "labels": []})
    assert not _MODULE.is_epic({"title": "Regular issue", "labels": []})


def test_list_merged_prs_sorts_by_merge_time_before_trimming(monkeypatch):
    rows = [
        {
            "number": 1,
            "title": "old creation, latest merge",
            "body": "",
            "mergedAt": "2026-09-01T12:00:00Z",
        },
        {
            "number": 2,
            "title": "new creation, earlier merge",
            "body": "",
            "mergedAt": "2026-08-31T12:00:00Z",
        },
        {
            "number": 3,
            "title": "oldest merge",
            "body": "",
            "mergedAt": "2026-08-30T12:00:00Z",
        },
    ]
    monkeypatch.setattr(_MODULE, "_merged_pr_slice", lambda repo, since, until: rows)

    prs = _MODULE.list_merged_prs("example/repo", 2)

    assert [pr.number for pr in prs] == [1, 2]


def test_merged_slice_halves_a_capped_window(monkeypatch):
    calls = []

    def fake_gh(args):
        search = args[args.index("--search") + 1]
        calls.append(search)
        if "merged:>=2026-08-28 merged:<2026-09-01" in search:
            return [{"number": n} for n in range(_MODULE.SEARCH_RESULT_CAP)]
        return []

    monkeypatch.setattr(_MODULE, "_gh_json", fake_gh)

    rows = _MODULE._merged_pr_slice(
        "example/repo",
        _MODULE.date(2026, 8, 28),
        _MODULE.date(2026, 9, 1),
    )

    assert rows == []
    assert len(calls) == 3


def test_cli_prints_json_and_never_writes(monkeypatch, capsys):
    epic = Epic(42, "[EPIC] Current", "Delivered by #101")
    pr = _pr(101, "See #42")
    monkeypatch.setattr(_MODULE, "list_open_epics", lambda repo: [epic])
    monkeypatch.setattr(_MODULE, "list_merged_prs", lambda repo, limit: [pr])

    assert _MODULE._cli(["--repo", "example/repo", "--pretty"]) == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["corpus"]["open_epics_examined"] == 1


def test_cli_reports_read_failure(monkeypatch, capsys):
    def fail(_repo):
        raise RuntimeError("GitHub unavailable")

    monkeypatch.setattr(_MODULE, "list_open_epics", fail)

    assert _MODULE._cli(["--repo", "example/repo"]) == 1
    assert "GitHub unavailable" in capsys.readouterr().err


def test_cli_rejects_nonpositive_limit(capsys):
    with pytest.raises(SystemExit) as exc:
        _MODULE._cli(["--pr-limit", "0"])

    assert exc.value.code == 2
    assert "--pr-limit must be positive" in capsys.readouterr().err
