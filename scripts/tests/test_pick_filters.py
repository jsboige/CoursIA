"""Tests for factual local filters in pick_idle_grain."""

from __future__ import annotations

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import pick_idle_grain as pig  # noqa: E402


def _item(
    number: int,
    *,
    labels: tuple[str, ...] = (),
    age: int = 10,
    idle: int = 5,
    klass: str = "grain",
) -> dict:
    return {
        "number": number,
        "title": f"Issue {number}",
        "labels": list(labels),
        "age": age,
        "idle": idle,
        "klass": klass,
    }


def test_csv_values_flattens_repeated_groups():
    assert pig._csv_values(["1, 2", "3", " ,4,"]) == ["1", "2", "3", "4"]


def test_require_labels_is_case_insensitive_and_requires_all():
    items = [
        _item(1, labels=("Bug", "Security")),
        _item(2, labels=("bug",)),
    ]
    kept, funnel = pig.filter_candidates(
        items, required_labels={"BUG", "security"}
    )
    assert [item["number"] for item in kept] == [1]
    assert funnel["excluded"] == {"require_label": 1}


def test_exclude_labels_uses_any_match_case_insensitively():
    items = [
        _item(1, labels=("Candidate-Delivered",)),
        _item(2, labels=("pedagogy", "blocked")),
        _item(3, labels=("pedagogy",)),
    ]
    kept, funnel = pig.filter_candidates(
        items, excluded_labels={"candidate-delivered", "BLOCKED"}
    )
    assert [item["number"] for item in kept] == [3]
    assert funnel["excluded"] == {"exclude_label": 2}


def test_age_and_idle_bounds_are_inclusive():
    items = [
        _item(1, age=3, idle=2),
        _item(2, age=5, idle=4),
        _item(3, age=8, idle=7),
    ]
    kept, funnel = pig.filter_candidates(
        items,
        min_age_days=3,
        max_age_days=5,
        min_idle_days=2,
        max_idle_days=4,
    )
    assert [item["number"] for item in kept] == [1, 2]
    assert funnel["excluded"] == {"max_age_days": 1}


def test_issue_exclusions_precede_other_filter_counts():
    items = [_item(1, age=1), _item(2, age=1), _item(3, age=10)]
    kept, funnel = pig.filter_candidates(
        items,
        exclude_issues={1},
        min_age_days=5,
    )
    assert [item["number"] for item in kept] == [3]
    assert funnel["excluded"] == {
        "exclude_issue": 1,
        "min_age_days": 1,
    }
    assert funnel["initial"] == funnel["final"] + funnel["excluded_total"]
    assert sum(funnel["excluded"].values()) == funnel["excluded_total"]


def test_urn_filter_and_final_population_counts():
    items = [
        _item(1, klass="grain"),
        _item(2, klass="umbrella"),
        _item(3, klass="delivered"),
    ]
    kept, funnel = pig.filter_candidates(items, urns={"umbrella", "delivered"})
    assert [item["number"] for item in kept] == [2, 3]
    assert funnel["excluded"] == {"urns": 1}
    assert funnel["by_urn"] == {
        "delivered": 1,
        "grain": 0,
        "umbrella": 1,
    }


def test_empty_result_names_all_exclusions_without_claiming_empty_pool():
    items = [_item(1), _item(2)]
    kept, funnel = pig.filter_candidates(items, exclude_issues={1, 2})
    assert kept == []
    assert funnel["initial"] == 2
    assert funnel["final"] == 0
    assert funnel["excluded"] == {"exclude_issue": 2}
    assert funnel["examples"] == {"exclude_issue": [1, 2]}


def test_narrow_local_filters_fail_open_to_a_bounded_second_pass():
    items = [_item(1, labels=("pedagogy",), age=30)]
    kept, funnel = pig.filter_candidates_with_continuity(
        items, required_labels={"missing"}, min_age_days=90)
    assert [item["number"] for item in kept] == [1]
    assert funnel["fell_back"] is True
    assert funnel["first_pass"]["final"] == 0
    assert funnel["final"] == 1
    assert funnel["fallback_final"] == 1
    assert funnel["by_urn"]["grain"] == 1
    assert funnel["excluded_total"] == 0
    requested = pig.requested_filter_funnel(funnel)
    assert requested["excluded"] == {"require_label": 1}
    assert requested["final"] == 0


def test_requested_filter_funnel_preserves_non_fallback_contract():
    items = [_item(1), _item(2, age=1)]
    _, funnel = pig.filter_candidates_with_continuity(
        items, min_age_days=5)
    assert funnel["fell_back"] is False
    assert pig.requested_filter_funnel(funnel) is funnel
    assert pig.requested_filter_funnel(funnel)["excluded"] == {
        "min_age_days": 1,
    }


def test_continuity_fallback_keeps_explicit_exclusions_and_urn_gate():
    items = [_item(1), _item(2, klass="delivered"), _item(3)]
    kept, funnel = pig.filter_candidates_with_continuity(
        items,
        exclude_issues={1},
        required_labels={"missing"},
        urns={"grain"},
    )
    assert [item["number"] for item in kept] == [3]
    assert funnel["fell_back"] is True
    assert 1 not in {item["number"] for item in kept}
    assert 2 not in {item["number"] for item in kept}


@pytest.mark.parametrize(
    "extra",
    [
        ["--min-age-days", "5", "--max-age-days", "4"],
        ["--min-idle-days", "-1"],
        ["--urns", "grain,unknown"],
        ["--exclude-issue", "not-a-number"],
        ["--write-state", "merged"],
    ],
)
def test_cli_rejects_invalid_filter_arguments(extra):
    with pytest.raises(SystemExit) as exc:
        pig.main(["--lane", "test:CoursIA", *extra])
    assert exc.value.code == 2
