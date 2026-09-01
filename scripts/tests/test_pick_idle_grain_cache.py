"""Tests for the bounded raw-payload cache used by pick_idle_grain."""

from __future__ import annotations

import json
import os
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from gh_payload_cache import (  # noqa: E402
    PayloadCache,
    cache_key,
    default_cache_dir,
)
import pick_idle_grain as pig  # noqa: E402
import series_saturation as series  # noqa: E402


def test_cache_key_changes_with_query_and_repository():
    first = cache_key("owner/repo", "pool", ["gh", "issue", "list"])
    assert first == cache_key("owner/repo", "pool", ["gh", "issue", "list"])
    assert first != cache_key("owner/repo", "pool", ["gh", "pr", "list"])
    assert first != cache_key("other/repo", "pool", ["gh", "issue", "list"])


def test_default_cache_dir_uses_localappdata_on_windows(monkeypatch, tmp_path):
    monkeypatch.setenv("LOCALAPPDATA", str(tmp_path))
    assert default_cache_dir("nt") == tmp_path / "CoursIA" / "cache" / "pick_idle_grain"


def test_miss_then_hit_does_not_refetch(tmp_path):
    now = [100.0]
    calls = []
    cache = PayloadCache(tmp_path, clock=lambda: now[0])

    def fetch():
        calls.append(True)
        return [{"number": 1}]

    first = cache.get_or_fetch("pool", 60, fetch)
    now[0] = 120.0
    second = cache.get_or_fetch("pool", 60, fetch)
    assert first.status == "miss"
    assert second.status == "hit"
    assert second.payload == first.payload
    assert second.age_seconds == 20.0
    assert len(calls) == 1


def test_expired_entry_is_refetched(tmp_path):
    now = [100.0]
    cache = PayloadCache(tmp_path, clock=lambda: now[0])
    values = iter([[1], [2]])
    assert cache.get_or_fetch("pool", 10, lambda: next(values)).payload == [1]
    now[0] = 111.0
    result = cache.get_or_fetch("pool", 10, lambda: next(values))
    assert result.status == "miss"
    assert result.payload == [2]


def test_refresh_forces_fetch_even_when_entry_is_fresh(tmp_path):
    now = [100.0]
    cache = PayloadCache(tmp_path, clock=lambda: now[0])
    cache.get_or_fetch("pool", 60, lambda: [1])
    now[0] = 101.0
    result = cache.get_or_fetch("pool", 60, lambda: [2], mode="refresh")
    assert result.status == "refresh"
    assert result.payload == [2]


def test_off_bypasses_all_disk_io(tmp_path):
    cache = PayloadCache(tmp_path)
    result = cache.get_or_fetch("pool", 60, lambda: [1], mode="off")
    assert result.status == "bypass"
    assert result.payload == [1]
    assert list(tmp_path.iterdir()) == []


def test_stale_fallback_is_explicit_after_fetch_failure(tmp_path):
    now = [100.0]
    cache = PayloadCache(tmp_path, clock=lambda: now[0])
    cache.get_or_fetch("pool", 10, lambda: [1])
    now[0] = 200.0

    def fail():
        raise RuntimeError("GitHub unavailable")

    result = cache.get_or_fetch("pool", 10, fail)
    assert result.status == "stale"
    assert result.payload == [1]
    assert result.age_seconds == 100.0
    assert result.error == "RuntimeError: GitHub unavailable"
    assert result.as_dict()["status"] == "stale"


def test_fetch_failure_without_stale_entry_propagates(tmp_path):
    cache = PayloadCache(tmp_path)
    with pytest.raises(RuntimeError, match="offline"):
        cache.get_or_fetch("pool", 10, lambda: (_ for _ in ()).throw(RuntimeError("offline")))


def test_corrupt_entry_is_treated_as_miss_and_replaced(tmp_path):
    (tmp_path / "pool.json").write_text("{broken", encoding="utf-8")
    cache = PayloadCache(tmp_path, clock=lambda: 100.0)
    result = cache.get_or_fetch("pool", 60, lambda: {"fresh": True})
    assert result.status == "miss"
    assert result.payload == {"fresh": True}
    envelope = json.loads((tmp_path / "pool.json").read_text(encoding="utf-8"))
    assert envelope["payload"] == {"fresh": True}


def test_unwritable_cache_returns_fresh_payload_as_bypass(monkeypatch, tmp_path):
    cache = PayloadCache(tmp_path, clock=lambda: 100.0)

    def denied(*args, **kwargs):
        raise PermissionError("read-only cache")

    monkeypatch.setattr(cache, "_write", denied)
    result = cache.get_or_fetch("pool", 60, lambda: [1])
    assert result.status == "bypass"
    assert result.payload == [1]
    assert "PermissionError" in result.error


def test_retention_keeps_only_newest_entries(tmp_path):
    now = [100.0]
    cache = PayloadCache(tmp_path, max_entries=2, clock=lambda: now[0])
    for index in range(3):
        now[0] += 1
        cache.get_or_fetch(f"key-{index}", 60, lambda index=index: [index])
        os.utime(tmp_path / f"key-{index}.json", (now[0], now[0]))
    assert sorted(path.name for path in tmp_path.glob("*.json")) == [
        "key-1.json",
        "key-2.json",
    ]


def test_atomic_write_leaves_no_temp_files(tmp_path):
    cache = PayloadCache(tmp_path, clock=lambda: 100.0)
    cache.get_or_fetch("pool", 60, lambda: [1])
    assert [path.name for path in tmp_path.iterdir()] == ["pool.json"]


class _Completed:
    def __init__(self, payload):
        self.stdout = json.dumps(payload)
        self.returncode = 0


def test_three_shared_payloads_are_reused_without_changing_derivations(
    monkeypatch, tmp_path
):
    issue = {
        "number": 13920,
        "title": "perf: picker cache",
        "labels": [{"name": "performance"}],
        "body": "",
        "createdAt": "2026-08-01T00:00:00Z",
        "updatedAt": "2026-08-15T00:00:00Z",
    }
    visit_pr = {
        "number": 14000,
        "title": "perf(picker): cache (#13920)",
        "body": "See #13920",
        "mergedAt": "2026-09-01T00:00:00Z",
    }
    series_pr = {
        **visit_pr,
        "files": [{
            "path": "MyIA.AI.Notebooks/Search/Part4-Metaheuristics/demo.ipynb",
            "additions": 400,
            "deletions": 0,
        }],
    }
    calls = []

    def run(command, **kwargs):
        calls.append(command)
        fields = command[command.index("--json") + 1]
        if command[1:3] == ["issue", "list"]:
            return _Completed([issue])
        if "files" in fields:
            return _Completed([series_pr])
        return _Completed([visit_pr])

    monkeypatch.setattr(pig.subprocess, "run", run)
    monkeypatch.setattr(series.subprocess, "run", run)
    cache = PayloadCache(tmp_path, clock=lambda: 100.0)

    first_status = {}
    first = (
        pig.fetch_pool(cache=cache, cache_mode="auto", cache_status=first_status),
        pig.fetch_visits(cache=cache, cache_mode="auto", cache_status=first_status),
        series.fetch_series_visits(
            cache=cache, cache_mode="auto", cache_status=first_status
        ),
    )
    second_status = {}
    second = (
        pig.fetch_pool(cache=cache, cache_mode="auto", cache_status=second_status),
        pig.fetch_visits(cache=cache, cache_mode="auto", cache_status=second_status),
        series.fetch_series_visits(
            cache=cache, cache_mode="auto", cache_status=second_status
        ),
    )

    assert first == second
    assert len(calls) == 3
    assert {entry["status"] for entry in first_status.values()} == {"miss"}
    assert {entry["status"] for entry in second_status.values()} == {"hit"}
    assert first[1] == ({13920: 1}, None)
    zones, issue_to_family, error = first[2]
    assert error is None
    assert zones["MyIA.AI.Notebooks/Search/Part4-Metaheuristics"]["new_notebooks"] == 1
    assert issue_to_family[13920] == "MyIA.AI.Notebooks/Search/Part4-Metaheuristics"


def test_stale_visits_are_used_but_reported_as_unmeasured(monkeypatch, tmp_path):
    now = [100.0]
    cache = PayloadCache(tmp_path, clock=lambda: now[0])
    success = _Completed([{
        "number": 14000,
        "title": "See #13920",
        "body": "See #13920",
        "mergedAt": "2026-09-01T00:00:00Z",
    }])
    monkeypatch.setattr(pig.subprocess, "run", lambda *args, **kwargs: success)
    pig.fetch_visits(cache=cache, cache_mode="auto", cache_status={})
    now[0] += pig.VISITS_CACHE_TTL_SECONDS + 1

    def fail(*args, **kwargs):
        raise RuntimeError("GitHub unavailable")

    monkeypatch.setattr(pig.subprocess, "run", fail)
    status = {}
    counts, error = pig.fetch_visits(
        cache=cache, cache_mode="auto", cache_status=status
    )
    assert counts == {13920: 1}
    assert status["visits"]["status"] == "stale"
    assert "GitHub unavailable" in error
