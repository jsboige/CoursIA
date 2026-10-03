"""Tests for shadow_replay.py — frozen candidates, append-only CSV, local replay (#18923).

The decisive test is `test_replay_uses_frozen_code`: after freezing, the strategy file is edited
and committed again; the replay must still return the frozen version's numbers.
"""

from __future__ import annotations

import json
import subprocess
from pathlib import Path

import numpy as np
import pytest

from shadow_replay import (
    append_row,
    due,
    fingerprint,
    freeze,
    load_registry,
    load_rows,
    main,
    metrics,
    replay_local,
    save_registry,
    validate,
)

SHA = "a" * 40


def _frozen(**overrides) -> list[dict]:
    kw = dict(id="demo-v1", kind="local", sha=SHA, frozen_on="2026-10-01",
              entrypoint="strat.py:run", params={"level": 1}, fee_model="5bps notional")
    kw.update(overrides)
    candidates: list[dict] = []
    freeze(candidates, **kw)
    return candidates


def _row(candidate="demo-v1", pass_date="2026-11-02", sha=SHA, frozen_on="2026-10-01") -> dict:
    return {"candidate": candidate, "sha": sha, "frozen_on": frozen_on, "pass_date": pass_date,
            "period_end": pass_date, "n_days": 22, "sharpe_net": 0.5, "cagr": 0.01,
            "max_drawdown": -0.02, "turnover": 0.001, "fees": 0.0002,
            "fee_model": "5bps notional"}


# ---------------------------------------------------------------- registre

def test_freeze_records_fingerprint_and_refuses_duplicate_id():
    candidates = _frozen()
    assert candidates[0]["fingerprint"] == fingerprint(candidates[0])
    with pytest.raises(ValueError, match="new id"):
        freeze(candidates, id="demo-v1", kind="local", sha=SHA, frozen_on="2026-10-02",
               entrypoint="strat.py:run", params={}, fee_model="5bps notional")


def test_freeze_rejects_unknown_kind_and_bad_date():
    with pytest.raises(ValueError, match="kind"):
        _frozen(kind="paper")
    with pytest.raises(ValueError):
        _frozen(frozen_on="01/10/2026")


def test_validate_detects_edit_after_freezing():
    candidates = _frozen()
    assert validate(candidates, []) == []
    candidates[0]["params"]["level"] = 2
    problems = validate(candidates, [])
    assert len(problems) == 1 and "fingerprint mismatch" in problems[0]


def test_validate_detects_removed_candidate_and_wrong_sha():
    candidates = _frozen()
    rows = [_row(), _row(candidate="gone-v1", pass_date="2026-11-03"),
            _row(pass_date="2026-12-01", sha="b" * 40)]
    problems = validate(candidates, rows)
    assert any("gone-v1" in p and "missing from the registry" in p for p in problems)
    assert any("2026-12-01" in p and "frozen sha/D" in p for p in problems)


def test_registry_round_trip(tmp_path):
    path = tmp_path / "shadow" / "registry.json"
    candidates = _frozen()
    save_registry(path, candidates)
    assert load_registry(path) == candidates
    assert load_registry(tmp_path / "absent.json") == []


# ---------------------------------------------------------------- CSV et echeances

def test_append_row_is_append_only_one_pass_per_month(tmp_path):
    path = tmp_path / "passes.csv"
    append_row(path, _row(pass_date="2026-11-02"))
    append_row(path, _row(pass_date="2026-12-01"))
    with pytest.raises(ValueError, match="already replayed in 2026-11"):
        append_row(path, _row(pass_date="2026-11-30"))
    rows = load_rows(path)
    assert [r["pass_date"] for r in rows] == ["2026-11-02", "2026-12-01"]
    assert path.read_text(encoding="utf-8").count("candidate,sha,") == 1


def test_due_skips_done_month_and_not_yet_frozen():
    candidates = _frozen()
    freeze(candidates, id="late-v1", kind="qc", sha=SHA, frozen_on="2026-11-15",
           entrypoint="30823587", params={}, fee_model="5bps notional")
    rows = load_rows(Path("absent.csv"))
    assert [c["id"] for c in due(candidates, rows, "2026-11-02")] == ["demo-v1"]
    assert [c["id"] for c in due(candidates, [_row()], "2026-11-20")] == ["late-v1"]
    assert [c["id"] for c in due(candidates, [_row()], "2026-12-01")] == ["demo-v1", "late-v1"]


# ---------------------------------------------------------------- metriques

DATES3 = ["2026-10-01", "2026-10-02", "2026-10-05"]


def test_metrics_match_definitions():
    rng = np.random.default_rng(18923)
    r = rng.normal(0.0004, 0.01, 504)
    days = np.busday_offset("2024-01-02", np.arange(504), roll="forward")
    dates = [str(d) for d in days]
    m = metrics(dates, r, np.full(504, 0.002), 0.0015)
    equity = np.cumprod(1 + r)
    years = (days[-1] - days[0]).astype(int) / 365.25
    assert m["n_days"] == 504
    assert m["sharpe_net"] == round(r.mean() / r.std(ddof=1) * np.sqrt(252), 4)
    assert m["cagr"] == round(equity[-1] ** (1 / years) - 1, 4)
    assert m["max_drawdown"] == round((equity / np.maximum.accumulate(equity) - 1).min(), 4)
    assert m["turnover"] == 0.002 and m["fees"] == 0.0015


def test_metrics_drawdown_on_known_path():
    m = metrics(DATES3, [0.10, -0.20, 0.05], [0, 0, 0], 0.0)
    assert m["max_drawdown"] == -0.2


def test_metrics_constant_returns_leave_sharpe_empty(tmp_path):
    m = metrics(DATES3, [0.001, 0.001, 0.001], [0, 0, 0], 0.0)
    assert m["sharpe_net"] is None and m["cagr"] > 0
    path = tmp_path / "passes.csv"
    append_row(path, {**_row(), **m})
    assert load_rows(path)[0]["sharpe_net"] == ""


def test_metrics_need_two_returns():
    with pytest.raises(ValueError):
        metrics(DATES3[:1], [0.01], [0.0], 0.0)
    with pytest.raises(ValueError, match="calendar day"):
        metrics(["2026-10-01", "2026-10-01"], [0.01, 0.02], [0.0, 0.0], 0.0)


# ---------------------------------------------------------------- rejeu local

STRATEGY = '''
from helper import daily_return

def run(start, end, level):
    import numpy as np
    dates = ["2026-10-01", "2026-10-02", "2026-10-05"]
    r = np.array([daily_return(level)] * 3)
    return {"dates": dates, "net_returns": r, "turnover": [0.01, 0.0, 0.0],
            "fees": 0.0005, "echo": [start, end]}
'''


def _git(repo: Path, *args: str) -> str:
    return subprocess.run(["git", "-C", str(repo), *args], check=True,
                          capture_output=True, text=True).stdout.strip()


@pytest.fixture
def repo(tmp_path) -> Path:
    root = tmp_path / "repo"
    (root / "strats").mkdir(parents=True)
    _git(root.parent, "init", "-q", str(root))
    _git(root, "config", "user.email", "test@example.invalid")
    _git(root, "config", "user.name", "test")
    (root / "strats" / "strat.py").write_text(STRATEGY, encoding="utf-8")
    (root / "strats" / "helper.py").write_text(
        "def daily_return(level):\n    return 0.001 * level\n", encoding="utf-8")
    _git(root, "add", "strats")
    _git(root, "commit", "-q", "-m", "frozen version")
    return root


def test_replay_uses_frozen_code(repo, tmp_path):
    frozen_sha = _git(repo, "rev-parse", "HEAD")
    # The helper changes after freezing: the replay must ignore it.
    (repo / "strats" / "helper.py").write_text(
        "def daily_return(level):\n    return -0.05\n", encoding="utf-8")
    _git(repo, "commit", "-q", "-am", "later edit")

    candidates = _frozen(sha=frozen_sha, entrypoint="strats/strat.py:run")
    series = tmp_path / "series"
    row = replay_local(repo, candidates[0], "2026-11-02", series_dir=series)

    assert row["sha"] == frozen_sha and row["period_end"] == "2026-10-05"
    assert row["n_days"] == 3 and row["fees"] == 0.0005
    assert row["cagr"] > 0 and row["max_drawdown"] == 0.0
    assert (series / "demo-v1_2026-11-02.csv").read_text(encoding="utf-8").startswith(
        "date,net_return,turnover\n2026-10-01,0.001,0.01\n")
    # The temporary worktree is gone.
    assert len(_git(repo, "worktree", "list").splitlines()) == 1


def test_replay_reports_entrypoint_failure(repo):
    candidates = _frozen(sha=_git(repo, "rev-parse", "HEAD"), entrypoint="strats/strat.py:nope")
    with pytest.raises(RuntimeError, match="frozen entrypoint failed"):
        replay_local(repo, candidates[0], "2026-11-02")
    assert len(_git(repo, "worktree", "list").splitlines()) == 1


def test_cli_freeze_validate_replay(repo, tmp_path, capsys):
    reg, out = tmp_path / "registry.json", tmp_path / "passes.csv"
    base = ["--registry", str(reg), "--csv", str(out)]
    assert main(base + ["freeze", "--id", "demo-v1", "--kind", "local", "--sha", "HEAD",
                        "--entrypoint", "strats/strat.py:run", "--params", '{"level": 2}',
                        "--fee-model", "5bps notional", "--frozen-on", "2026-10-01",
                        "--repo", str(repo)]) == 0
    assert load_registry(reg)[0]["sha"] == _git(repo, "rev-parse", "HEAD")
    assert main(base + ["replay-local", "--pass-date", "2026-11-02", "--repo", str(repo)]) == 0
    assert main(base + ["due", "--pass-date", "2026-11-20"]) == 0
    assert main(base + ["validate"]) == 0
    printed = capsys.readouterr().out
    assert "OK 1 candidates, 1 passes" in printed
    assert json.loads(printed.splitlines()[1])["candidate"] == "demo-v1"

    # Editing the registry by hand makes every command refuse to run.
    data = json.loads(reg.read_text(encoding="utf-8"))
    data["candidates"][0]["params"]["level"] = 3
    reg.write_text(json.dumps(data), encoding="utf-8")
    assert main(base + ["replay-local", "--pass-date", "2026-12-01", "--repo", str(repo)]) == 1
    assert main(base + ["freeze", "--id", "demo-v2", "--kind", "local", "--sha", "HEAD",
                        "--entrypoint", "strats/strat.py:run", "--fee-model", "5bps notional",
                        "--repo", str(repo)]) == 1
    assert len(load_rows(out)) == 1 and len(load_registry(reg)) == 1
