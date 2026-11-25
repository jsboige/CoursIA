"""Tests for shadow_replay.py — frozen candidates, append-only CSV, local and QC replay (#18923).

The decisive tests are `test_replay_uses_frozen_code` and `test_plan_qc_extracts_frozen_files`:
after freezing, the strategy is edited and committed again; the replay must still use the frozen
version.
"""

from __future__ import annotations

import datetime as dt
import hashlib
import json
import subprocess
from pathlib import Path
from zoneinfo import ZoneInfo

import numpy as np
import pytest

from shadow_replay import (
    append_row,
    due,
    fingerprint,
    freeze,
    ingest_qc,
    load_registry,
    load_rows,
    main,
    metrics,
    plan_qc,
    QC_FROZEN_SESSIONS,
    qc_daily_equity,
    qc_entrypoint,
    qc_frozen_sessions,
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
           entrypoint="qcproj:4242", params={}, fee_model="5bps notional")
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
                          capture_output=True, text=True,
                          encoding="utf-8", errors="replace").stdout.strip()


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


# ---------------------------------------------------------------- rejeu QuantConnect

NY = ZoneInfo("America/New_York")
QC_V1 = "VERSION = 1\n"


def _close_ts(day: str) -> int:
    """16:00 New York: the time QC stamps on a daily close."""
    return int(dt.datetime.combine(dt.date.fromisoformat(day), dt.time(16), tzinfo=NY).timestamp())


def _sessions(start: str, n: int) -> list[str]:
    return [str(d) for d in np.busday_offset(start, np.arange(n), roll="forward")]


def _calendar_sessions(start: str, n: int) -> list[str]:
    # Jours calendaires consecutifs -- une candidate crypto cote 7/7 et peut geler un
    # samedi, jour qu'aucun `np.busday_offset` ne produit (revue Hermes #24288 : les
    # fixtures en jours ouvrés ne peuvent PAS pinner l'ancrage calendaire du garde).
    d0 = dt.date.fromisoformat(start)
    return [str(d0 + dt.timedelta(days=i)) for i in range(n)]


def _chart(days: list[str], equity, fees: float = 0.0012, turnover: float = 1.6,
           shift: int = 0) -> dict:
    """Chart `shadow` as the candidate contract plots it: equity in e0..e4 in turn, cumulative
    costs at every close. `shift` décale le cycle d'un cran constant (cas
    `btc-voltarget-base`, #24153, où le premier point tombe dans e1)."""
    series = {f"e{k}": {"values": []} for k in range(5)}
    for i, (d, v) in enumerate(zip(days, equity)):
        series[f"e{(i + shift) % 5}"]["values"].append([_close_ts(d), float(v)])
    n = len(days)
    series["fees"] = {"values": [{"x": _close_ts(d), "y": fees * (i + 1) / n}
                                 for i, d in enumerate(days)]}
    series["turnover"] = {"values": [[_close_ts(d), turnover * (i + 1) / n]
                                     for i, d in enumerate(days)]}
    return {"name": "shadow", "series": series}


def _midnight_ts(day: str) -> int:
    """00:00 New York: the time QC stamps on a benchmark point, one per calendar day."""
    return int(dt.datetime.combine(dt.date.fromisoformat(day), dt.time(0), tzinfo=NY).timestamp())


def _benchmark(closes: list[float], start: str) -> dict:
    """Chart `Benchmark` as QC returns it: one point per calendar day, weekends included,
    where a closed market repeats the last close."""
    day0 = dt.date.fromisoformat(start)
    return {"name": "Benchmark", "series": {"Benchmark": {"values": [
        [_midnight_ts(str(day0 + dt.timedelta(days=i))), float(close)]
        for i, close in enumerate(closes)]}}}


def _live_benchmark(start: str, n_days: int) -> dict:
    """A published market: the close changes every day, so no session repeats."""
    return _benchmark([700.0 + i for i in range(n_days)], start)


# Graphique `Benchmark` du backtest 273d04de (projet 39243884), lu le 2026-11-25 : neuf
# points, un par jour de calendrier, du jeudi 12 au vendredi 20 novembre. Chaque point porte
# la cloture de la veille : celui du samedi 14 porte celle du vendredi 13 (754,37 differe de
# 757,12), le dimanche et le lundi la repetent (marche ferme). Le point du jeudi 19 et celui
# du vendredi 20 repetent aussi celui de la veille alors que le marche etait ouvert : les
# barres du mercredi 18 et du jeudi 19 n'etaient pas publiees au passage du vendredi 20.
BENCHMARK_273D04DE = [759.81, 757.12, 754.37, 754.37, 754.37, 739.95, 732.44, 732.44, 732.44]


def _qc_candidate(sha: str = SHA) -> dict:
    return _frozen(id="qc-demo", kind="qc", sha=sha, frozen_on="2025-10-01",
                   entrypoint="qcproj:4242", params={"weight": 0.6})[0]


def _qc_plan(candidate: dict, pass_date: str = "2025-11-14") -> dict:
    return {"candidate": candidate["id"], "sha": candidate["sha"],
            "frozen_on": candidate["frozen_on"], "pass_date": pass_date,
            "backtest_name": f"shadow-{candidate['id']}-{pass_date}"}


def _backtest(plan: dict, **overrides) -> dict:
    return {"name": plan["backtest_name"], "completed": True, "error": "", **overrides}


def _equity(n: int, seed: int = 18923) -> np.ndarray:
    return 100000 * np.cumprod(1 + np.random.default_rng(seed).normal(0.0004, 0.008, n))


@pytest.fixture
def qc_repo(tmp_path) -> Path:
    root = tmp_path / "qcrepo"
    (root / "qcproj" / "lib").mkdir(parents=True)
    _git(root.parent, "init", "-q", str(root))
    _git(root, "config", "user.email", "test@example.invalid")
    _git(root, "config", "user.name", "test")
    (root / "qcproj" / "main.py").write_bytes(QC_V1.encode())
    (root / "qcproj" / "lib" / "signals.py").write_text("LOOKBACK = 21\n", encoding="utf-8")
    (root / "qcproj" / "notes.md").write_text("not a project file\n", encoding="utf-8")
    _git(root, "add", "qcproj")
    _git(root, "commit", "-q", "-m", "frozen version")
    return root


def test_qc_entrypoint_parsing():
    assert qc_entrypoint(_qc_candidate()) == ("qcproj", 4242)
    assert qc_entrypoint({**_qc_candidate(), "entrypoint": "a/b/proj/:17"}) == ("a/b/proj", 17)
    for bad in ("4242", "qcproj:", "qcproj:abc"):
        with pytest.raises(ValueError, match="qc entrypoint"):
            qc_entrypoint({**_qc_candidate(), "entrypoint": bad})
    with pytest.raises(ValueError, match="not qc"):
        qc_entrypoint(_frozen()[0])


def test_plan_qc_extracts_frozen_files(qc_repo, tmp_path):
    frozen_sha = _git(qc_repo, "rev-parse", "HEAD")
    (qc_repo / "qcproj" / "main.py").write_text("VERSION = 2\n", encoding="utf-8")
    _git(qc_repo, "commit", "-q", "-am", "later edit")

    candidate = _qc_candidate(sha=frozen_sha)
    plan = plan_qc(qc_repo, candidate, "2025-11-14", tmp_path / "plans")
    target = tmp_path / "plans" / "qc-demo"

    assert (target / "files" / "main.py").read_text(encoding="utf-8") == QC_V1
    assert (target / "files" / "lib" / "signals.py").exists()
    assert not (target / "files" / "notes.md").exists()
    assert sorted(f["name"] for f in plan["files"]) == ["lib/signals.py", "main.py"]
    main_entry = next(f for f in plan["files"] if f["name"] == "main.py")
    assert main_entry["sha256"] == hashlib.sha256(QC_V1.encode()).hexdigest()
    assert plan["qc_project_id"] == 4242 and plan["sha"] == frozen_sha
    assert plan["parameters"] == {"start": "2025-10-01", "end": "2025-11-14", "weight": "0.6"}
    assert plan["backtest_name"] == "shadow-qc-demo-2025-11-14"
    assert plan["chart_start"] <= _close_ts("2025-10-01")
    assert plan["chart_end"] > _close_ts("2025-11-14")
    assert plan["benchmark_chart"] == "Benchmark"
    assert json.loads((target / "plan.json").read_text(encoding="utf-8")) == plan


def test_plan_qc_resolves_the_entrypoint_from_the_repo_root(qc_repo, tmp_path):
    # Le README lance la commande depuis un sous-dossier, avec --repo a sa valeur par defaut.
    candidate = _qc_candidate(sha=_git(qc_repo, "rev-parse", "HEAD"))
    plan = plan_qc(qc_repo / "qcproj" / "lib", candidate, "2025-11-14", tmp_path / "plans")
    assert sorted(f["name"] for f in plan["files"]) == ["lib/signals.py", "main.py"]
    assert (tmp_path / "plans" / "qc-demo" / "files" / "main.py").read_text(encoding="utf-8") == QC_V1

def test_plan_qc_rejects_reserved_params_and_empty_project(qc_repo, tmp_path):
    sha = _git(qc_repo, "rev-parse", "HEAD")
    reserved = _frozen(id="qc-demo", kind="qc", sha=sha, frozen_on="2025-10-01",
                       entrypoint="qcproj:4242", params={"start": "2020-01-01"})[0]
    with pytest.raises(ValueError, match="reserved"):
        plan_qc(qc_repo, reserved, "2025-11-14", tmp_path)
    empty = {**_qc_candidate(sha=sha), "entrypoint": "absent:4242"}
    with pytest.raises(ValueError, match="no .py file"):
        plan_qc(qc_repo, empty, "2025-11-14", tmp_path)


def test_qc_daily_equity_merges_series_in_session_order():
    days = _sessions("2025-10-01", 12)
    equity = _equity(12)
    dates, values = qc_daily_equity(_chart(days, equity))
    assert dates == days
    assert values == pytest.approx(list(equity))


def test_qc_daily_equity_detects_lost_point():
    days = _sessions("2025-10-01", 12)
    chart = _chart(days, _equity(12))
    del chart["series"]["e2"]["values"][1]      # session 7 never reached the chart
    with pytest.raises(ValueError, match="interleaving broken at point 7"):
        qc_daily_equity(chart)


def test_qc_daily_equity_detects_two_points_on_one_session():
    days = _sessions("2025-10-01", 10)
    chart = _chart(days, _equity(10))
    # Point 5 (e0) lands one hour after point 4 (e4), on the same session: the cycle holds.
    chart["series"]["e0"]["values"][1][0] = _close_ts(days[4]) + 3600
    with pytest.raises(ValueError, match="same session"):
        qc_daily_equity(chart)


def test_qc_daily_equity_accepts_short_window():
    days = _sessions("2025-10-01", 3)           # e3 and e4 stay empty: cycle open, not broken
    dates, values = qc_daily_equity(_chart(days, _equity(3)))
    assert dates == days
    assert len(values) == 3


def test_qc_daily_equity_refuses_series_gap():
    days = _sessions("2025-10-01", 12)
    chart = _chart(days, _equity(12))
    chart["series"]["e3"]["values"] = []        # a hole inside the cycle
    with pytest.raises(ValueError, match="contiguous prefix"):
        qc_daily_equity(chart)


def test_qc_daily_equity_admits_a_constant_shift_anchored_on_the_window():
    # Cas btc-voltarget-base (#24153) : la candidate incremente son compteur avant le
    # modulo, donc la premiere seance tombe dans e1 et le cycle est decale d'un cran sans
    # qu'aucun point ne manque. Admis parce que le premier point EST la premiere seance de
    # la fenetre : rien n'a pu etre perdu avant lui.
    days = _sessions("2025-10-01", 7)
    equity = _equity(7)
    dates, values = qc_daily_equity(_chart(days, equity, shift=1), window_start=days[0])
    assert dates == days
    assert values == pytest.approx(list(equity))


def test_qc_daily_equity_refuses_a_shift_not_anchored_on_the_window():
    # Meme decalage, mais le premier point tombe le deuxieme jour de la fenetre : la
    # premiere seance a disparu avant le premier point, et le decalage ne l'explique pas.
    days = _sessions("2025-10-01", 7)
    chart = _chart(days[1:], _equity(6), shift=1)
    with pytest.raises(ValueError, match="not the first session of the window"):
        qc_daily_equity(chart, window_start=days[0])


def test_qc_daily_equity_refuses_a_shift_without_window_start():
    # Appel direct sans fenetre (`league_correlation`) : le cycle doit partir de e0,
    # faute de reference pour distinguer un decalage d'un point perdu -> fail-CLOSED.
    days = _sessions("2025-10-01", 7)
    with pytest.raises(ValueError, match="starts at e1"):
        qc_daily_equity(_chart(days, _equity(7), shift=1))


def test_qc_daily_equity_accepts_a_saturday_freeze_shifted_cycle():
    # Le cas REEL de #24153 : `btc-voltarget-base` a gele le samedi 2026-10-17 (Bitfinex
    # cote 7/7) et le cycle part de e1. Un ancrage en jours ouvrés roulerait la premiere
    # seance au lundi 19 et refuserait sous un autre message le cas meme que le garde
    # doit admettre. En jours calendaires : premiere seance = date de gel -> admis.
    days = _calendar_sessions("2026-10-17", 6)  # samedi -> jeudi
    assert dt.date.fromisoformat(days[0]).weekday() == 5  # samedi, pinné
    dates, _ = qc_daily_equity(_chart(days, _equity(6), shift=1),
                               window_start=days[0])
    assert dates == days


def test_qc_daily_equity_refuses_a_lost_first_session_on_calendar_days():
    # Contre-epreuve sur les memes jours calendaires : la premiere seance (samedi) est
    # reellement perdue -- le premier point tombe au dimanche. Refuse, alors que
    # l'ancrage en jours ouvrés l'admettait (samedi roule au lundi = lundi observe).
    days = _calendar_sessions("2026-10-17", 6)
    with pytest.raises(ValueError, match="not the first session of the window"):
        qc_daily_equity(_chart(days[1:], _equity(5), shift=1),
                        window_start=days[0])


def test_ingest_qc_accepts_the_btc_voltarget_shift():
    # Le passage lui-meme : `ingest_qc` ancre le decalage sur la date de gel du plan, et la
    # ligne produite couvre la fenetre entiere. Candidate gelee le premier jour des
    # seances, comme dans le cas reel (`frozen_on` = premiere seance de la fenetre).
    days = _sessions("2025-11-10", 5)
    candidate = _frozen(id="qc-shift", kind="qc", sha=SHA, frozen_on=days[0],
                        entrypoint="qcproj:4242", params={"weight": 0.6})[0]
    plan = _qc_plan(candidate, pass_date=days[-1])
    row = ingest_qc(candidate, plan, _backtest(plan),
                    _chart(days, _equity(5), shift=1), _live_benchmark(days[0], 12))
    assert row["period_end"] == days[-1]
    assert row["n_days"] == 4


def test_ingest_qc_refuses_a_shifted_chart_whose_first_session_is_missing():
    # Contre-epreuve au niveau du passage : decale ET ampute de sa premiere seance, le
    # graphique ne passe pas, meme avec la fenetre du plan.
    days = _sessions("2025-11-10", 5)
    candidate = _frozen(id="qc-shift", kind="qc", sha=SHA, frozen_on=days[0],
                        entrypoint="qcproj:4242", params={"weight": 0.6})[0]
    plan = _qc_plan(candidate, pass_date=days[-1])
    with pytest.raises(ValueError, match="not the first session of the window"):
        ingest_qc(candidate, plan, _backtest(plan),
                  _chart(days[1:], _equity(4), shift=1), _live_benchmark(days[0], 12))


def test_ingest_qc_accepts_short_window_ending_near_the_pass_date():
    # Fenetre courte (trois seances) dont la derniere cloture est proche de la date de
    # passage : les comptes n'ont pas besoin d'etre egaux, la complétude se lit au
    # calendrier.
    candidate = _qc_candidate()
    plan = _qc_plan(candidate)
    days = _sessions("2025-11-10", 3)
    row = ingest_qc(candidate, plan, _backtest(plan, tradeableDates=9),
                    _chart(days, _equity(3)), _live_benchmark(days[0], 10))
    assert row["period_end"] == days[-1]


def test_ingest_qc_accepts_universe_dates_beyond_the_traced_closes():
    # Cas fs774 (passe du 2026-10-27) : la candidate declare un `add_universe` de 500
    # titres et une donnee CBOE, donc `tradeableDates` (22) depasse les clotures SPY
    # tracees (15). L'ancienne garde d'egalite refusait ce graphique complet ; la
    # derniere cloture (vendredi 23) reste recente au regard du passage (mardi 27).
    candidate = _qc_candidate()
    plan = _qc_plan(candidate, pass_date="2026-10-27")
    days = _sessions("2026-10-05", 15)
    assert days[-1] == "2026-10-23"
    row = ingest_qc(candidate, plan, _backtest(plan, tradeableDates=22),
                    _chart(days, _equity(15)), _live_benchmark(days[0], 24))
    assert row["period_end"] == "2026-10-23" and row["n_days"] == 14


def test_ingest_qc_refuses_trailing_truncation():
    # Chart ampute de ses dix dernieres seances : le cycle e0..e4 reste intact, seule
    # la derniere cloture (2025-10-30, quinze jours avant le passage) trahit la coupe.
    candidate = _qc_candidate()
    plan = _qc_plan(candidate)
    days = _sessions("2025-10-01", 32)
    equity = _equity(32)
    chart = _chart(days[:22], equity[:22])
    with pytest.raises(ValueError, match="chart truncated or incomplete"):
        ingest_qc(candidate, plan, _backtest(plan, tradeableDates=32), chart,
                  _live_benchmark(days[0], 40))


def test_ingest_qc_matches_direct_metrics(tmp_path):
    candidate = _qc_candidate()
    plan = _qc_plan(candidate)
    days = _sessions("2025-10-01", 32)
    equity = _equity(32)
    row = ingest_qc(candidate, plan, _backtest(plan), _chart(days, equity),
                    _live_benchmark(days[0], 48), series_dir=tmp_path / "series")

    returns = equity[1:] / equity[:-1] - 1
    expected = metrics(days, returns, np.full(31, 1.6 / 31), 0.0012)
    assert row == {"candidate": "qc-demo", "sha": SHA, "frozen_on": "2025-10-01",
                   "pass_date": "2025-11-14", "period_end": days[-1],
                   "fee_model": "5bps notional", **expected}
    assert row["n_days"] == 31 and row["turnover"] == round(1.6 / 31, 6)
    series = (tmp_path / "series" / "qc-demo_2025-11-14.csv").read_text(encoding="utf-8")
    assert series.startswith(f"date,equity\n{days[0]},{float(equity[0])}\n")
    assert len(series.splitlines()) == 33


@pytest.mark.parametrize("change, exc, message", [
    (lambda bt, plan, chart: bt.update(completed=False), ValueError, "not completed"),
    (lambda bt, plan, chart: bt.update(completed=""), ValueError, "not completed"),
    (lambda bt, plan, chart: bt.update(name="other"), ValueError, "is not 'shadow-qc-demo"),
    (lambda bt, plan, chart: bt.update(error="Runtime Error"), RuntimeError, "backtest failed"),
    (lambda bt, plan, chart: plan.update(sha="b" * 40), ValueError, "plan does not match"),
    (lambda bt, plan, chart: plan.update(pass_date="2025-11-05"), ValueError, "outside"),
    (lambda bt, plan, chart: chart["series"]["fees"]["values"].pop(), ValueError, "last fees"),
    (lambda bt, plan, chart: chart["series"].pop("turnover"), ValueError, "missing series"),
    (lambda bt, plan, chart: bt.update(tradeableDates=9), ValueError, "9 tradeable dates"),
])
def test_ingest_qc_refuses(change, exc, message):
    candidate = _qc_candidate()
    plan = _qc_plan(candidate)
    bt = _backtest(plan)
    chart = _chart(_sessions("2025-10-01", 32), _equity(32))
    change(bt, plan, chart)
    with pytest.raises(exc, match=message):
        ingest_qc(candidate, plan, bt, chart, _live_benchmark("2025-10-01", 48))


def test_ingest_qc_refuses_equity_before_freezing():
    candidate = _qc_candidate()
    plan = _qc_plan(candidate)
    chart = _chart(_sessions("2025-09-29", 20), _equity(20))
    with pytest.raises(ValueError, match="outside 2025-10-01"):
        ingest_qc(candidate, plan, _backtest(plan), chart, _live_benchmark("2025-09-29", 32))


def _passage_273d04de():
    """Le passage de `short-intl-v2` du 2026-11-20 (backtest 273d04de), tel que la plateforme
    l'a rendu : six seances, l'equite figee du 17 au 19 novembre (100 112,3408 trois fois),
    les frais et la rotation figes avec elle."""
    days = ["2026-11-12", "2026-11-13", "2026-11-16", "2026-11-17", "2026-11-18", "2026-11-19"]
    chart = _chart(days, [100437.8878, 100261.0932, 100112.3193, 100112.3408, 100112.3408,
                          100112.3408], fees=0.0007117, turnover=0.9904392)
    candidate = _frozen(id="short-intl-v2", kind="qc", sha=SHA, frozen_on=days[0],
                        entrypoint="qcproj:4242", params={"weight": 0.6})[0]
    plan = _qc_plan(candidate, pass_date="2026-11-20")
    return candidate, plan, _backtest(plan), chart


def test_qc_frozen_sessions_reads_the_measured_tail():
    # Les points du jeudi 19 et du vendredi 20 repetent celui de la veille : les barres du
    # mercredi 18 et du jeudi 19 n'etaient pas publiees. Le dimanche 15 et le lundi 16
    # repetent aussi le vendredi 13 : le marche etait ferme, rien ne compte.
    benchmark = _benchmark(BENCHMARK_273D04DE, "2026-11-12")
    assert qc_frozen_sessions(benchmark, "2026-11-20") == ["2026-11-18", "2026-11-19"]


def test_qc_frozen_sessions_ignores_closed_days():
    # Un passage le lundi 16 lit deux points qui repetent celui du vendredi 13 : le marche
    # etait ferme samedi 14 et dimanche 15.
    assert qc_frozen_sessions(_benchmark([759.81, 757.12, 754.37, 754.37, 754.37],
                                         "2026-11-12"), "2026-11-16") == []


def test_qc_frozen_sessions_does_not_reset_the_run_over_a_weekend():
    # Barres du jeudi 19 et du vendredi 20 non publiees, passage le lundi 23 : les points
    # du samedi et du dimanche repetent aussi, sans interrompre la suite.
    benchmark = _benchmark([701.0, 700.0, 700.0, 700.0, 700.0, 700.0], "2026-11-18")
    assert qc_frozen_sessions(benchmark, "2026-11-23") == ["2026-11-19", "2026-11-20"]


def test_qc_frozen_sessions_stops_at_the_pass_date():
    # Le point du passage (jeudi 19) porte la barre du mercredi 18 : sa repetition est
    # comptee. Un point d'apres porterait la seance du passage, hors fenetre.
    assert qc_frozen_sessions(_benchmark([700.0, 701.0, 701.0, 701.0], "2026-11-17"),
                              "2026-11-19") == ["2026-11-18"]


def test_qc_frozen_sessions_admits_one_closed_weekday():
    # Jeudi de Thanksgiving 2026 (26/11) : le marche est ferme, le point du vendredi 27
    # repete celui du jeudi. Une repetition seule ne se distingue pas d'une barre en
    # retard d'un jour : la seance est rendue, sans atteindre le seuil.
    assert qc_frozen_sessions(_benchmark([700.0, 701.0, 702.0, 702.0], "2026-11-24"),
                              "2026-11-27") == ["2026-11-26"]
    assert 1 < QC_FROZEN_SESSIONS


def test_qc_frozen_sessions_keeps_only_the_trailing_run():
    # Une repetition isolee en cours de fenetre (point du mercredi 25) n'affecte pas la fin.
    assert qc_frozen_sessions(_benchmark([700.0, 701.0, 701.0, 702.0, 703.0], "2026-11-23"),
                              "2026-11-28") == []


def test_qc_frozen_sessions_compares_only_the_day_after():
    # Un backtest qui s'arrete en cours de jour ajoute un point a son heure d'arret (cas
    # mesure sur `controle-v2-sans-defaut`, 2026-11-10 a 19:00). Un second point du meme
    # jour ne suit pas la veille : il n'est compare a rien, meme s'il repete le premier.
    def stopped(last: float) -> dict:
        return {"name": "Benchmark", "series": {"Benchmark": {"values": [
            [_midnight_ts("2026-11-09"), 74825.0], [_midnight_ts("2026-11-10"), 74780.0],
            [_midnight_ts("2026-11-10") + 19 * 3600, last]]}}}

    assert qc_frozen_sessions(stopped(73797.0), "2026-11-11") == []
    assert qc_frozen_sessions(stopped(74780.0), "2026-11-11") == []


def test_ingest_qc_refuses_the_passage_that_measured_flat_sessions():
    # Accepte le 2026-11-20 par la version d'alors, ce passage a ete retire de #27480. La
    # date de sa derniere cloture (la veille) est recente : la fraicheur des seances se lit
    # sur le benchmark, pas au calendrier.
    candidate, plan, backtest, chart = _passage_273d04de()
    with pytest.raises(ValueError, match=r"last 2 sessions.*\(2026-11-18, 2026-11-19\)"):
        ingest_qc(candidate, plan, backtest, chart,
                  _benchmark(BENCHMARK_273D04DE, "2026-11-12"))


def test_ingest_qc_accepts_a_flat_candidate_on_a_published_market():
    # Contre-epreuve : l'equite figee n'est pas ce que le garde refuse. Un portefeuille en
    # liquidites trace une equite constante ; si le marche, lui, cote, le passage est sain.
    candidate, plan, backtest, chart = _passage_273d04de()
    row = ingest_qc(candidate, plan, backtest, chart, _live_benchmark("2026-11-12", 8))
    assert row["period_end"] == "2026-11-19" and row["n_days"] == 5
    assert row["turnover"] == pytest.approx(0.9904392 / 5, abs=1e-6)


def test_ingest_qc_refuses_a_benchmark_that_stops_before_the_last_close():
    # Temoin ampute de sa fin : la publication des dernieres seances ne se lit plus.
    candidate, plan, backtest, chart = _passage_273d04de()
    with pytest.raises(ValueError,
                       match=r"'Benchmark' ends on 2026-11-17, before the last close 2026-11-19"):
        ingest_qc(candidate, plan, backtest, chart, _live_benchmark("2026-11-12", 6))


def test_ingest_qc_refuses_a_passage_without_its_benchmark():
    # Sans temoin, la fraicheur des seances ne se mesure pas : le passage ne s'accepte pas.
    candidate, plan, backtest, chart = _passage_273d04de()
    with pytest.raises(ValueError, match="'Benchmark': missing series 'Benchmark'"):
        ingest_qc(candidate, plan, backtest, chart, {"name": "Benchmark", "series": {}})


def test_cli_ingest_qc_refuses_a_plan_dir_without_the_benchmark(tmp_path, capsys):
    reg, out = tmp_path / "registry.json", tmp_path / "passes.csv"
    candidate, plan, backtest, chart = _passage_273d04de()
    save_registry(reg, [candidate])
    plan_dir = tmp_path / "short-intl-v2"
    plan_dir.mkdir()
    (plan_dir / "plan.json").write_text(json.dumps(plan), encoding="utf-8")
    (plan_dir / "backtest.json").write_text(json.dumps(backtest), encoding="utf-8")
    (plan_dir / "chart.json").write_text(json.dumps(chart), encoding="utf-8")
    cmd = ["--registry", str(reg), "--csv", str(out), "ingest-qc", "--plan-dir", str(plan_dir)]

    assert main(cmd) == 1
    printed = capsys.readouterr().out
    assert "benchmark.json is missing" in printed and "'Benchmark'" in printed

    (plan_dir / "benchmark.json").write_text(
        json.dumps(_benchmark(BENCHMARK_273D04DE, "2026-11-12")), encoding="utf-8")
    with pytest.raises(ValueError, match="not published"):
        main(cmd)
    assert not out.exists()


def test_cli_plan_qc_then_ingest_qc(qc_repo, tmp_path, capsys):
    reg, out, plans = tmp_path / "registry.json", tmp_path / "passes.csv", tmp_path / "plans"
    base = ["--registry", str(reg), "--csv", str(out)]
    assert main(base + ["freeze", "--id", "qc-demo", "--kind", "qc", "--sha", "HEAD",
                        "--entrypoint", "qcproj:4242", "--params", '{"weight": 0.6}',
                        "--fee-model", "QC default", "--frozen-on", "2025-10-01",
                        "--repo", str(qc_repo)]) == 0
    capsys.readouterr()

    # The local replay leaves QC candidates to plan-qc / ingest-qc.
    assert main(base + ["replay-local", "--pass-date", "2025-11-14", "--repo", str(qc_repo)]) == 0
    assert "SKIPPED (qc candidates, replay with plan-qc then ingest-qc): qc-demo" in \
        capsys.readouterr().out

    assert main(base + ["plan-qc", "--pass-date", "2025-11-14", "--repo", str(qc_repo),
                        "--out-dir", str(plans)]) == 0
    printed = json.loads(capsys.readouterr().out.splitlines()[0])
    assert printed["qc_project_id"] == 4242
    assert printed["backtest_name"] == "shadow-qc-demo-2025-11-14"

    # What the operator saves after the MCP run.
    plan_dir = plans / "qc-demo"
    plan = json.loads((plan_dir / "plan.json").read_text(encoding="utf-8"))
    days = _sessions("2025-10-01", 32)
    (plan_dir / "backtest.json").write_text(json.dumps(_backtest(plan)), encoding="utf-8")
    (plan_dir / "chart.json").write_text(json.dumps(_chart(days, _equity(32))), encoding="utf-8")
    (plan_dir / "benchmark.json").write_text(
        json.dumps(_live_benchmark("2025-10-01", 50)), encoding="utf-8")

    assert main(base + ["ingest-qc", "--plan-dir", str(plan_dir)]) == 0
    rows = load_rows(out)
    assert len(rows) == 1 and rows[0]["candidate"] == "qc-demo"
    assert rows[0]["period_end"] == days[-1] and rows[0]["fee_model"] == "QC default"
    assert main(base + ["validate"]) == 0

    # Once ingested, the month is done: plan-qc has nothing left to prepare.
    capsys.readouterr()
    assert main(base + ["plan-qc", "--pass-date", "2025-11-20", "--repo", str(qc_repo),
                        "--out-dir", str(tmp_path / "plans2")]) == 0
    assert capsys.readouterr().out == "" and not (tmp_path / "plans2").exists()
