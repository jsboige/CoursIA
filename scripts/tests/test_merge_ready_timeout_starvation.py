"""Witnesses for merge_ready timeout starvation (dispatch c0175, #28973).

These tests simulate a bounded pass with expensive timed-out PR evaluations
and verify the acceptance criterion: at least 20 PRs are evaluated.
"""

import importlib.util
import json
import sys
from pathlib import Path

import pytest

MERGE_READY_PATH = Path(__file__).resolve().parents[1] / "coordination" / "merge_ready.py"
_spec = importlib.util.spec_from_file_location("merge_ready_timeout_test", MERGE_READY_PATH)
mr = importlib.util.module_from_spec(_spec)
sys.modules["merge_ready_timeout_test"] = mr
_spec.loader.exec_module(mr)

NORMAL_COST = 5.0
TIMEOUT_COST = 600.0
NORMAL_PR_DEADLINE = 90.0  # default budget consumed by the post-#28966 base
PRS = tuple(range(1, 31))
TIMING_OUT = (1, 4, 7, 10, 13, 16, 19, 22)


class FakeClock:
    """Pass clock advanced by the fake runner."""

    def __init__(self):
        self.now = 1000.0

    def __call__(self):
        return self.now

    def advance(self, seconds):
        self.now += seconds


class TimedRunner:
    """Small runner fake that supplies only the merge_ready inputs under test."""

    def __init__(self, clock, timeouts=(), prs=()):
        self.clock = clock
        self.timeouts = set(timeouts)
        self.prs = tuple(prs)
        self.budget = None
        self.budgets = []
        self.viewed = []

    def set_pr_budget(self, budget_s):
        self.budget = budget_s
        self.budgets.append(budget_s)

    def run(self, cmd, env=None):
        c = list(cmd)
        if c[:2] == ["gh", "api"] and "/commits?sha=main" in c[2]:
            return mr.RunResult(0, "\n".join("a" * 40 for _ in range(50)), "")
        if c[:2] == ["gh", "api"] and "/check-runs?" in c[2]:
            check = {
                "name": "Scripts Tests (CPU)",
                "conclusion": "success",
                "status": "completed",
                "started_at": "2026-11-28T00:00:00Z",
                "output": {"title": "", "summary": ""},
                "details_url": "",
            }
            return mr.RunResult(0, json.dumps(check), "")
        if c[:3] == ["gh", "pr", "list"]:
            rows = [{"number": pr, "latestReviews": []} for pr in self.prs]
            return mr.RunResult(0, json.dumps(rows), "")
        if c[:3] == ["gh", "pr", "view"] and len(c) > 3:
            pr = int(c[3])
            self.viewed.append(pr)
            if pr in self.timeouts:
                self.clock.advance(min(TIMEOUT_COST, self.budget or TIMEOUT_COST))
                return mr.RunResult(mr.TIMEOUT_RC, "", "simulated timeout")
            self.clock.advance(min(NORMAL_COST, self.budget or NORMAL_COST))
            return mr.RunResult(0, json.dumps(_view(pr)), "")
        if c[:2] == ["gh", "auth"]:
            return mr.RunResult(0, "token", "")
        if c[:2] == ["gh", "api"]:
            return mr.RunResult(0, "[]", "")
        return mr.RunResult(0, "", "")


def _view(pr):
    return {
        "number": pr,
        "title": f"Test PR {pr}",
        "state": "OPEN",
        "isDraft": False,
        "baseRefName": "main",
        "headRefOid": "0123456789abcdef0123456789abcdef01234567",
        "mergeable": "MERGEABLE",
        "reviewDecision": "APPROVED",
        "files": [],
        "labels": [],
        "reviews": [],
    }


def _empty_stack_index():
    return {}


@pytest.fixture
def clock(monkeypatch):
    value = FakeClock()
    monkeypatch.setattr(mr, "_clock", value)
    monkeypatch.setattr(mr.gate, "default_stack_index", _empty_stack_index)
    return value


def _run(tmp_path, runner, extra=()):
    journal = tmp_path / "journal.jsonl"
    hold_file = tmp_path / "hold.txt"
    hold_file.write_text("", encoding="utf-8")
    rc = mr.run(
        ["--journal", str(journal), "--hold-file", str(hold_file), "--max", "1000", *extra],
        runner=runner,
    )
    lines = []
    if journal.is_file():
        lines = [
            json.loads(row)
            for row in journal.read_text(encoding="utf-8").splitlines()
            if row.strip()
        ]
    return rc, lines


def test_a_pass_with_timeouts_evaluates_at_least_twenty_prs(tmp_path, clock):
    runner = TimedRunner(clock=clock, timeouts=TIMING_OUT, prs=PRS)
    rc, _lines = _run(tmp_path, runner)
    assert rc == 0
    assert len(runner.viewed) >= 20, f"evaluated {len(runner.viewed)} PRs"


def test_timeout_budget_switches_to_degraded_pr_deadline(tmp_path, clock):
    runner = TimedRunner(clock=clock, timeouts=TIMING_OUT, prs=PRS)
    rc, _lines = _run(tmp_path, runner)
    assert rc == 0
    deadlines = [budget for budget in runner.budgets if budget is not None]
    assert NORMAL_PR_DEADLINE in deadlines
    assert mr.PR_EVALUATION_FLOOR_S in deadlines
    assert max(deadlines) > min(deadlines)


def test_disabling_timeout_budget_falsifies_the_acceptance_criterion(tmp_path, clock):
    runner = TimedRunner(clock=clock, timeouts=TIMING_OUT, prs=PRS)
    rc, _lines = _run(tmp_path, runner, extra=("--timeout-budget-s", "1000000"))
    assert rc == 0
    assert len(runner.viewed) < 20, f"falsification invalid: {len(runner.viewed)}"


def test_timeout_budget_handles_timeouts_without_prior_journal_entries(tmp_path, clock):
    runner = TimedRunner(clock=clock, timeouts=TIMING_OUT, prs=PRS)
    rc, _lines = _run(tmp_path, runner)
    assert rc == 0
    assert len(runner.viewed) >= 20, f"evaluated {len(runner.viewed)} PRs"


def test_human_report_names_timeout_budget_and_degraded_mode(tmp_path, capsys, clock):
    runner = TimedRunner(clock=clock, timeouts=TIMING_OUT, prs=PRS)
    rc, _lines = _run(tmp_path, runner)
    assert rc == 0
    output = capsys.readouterr().out
    assert "timeouts :" in output
    assert "MODE DEGRADE" in output
