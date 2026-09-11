"""Tests du runner de frontière de coût SAT Life (#12205 §6.3)."""

from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import life_sat_cost_frontier as frontier


def _result(verdict: str) -> dict:
    return {
        "verdict": verdict,
        "min_cells": 1 if verdict == "FOUND" else None,
        "sizes_refuted": [],
        "attempts": [],
        "count_normalized": 0,
        "patterns": [],
        "canonical_glider_present": False,
        "elapsed_s": 0.001,
    }


def test_case_ids_sont_uniques():
    ids = [case.case_id for case in frontier.CASES]
    assert len(ids) == len(set(ids))


def test_les_quatre_axes_et_deux_controles_sont_presents():
    axes = {case.axis for case in frontier.CASES}
    roles = {case.role for case in frontier.CASES}
    assert axes == {"control", "period", "displacement", "box", "cardinality"}
    assert {"positive", "negative"} <= roles


def test_run_case_transmet_le_budget_par_k(monkeypatch):
    captured = {}

    def fake_search_minimal(**kwargs):
        captured.update(kwargs)
        return _result("FOUND")

    monkeypatch.setattr(frontier, "search_minimal", fake_search_minimal)
    case = frontier.CASES[0]
    result = frontier.run_case(case, timeout_ms=1234)

    xs, ys = frontier.universe_bounds(
        case.box_w, case.box_h, case.n, (case.vx, case.vy)
    )
    assert captured["timeout_ms"] == 1234
    assert captured["enumerate_all"] is False
    assert result["case_id"] == case.case_id
    assert result["verdict"] == "FOUND"
    assert result["encoded_width"] == len(xs)
    assert result["encoded_height"] == len(ys)
    assert result["encoded_cells_per_generation"] == len(xs) * len(ys)
    assert result["boolean_state_variables"] == (case.n + 1) * len(xs) * len(ys)


def test_run_campaign_conserve_chaque_repetition(monkeypatch):
    monkeypatch.setattr(frontier, "run_case", lambda case, timeout_ms: _result("FOUND"))
    report = frontier.run_campaign(frontier.CASES[:2], timeout_ms=10, repeats=3)

    assert report["repeats"] == 3
    assert [result["repeat"] for result in report["results"]] == [1, 1, 2, 2, 3, 3]
    assert report["counts"] == {"FOUND": 6, "IMPOSSIBLE": 0, "TIMEOUT": 0}


def test_main_transmet_le_nombre_de_repetitions(monkeypatch, capsys):
    captured = {}

    def fake_run_campaign(cases, timeout_ms, repeats):
        captured["case_ids"] = [case.case_id for case in cases]
        captured["timeout_ms"] = timeout_ms
        captured["repeats"] = repeats
        return {
            "results": [
                {"role": "positive", "verdict": "FOUND"},
                {"role": "negative", "verdict": "IMPOSSIBLE"},
            ]
        }

    monkeypatch.setattr(frontier, "run_campaign", fake_run_campaign)
    assert frontier.main(["--timeout-ms", "17", "--repeats", "3"]) == 0
    assert captured == {
        "case_ids": [case.case_id for case in frontier.CASES],
        "timeout_ms": 17,
        "repeats": 3,
    }
    assert json.loads(capsys.readouterr().out)["results"][0]["verdict"] == "FOUND"


@pytest.mark.parametrize(
    "results",
    [
        [
            {"role": "positive", "verdict": "FOUND"},
            {"role": "negative", "verdict": "FOUND"},
        ],
        [
            {"role": "positive", "verdict": "TIMEOUT"},
            {"role": "negative", "verdict": "IMPOSSIBLE"},
            {"role": "positive", "verdict": "FOUND"},
            {"role": "negative", "verdict": "IMPOSSIBLE"},
        ],
    ],
)
def test_main_refuse_un_controle_non_discriminant(monkeypatch, capsys, results):
    monkeypatch.setattr(
        frontier,
        "run_campaign",
        lambda cases, timeout_ms, repeats: {"results": results},
    )
    assert frontier.main([]) == 2
    assert json.loads(capsys.readouterr().out)["results"] == results


def test_main_refuse_un_budget_nul():
    with pytest.raises(SystemExit) as exc:
        frontier.main(["--timeout-ms", "0"])
    assert exc.value.code == 2


def test_main_refuse_un_nombre_de_repetitions_nul():
    with pytest.raises(SystemExit) as exc:
        frontier.main(["--repeats", "0"])
    assert exc.value.code == 2
