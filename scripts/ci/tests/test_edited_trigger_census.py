"""Tests du census `edited` (#22467).

Deux organes sont pins ici :

* `scripts/ci/list_edited_trigger_workflows.py` -- quels workflows ecoutent
  `pull_request: edited` et si leur verdict bouge quand le body, le titre ou
  la base de la PR bougent ;
* `scripts/ci/measure_redundant_runs.py` -- combien de premieres tentatives
  redondantes la flotte produit, et combien sont imputables a un evenement
  `edited`.

Le pin le plus important est **negatif** : les wrappers Lean ne doivent PLUS
ecouter `edited`. C'est le geste de la PR, et un test qui l'oublierait
laisserait revenir le declencheur sans que rien ne le dise.
"""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[3]
CI_DIR = REPO_ROOT / "scripts" / "ci"
sys.path.insert(0, str(CI_DIR))


def _load(name: str):
    spec = importlib.util.spec_from_file_location(name, CI_DIR / f"{name}.py")
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


census = _load("list_edited_trigger_workflows")
measure = _load("measure_redundant_runs")


# ---------------------------------------------------------------------------
# Census statique
# ---------------------------------------------------------------------------


@pytest.fixture(scope="module")
def rows():
    return census.survey(REPO_ROOT)


def _by_workflow(rows):
    return {row["workflow"]: row for row in rows}


def test_le_census_trouve_la_famille_qui_ecoute_encore_edited(rows):
    found = _by_workflow(rows)
    # `always-on-guards-body.yml` est le workflow des organes de body : il
    # DOIT ecouter `edited` (c'est le verbatim de #22331).
    assert ".github/workflows/always-on-guards-body.yml" in found
    assert "body" in found[".github/workflows/always-on-guards-body.yml"]["depends_on"]


def test_le_census_classe_le_verdict_sur_le_body_lu_directement(rows):
    found = _by_workflow(rows)
    row = found[".github/workflows/always-on-guards-body.yml"]
    assert row["verdict"] == "PR_METADATA_DEPENDENT"
    assert row["direct_body_read"] is True


def test_le_census_ignore_un_workflow_sans_declencheur_edited(rows):
    found = _by_workflow(rows)
    assert ".github/workflows/lean-axiom.yml" not in found


@pytest.mark.parametrize(
    "workflow",
    [
        ".github/workflows/lean-knot.yml",
        ".github/workflows/lean-conway.yml",
    ],
)
def test_les_wrappers_lean_n_ecoutent_plus_edited(rows, workflow):
    """Le geste de la PR : le verdict Lean ne depend ni du body, ni du titre,
    ni de la base de la PR -- donc `edited` ne peut que rejouer le meme
    verdict sur la meme tete."""
    found = _by_workflow(rows)
    assert workflow not in found, (
        f"{workflow} ecoute encore `edited` : son verdict de contenu est "
        "rejoue a chaque edition de body"
    )


def test_le_census_signale_le_dependance_a_la_base(rows):
    """`always-on-metadata-guards.yml` lit la base de la PR : changer de base
    est un evenement `edited`, son verdict bouge -- il doit rester ecoute."""
    found = _by_workflow(rows)
    row = found[".github/workflows/always-on-metadata-guards.yml"]
    assert "base" in row["depends_on"]


# ---------------------------------------------------------------------------
# Mesure des redondances
# ---------------------------------------------------------------------------


def _run(run_id: int, sha: str, created: str, attempt: int = 1, path: str = ".github/workflows/x.yml", pr: int | None = 7):
    return {
        "id": run_id,
        "path": path,
        "name": "X",
        "head_sha": sha,
        "run_attempt": attempt,
        "created_at": created,
        "event": "pull_request",
        "pull_requests": [{"number": pr}] if pr else [],
    }


def test_la_mesure_compte_les_premieres_tentatives_redondantes():
    runs = [
        _run(1, "aaa", "2026-11-01T10:00:00Z"),
        _run(2, "aaa", "2026-11-01T10:05:00Z"),
        _run(3, "bbb", "2026-11-01T11:00:00Z"),
        _run(4, "aaa", "2026-11-01T10:06:00Z", attempt=2),
    ]
    report = measure.analyze(runs, {})
    totals = report["totals"]
    assert totals["redundant_first_attempts"] == 1
    assert totals["reruns"] == 1
    assert totals["heads"] == 2


def test_la_mesure_attribue_la_redondance_a_un_evenement_edited():
    runs = [
        _run(1, "aaa", "2026-11-01T10:00:00Z"),
        _run(2, "aaa", "2026-11-01T10:05:00Z"),
    ]
    edits = {"7": ["2026-11-01T10:04:30Z"]}
    report = measure.analyze(runs, edits)
    assert report["totals"]["redundant_attributed_to_edited"] == 1


def test_la_mesure_ne_attribue_pas_sans_evenement_edited():
    runs = [
        _run(1, "aaa", "2026-11-01T10:00:00Z"),
        _run(2, "aaa", "2026-11-01T10:05:00Z"),
    ]
    edits = {"7": ["2026-11-01T18:00:00Z"]}
    report = measure.analyze(runs, edits)
    assert report["totals"]["redundant_first_attempts"] == 1
    assert report["totals"]["redundant_attributed_to_edited"] == 0


def test_la_mesure_compte_par_workflow():
    runs = [
        _run(1, "aaa", "2026-11-01T10:00:00Z"),
        _run(2, "aaa", "2026-11-01T10:05:00Z"),
        _run(3, "ccc", "2026-11-01T10:00:00Z", path=".github/workflows/y.yml"),
    ]
    report = measure.analyze(runs, {})
    rows = {row["workflow"]: row for row in report["workflows"]}
    assert rows[".github/workflows/x.yml"]["redundant_first_attempts"] == 1
    assert rows[".github/workflows/y.yml"]["redundant_first_attempts"] == 0
