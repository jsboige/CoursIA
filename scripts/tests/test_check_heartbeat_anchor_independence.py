from __future__ import annotations

import base64
import sys
from pathlib import Path

CI_DIR = Path(__file__).resolve().parents[1] / "ci"
sys.path.insert(0, str(CI_DIR))

import check_heartbeat_anchor_independence as chi  # noqa: E402
import check_runner_starvation as rs  # noqa: E402


def fake_api(workflows, runs_by_id, jobs_by_run, files_by_path=None):
    """Fabrique un faux `_gh_json` a partir de tables explicites.

    `workflows` : liste de dicts (name/id/path) telle que la rend l'API,
    repartie en pages de 100 -- c'est la pagination reelle qui est simulee,
    pas une liste plate, parce que le depot en compte 169 au 2026-10-29 et
    qu'une seule page rendait « introuvable » un workflow existant.
    `files_by_path` : contenu des fichiers de workflow (le bloc `on:` declare,
    relu par l'organe depuis l'API contents -- review #23280).
    """
    calls = {"n": 0}
    files_by_path = files_by_path or {}
    vars_value = ["false"]

    def api(args, token=None, stats=None):
        calls["n"] += 1
        endpoint = args[0]
        if endpoint.endswith("/actions/variables/CI_OVERFLOW_LOCAL"):
            return {"name": "CI_OVERFLOW_LOCAL", "value": vars_value[0]}
        if endpoint.startswith("repos/") and "/actions/workflows?" in endpoint:
            page = int(endpoint.rsplit("page=", 1)[1]) if "page=" in endpoint else 1
            chunk = workflows[(page - 1) * 100: page * 100]
            return {"total_count": len(workflows), "workflows": chunk}
        if "/contents/" in endpoint:
            path = endpoint.split("/contents/", 1)[1]
            text = files_by_path.get(path)
            if text is None:
                return {"message": "Not Found"}
            return {"content": base64.b64encode(text.encode()).decode(),
                    "encoding": "base64"}
        if "/actions/runs/" in endpoint and "/jobs" in endpoint:
            run_id = int(endpoint.split("/actions/runs/")[1].split("/")[0])
            return {"jobs": [{"labels": labels}
                             for labels in jobs_by_run.get(run_id, [])]}
        if "/actions/workflows/" in endpoint and "/runs" in endpoint:
            wf_id = int(endpoint.split("/actions/workflows/")[1].split("/")[0])
            return {"workflow_runs": runs_by_id.get(wf_id, [])}
        return None

    api.calls = calls
    return api


def run(monkeypatch, api, advisory_text, tmp_path, runs=3):
    monkeypatch.setattr(chi, "_gh_json", api)
    path = tmp_path / "advisory.yml"
    path.write_text(advisory_text, encoding="utf-8")
    verdict = chi.evaluate("o/r", [path], runs, rs.CallStats())
    return verdict


def wf_entry(name, wf_id):
    return {"name": name, "id": wf_id,
            "path": f".github/workflows/{name.lower()}.yml"}


ON_PR = "name: A\non: [pull_request]\njobs:\n  x:\n    runs-on: ubuntu-latest\n"
ON_PR_B = "name: B\non: [push]\njobs:\n  x:\n    runs-on: ubuntu-latest\n"
ON_DISPATCH = ("name: A\non: [workflow_dispatch]\njobs:\n  x:\n"
               "    runs-on: ubuntu-latest\n")
ON_SCHED_DISPATCH = ("name: A\non:\n  schedule:\n    - cron: '0 * * * *'\n"
                     "  workflow_dispatch:\njobs:\n  x:\n"
                     "    runs-on: ubuntu-latest\n")

ADVISORY = """name: X

on:
  schedule:
    - cron: '0 * * * *'
  workflow_run:
    workflows: ["A", "B"]
    types: [completed]

permissions:
  contents: read

jobs:
  x:
    runs-on: ubuntu-latest
    steps:
      - run: echo hi
"""

ADVISORY_BLOCK_LIST = """name: X

on:
  workflow_run:
    workflows:
      - "A"
      - "B"
    types: [completed]

jobs:
  x:
    runs-on: ubuntu-latest
"""


def test_parses_anchor_names_from_real_advisories():
    root = Path(__file__).resolve().parents[2]
    for rel in chi.DEFAULT_ADVISORIES:
        names = chi.load_anchor_names(root / rel)
        assert names == ["Secret Scan", "Enrich-quality gate"], rel


def test_parses_anchor_names_from_block_form_list():
    """Cas C de la review #23280 : la forme bloc est celle qu'un `yaml.dump`
    produit -- ne lire que l'inline y rend `[]`, donc UNKNOWN en silence."""
    import tempfile
    with tempfile.TemporaryDirectory() as d:
        p = Path(d) / "advisory.yml"
        p.write_text(ADVISORY_BLOCK_LIST, encoding="utf-8")
        assert chi.load_anchor_names(p) == ["A", "B"]


def test_declared_events_reads_scalar_inline_and_block_forms():
    assert chi._declared_events("on: push\n") == ["push"]
    assert chi._declared_events("on: [push, pull_request]\n") == [
        "push", "pull_request"]
    block = ("on:\n  schedule:\n    - cron: '0 * * * *'\n"
             "  workflow_run:\n    workflows: [\"X\"]\n"
             "  pull_request:\n    branches:\n      - main\n")
    assert chi._declared_events(block) == [
        "schedule", "workflow_run", "pull_request"]


def test_hosted_anchor_declared_pr_is_a_leg(monkeypatch, tmp_path):
    api = fake_api(
        workflows=[wf_entry("A", 11), wf_entry("B", 22)],
        runs_by_id={11: [{"id": 1, "event": "pull_request"}], 22: []},
        jobs_by_run={1: [["ubuntu-latest"], ["ubuntu-latest"]]},
        files_by_path={".github/workflows/a.yml": ON_PR,
                       ".github/workflows/b.yml": ON_PR_B},
    )
    verdict = run(monkeypatch, api, ADVISORY, tmp_path)
    assert verdict.verdict == "ANCHOR_PROVED"
    leg = [a for a in verdict.anchors if a.is_leg]
    assert [a.name for a in leg] == ["A"]


def test_all_self_hosted_means_no_leg(monkeypatch, tmp_path):
    api = fake_api(
        workflows=[wf_entry("A", 11), wf_entry("B", 22)],
        runs_by_id={11: [{"id": 1, "event": "pull_request"}],
                    22: [{"id": 2, "event": "push"}]},
        jobs_by_run={1: [["self-hosted", "coursia-linux"]],
                     2: [["self-hosted", "coursia-waiter"]]},
        files_by_path={".github/workflows/a.yml": ON_PR,
                       ".github/workflows/b.yml": ON_PR_B},
    )
    verdict = run(monkeypatch, api, ADVISORY, tmp_path)
    assert verdict.verdict == "NO_HOSTED_LEG"
    assert all(not a.is_leg for a in verdict.anchors)


def test_hosted_but_dispatch_only_is_not_a_leg(monkeypatch, tmp_path):
    """100 % heberge ne suffit pas : un workflow_dispatch ne se declenche pas seul."""
    api = fake_api(
        workflows=[wf_entry("A", 11), wf_entry("B", 22)],
        runs_by_id={11: [{"id": 1, "event": "workflow_dispatch"}], 22: []},
        jobs_by_run={1: [["ubuntu-latest"]]},
        files_by_path={".github/workflows/a.yml": ON_DISPATCH,
                       ".github/workflows/b.yml": ON_PR_B},
    )
    verdict = run(monkeypatch, api, ADVISORY, tmp_path)
    assert verdict.verdict == "NO_HOSTED_LEG"


def test_window_dispatch_does_not_flip_a_declared_pr_leg(monkeypatch, tmp_path):
    """Cas A de la review #23280 : ancre declaree `pull_request`, fenetre de 3
    runs 100 % `workflow_dispatch`. L'ancien predicat (evenements de la
    fenetre) rendait False -- faux rouge : GitHub declenche bien l'ancre sur
    chaque PR, la fenetre n'a juste pas vu de PR."""
    api = fake_api(
        workflows=[wf_entry("A", 11)],
        runs_by_id={11: [{"id": 1, "event": "workflow_dispatch"},
                         {"id": 2, "event": "workflow_dispatch"},
                         {"id": 3, "event": "workflow_dispatch"}]},
        jobs_by_run={1: [["ubuntu-latest"]], 2: [["ubuntu-latest"]],
                     3: [["ubuntu-latest"]]},
        files_by_path={".github/workflows/a.yml": ON_PR},
    )
    verdict = run(monkeypatch, api, ADVISORY, tmp_path)
    anchor = verdict.anchors[0]
    assert anchor.declared_triggers == ["pull_request"]
    assert anchor.triggers == ["workflow_dispatch"]
    assert anchor.is_leg
    assert verdict.verdict == "ANCHOR_PROVED"


def test_declared_dispatch_window_push_is_not_a_leg(monkeypatch, tmp_path):
    """Cas B de la review #23280, en sa variante fausse-verte : ancre declaree
    `schedule` + `workflow_dispatch` (jamais `push`), fenetre 100 % `push`.
    L'ancien predicat rendait True sur l'evenement observe -- faux vert :
    l'ancre ne se declenche pas sur push, la jambe n'existe pas."""
    api = fake_api(
        workflows=[wf_entry("A", 11)],
        runs_by_id={11: [{"id": 1, "event": "push"}]},
        jobs_by_run={1: [["ubuntu-latest"]]},
        files_by_path={".github/workflows/a.yml": ON_SCHED_DISPATCH},
    )
    verdict = run(monkeypatch, api, ADVISORY, tmp_path)
    anchor = verdict.anchors[0]
    assert anchor.declared_triggers == ["schedule", "workflow_dispatch"]
    assert anchor.triggers == ["push"]
    assert not anchor.is_leg
    assert verdict.verdict == "NO_HOSTED_LEG"


def test_unreadable_on_block_is_an_error_not_a_false_red(monkeypatch, tmp_path):
    """Un bloc `on:` illisible met l'ancre en erreur (vers UNKNOWN), pas en
    faux NO_HOSTED_LEG -- un instrument aveugle n'est pas un rouge (#14849)."""
    api = fake_api(
        workflows=[wf_entry("A", 11)],
        runs_by_id={11: [{"id": 1, "event": "pull_request"}]},
        jobs_by_run={1: [["ubuntu-latest"]]},
        files_by_path={".github/workflows/a.yml": "name: A\njobs:\n  x:\n"},
    )
    verdict = run(monkeypatch, api, ADVISORY, tmp_path)
    assert verdict.anchors[0].error == "bloc on: illisible"
    assert verdict.verdict == "UNKNOWN"


def test_workflow_on_second_page_is_found(monkeypatch, tmp_path):
    """Regression : 169 workflows au depot, l'API pagine a 100.

    Une seule page rendait « introuvable par nom » un workflow qui existe --
    l'organe fabriquait le faux negatif qu'il est cense attraper.
    """
    filler = [{"name": f"W{i}", "id": 1000 + i} for i in range(100)]
    api = fake_api(
        workflows=filler + [wf_entry("A", 11)],
        runs_by_id={11: [{"id": 1, "event": "push"}]},
        jobs_by_run={1: [["ubuntu-latest"]]},
        files_by_path={".github/workflows/a.yml": ON_PR},
    )
    verdict = run(monkeypatch, api, "on:\n  workflow_run:\n    workflows: [\"A\"]\n    types: [completed]\n\njobs:\n  x:\n    runs-on: ubuntu-latest\n", tmp_path)
    anchor = verdict.anchors[0]
    assert anchor.error is None
    assert anchor.workflow_id == 11
    assert verdict.verdict == "ANCHOR_PROVED"


def test_overflow_mode_is_named_not_inferred(monkeypatch, tmp_path):
    """Vague #23016 : quand CI_OVERFLOW_LOCAL=true, les ancres hybrides
    basculent sur le parc -- le verdict reste NO_HOSTED_LEG (la jambe
    n'existe pas), mais le mode est LU et rapporte, pas devine."""
    api = fake_api(
        workflows=[wf_entry("A", 11)],
        runs_by_id={11: [{"id": 1, "event": "pull_request"}]},
        jobs_by_run={1: [["self-hosted", "coursia-linux"]]},
        files_by_path={".github/workflows/a.yml": ON_PR},
    )

    def api_with_var_true(args, token=None, stats=None):
        if args[0].endswith("/actions/variables/CI_OVERFLOW_LOCAL"):
            return {"name": "CI_OVERFLOW_LOCAL", "value": "true"}
        return api(args, token=token, stats=stats)

    monkeypatch.setattr(chi, "_gh_json", api_with_var_true)
    path = tmp_path / "advisory.yml"
    path.write_text(ADVISORY, encoding="utf-8")
    verdict = chi.evaluate("o/r", [path], 3, rs.CallStats())
    assert verdict.verdict == "NO_HOSTED_LEG"
    assert verdict.ci_overflow_local is True
    assert "ci_overflow_local=true" in chi.render_text(verdict)


def test_blind_api_is_unknown_not_red(monkeypatch, tmp_path):
    api = fake_api(workflows=[], runs_by_id={}, jobs_by_run={})
    verdict = run(monkeypatch, api, ADVISORY, tmp_path)
    assert verdict.verdict == "UNKNOWN"
    assert chi.main.__module__ == chi.__name__
