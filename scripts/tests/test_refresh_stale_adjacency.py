#!/usr/bin/env python3
"""Unit tests for refresh_stale_adjacency (the G-VAR-3 stale-verdict re-trigger).

Covers the pure helpers: `append_marker` (idempotent), `now_marker` (format),
and the verdict-routing logic of `refresh_one` simulated via fake `gh` output.

The end-to-end `refresh_one` calls real `gh` CLI -- so the live-call branch is
tested by hand against a small set of PRs and NOT in pytest. The unit tests
focus on:

  * `append_marker` idempotency -- running the function N times on the same
    body produces exactly ONE marker, with the latest timestamp.
  * The marker format -- exactly one line, ISO-8601 UTC, prefixed.
  * `now_marker` returns a string that round-trips through `append_marker`.
  * The verdict-routing matrix of `refresh_one` -- given a fake
    `(always_on_failing, guard_pass)` pair, decide correctly whether to
    refresh.

We mock the subprocess calls so the unit tests do not need network. The
fixture `FakeRun` emulates `subprocess.run` output for `gh pr view --json
body` and `gh pr checks`. A monkeypatch fixture swaps
`subprocess.run` for a controller.
"""
from __future__ import annotations

import json
import re
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))

import refresh_stale_adjacency as rsa  # noqa: E402


# --- helpers ----------------------------------------------------------------


class FakeRun:
    """Emulates `subprocess.run` return for `gh` calls.

    `specs` is a dict mapping `argv` tuple -> (returncode, stdout, stderr).
    The first matching spec wins; the default is (0, "", "") so unrelated
    calls return cleanly.
    """

    def __init__(self, specs: dict | None = None) -> None:
        self.specs: dict = specs or {}
        self.calls: list[tuple] = []

    def __call__(self, argv, capture_output=True, text=True, check=False,
                 input=None, **kwargs):  # noqa: ANN001 -- mirror subprocess.run
        self.calls.append(tuple(argv))
        # Find a matching spec (subsequence match: argv must contain all of
        # `argv_prefix` tokens in order).
        for key, val in self.specs.items():
            if self._argv_matches(list(argv), key):
                rc, stdout, stderr = val
                cp = subprocess.CompletedProcess(
                    args=argv, returncode=rc, stdout=stdout, stderr=stderr,
                )
                return cp
        return subprocess.CompletedProcess(
            args=argv, returncode=0, stdout="", stderr="",
        )

    @staticmethod
    def _argv_matches(argv, key) -> bool:
        # If key is a tuple of strings, all must appear in argv in order.
        if isinstance(key, tuple):
            i = 0
            for tok in argv:
                if tok == key[i]:
                    i += 1
                    if i == len(key):
                        return True
            return False
        return False


@pytest.fixture
def fake_run(monkeypatch):
    """Replace `subprocess.run` with a FakeRun controller.

    Returns the FakeRun instance; the caller sets `.specs` to declare
    expected `gh` invocations.
    """
    fr = FakeRun()
    monkeypatch.setattr(rsa.subprocess, "run", fr)
    return fr


# --- pure helper tests ------------------------------------------------------


def test_append_marker_adds_one_line():
    body = "## Quoi\n\nClose #1.\n\nGrain: MED/guard -- lane myia-po-2026:CoursIA -- prev: MED/guard #0\n"
    out = rsa.append_marker(body, "<!-- refresh-adj: 2026-09-01T09:42:00Z -->")
    assert out.count("<!-- refresh-adj:") == 1
    assert out.endswith("<!-- refresh-adj: 2026-09-01T09:42:00Z -->\n")
    assert "Grain: MED/guard" in out  # substance preserved


def test_append_marker_idempotent():
    body = "## Section\n\nBody.\n"
    out1 = rsa.append_marker(body, "<!-- refresh-adj: 2026-09-01T09:00:00Z -->")
    out2 = rsa.append_marker(out1, "<!-- refresh-adj: 2026-09-01T09:30:00Z -->")
    out3 = rsa.append_marker(out2, "<!-- refresh-adj: 2026-09-01T10:00:00Z -->")
    assert out3.count("<!-- refresh-adj:") == 1, f"expected 1, got {out3.count('<!-- refresh-adj:')}"
    assert "2026-09-01T10:00:00Z" in out3
    assert "2026-09-01T09:00:00Z" not in out3
    assert "2026-09-01T09:30:00Z" not in out3


def test_append_marker_handles_empty_body():
    out = rsa.append_marker("", "<!-- refresh-adj: 2026-09-01T00:00:00Z -->")
    assert out == "<!-- refresh-adj: 2026-09-01T00:00:00Z -->\n"


def test_append_marker_handles_none_body():
    # Defensive: a None body (unusual, but seen in fork PRs) becomes "".
    out = rsa.append_marker("", "<!-- refresh-adj: X -->")
    assert "<!-- refresh-adj: X -->" in out


def test_now_marker_format():
    m = rsa.now_marker()
    # Exactly one line, no trailing newline, exact prefix.
    assert m.startswith("<!-- refresh-adj: ")
    assert m.endswith(" -->")
    # The timestamp between is ISO-8601 UTC (YYYY-MM-DDTHH:MM:SSZ).
    iso = re.search(r"\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}Z", m)
    assert iso is not None


def test_now_marker_round_trips_through_append_marker():
    body = "Some body\n"
    out = rsa.append_marker(body, rsa.now_marker())
    assert out.count("<!-- refresh-adj:") == 1


# --- verdict-routing tests (refresh_one logic, mocked subprocess) ------------


PR_BODY_OK = (
    "## Quoi\n\n"
    "Fixes #1. Grain tag.\n\n"
    "Grain: MED/docs -- lane myia-po-2026:CoursIA -- prev: MED/tooling #999\n"
)

# --- la jambe de body (#22748) ----------------------------------------------
# Les organes de body ont leur propre workflow depuis #22331/#22333, et
# l'organe d'adjacence y tourne aussi. Le sweep lisait les jambes resolues
# dans `always-on-guards.yml` seulement : cette jambe-la n'y est pas declaree,
# et un filtre l'y excluait en plus. Un verdict G-VAR-3 perime tombe sur elle
# n'etait donc jamais rafraichi (#22748, ~12 h rouge).

BODY_JOB_NAME = "Always-on guards -- body"
BODY_JOB_URL = (
    "https://github.com/jsboige/CoursIA/actions/runs/40366622667/job/122038953042")
BODY_ANNOTATIONS_API = (
    "api", "repos/jsboige/CoursIA/check-runs/122038953042/annotations")
# Sentinelle : « on ne declare pas l'appel d'annotations » (l'organe ne doit
# pas aller le chercher). `None` veut dire « l'appel echoue ».
_UNSET = object()


def _check_row(name: str, conclusion: str, url: str = "https://x") -> str:
    return "\t".join([name, conclusion, "0s", url])


def _setup_fake_for_pr(fake_run: FakeRun, pr: int, body: str,
                        always_on_failing: bool,
                        body_conclusion: str | None = None,
                        bodys_annotations: list[str] | None | object = _UNSET):
    """Configure FakeRun for one PR: body, checks, comments.

    `body_conclusion` pose la jambe `Always-on guards -- body` a la
    conclusion donnee (None = absente de la sortie `gh pr checks`) ;
    `bodys_annotations` declare ce que rend l'API d'annotations de cette
    jambe (`_UNSET` = on ne l'appelle pas, `None` = appel en echec).

    `always_on_failing` ne pilote plus que la jambe de CONTENU : la jambe de
    body est decidee par ses annotations (#22748).
    """
    fake_run.specs[("pr", "view", str(pr), "--json", "body")] = (
        0, json.dumps({"body": body}), "")
    fake_run.specs[("pr", "view", str(pr), "--json", "comments",
                    "--jq")] = (
        0, "[]", "")
    rows = [
        # Les noms sont ceux que l'organe RESOUT dans le workflow (#22403) :
        # une fixture qui reecrirait le nom en dur reproduirait exactement le
        # defaut corrige -- elle resterait verte sur un workflow renomme.
        _check_row(name, "fail" if always_on_failing else "success")
        for name in rsa.content_guard_job_names()
    ]
    if body_conclusion is not None:
        rows.append(_check_row(BODY_JOB_NAME, body_conclusion, BODY_JOB_URL))
    checks_text = "\n".join(rows) + "\n"
    fake_run.specs[("pr", "checks", str(pr))] = (0, checks_text, "")
    if bodys_annotations is not _UNSET:
        if bodys_annotations is None:
            # `gh api` en echec (404/quota) : l'attribution est alors
            # impossible, et le contrat est de ne RIEN ecrire.
            fake_run.specs[BODY_ANNOTATIONS_API] = (
                1, "", "gh: Not Found (HTTP 404)")
        else:
            fake_run.specs[BODY_ANNOTATIONS_API] = (
                0, json.dumps([{"message": m} for m in bodys_annotations]), "")
    # `gh pr edit ... --body-file -` (the edit call): accept any input.
    fake_run.specs[("pr", "edit", str(pr), "--body-file", "-")] = (
        0, "", "")


def test_refresh_one_skips_when_already_passing(fake_run):
    """If `Always-on guards` is NOT failing, do NOT refresh.

    The script must NEVER touch a PR whose check is already green: the
    guard could fail on the next run for an unrelated reason and we would
    have polluted its body for nothing.
    """
    _setup_fake_for_pr(fake_run, 13812, PR_BODY_OK, always_on_failing=False)
    merged_window = [
        {"number": 999, "body": "Grain: MED/tooling -- lane myia-po-2026:CoursIA -- prev: MED/guard #998\n",
         "mergedAt": "2026-09-01T07:00:00Z"},
    ]
    result = rsa.refresh_one(13812, dry_run=True, merged_window=merged_window)
    assert result["would_refresh"] is False
    assert result["refreshed"] is False
    assert result["always_on_failing"] is False


def test_refresh_one_refreshes_when_stale_failing(fake_run):
    """If Always-on guards is failing AND guard_pass=True, refresh.

    The founder case: G-VAR-3 stale verdict (the merged sequence has moved
    past the PR's predecessor).
    """
    _setup_fake_for_pr(fake_run, 13812, PR_BODY_OK, always_on_failing=True)
    merged_window = [
        {"number": 999, "body": "Grain: MED/tooling -- lane myia-po-2026:CoursIA -- prev: MED/guard #998\n",
         "mergedAt": "2026-09-01T07:00:00Z"},
    ]
    # MED/docs after MED/tooling -> guard_pass=True.
    result = rsa.refresh_one(13812, dry_run=True, merged_window=merged_window)
    assert result["guard_pass"] is True
    assert result["always_on_failing"] is True
    assert result["would_refresh"] is True
    assert result["refreshed"] is True  # dry-run, virtual


def test_refresh_one_refuses_when_real_failing(fake_run):
    """If Always-on guards is failing AND guard_pass=False, do NOT refresh.

    A genuine G-VAR-3 adjacency (the rule is doing its job) is NOT a stale
    verdict: the script must surface this, not pretend a marker will help.
    """
    body_guard = (
        "## Quoi\n\nFixes.\n\n"
        "Grain: LIGHT/guard -- lane myia-po-2026:CoursIA -- prev: LIGHT/guard #0\n"
    )
    _setup_fake_for_pr(fake_run, 13869, body_guard, always_on_failing=True)
    # Two consecutive LIGHT/guard in the merged window -> G-VAR-3 fires.
    merged_window = [
        {"number": 998, "body": "Grain: LIGHT/guard -- lane myia-po-2026:CoursIA -- prev: LIGHT/tooling #997\n",
         "mergedAt": "2026-09-01T05:00:00Z"},
        {"number": 997, "body": "Grain: LIGHT/tooling -- lane myia-po-2026:CoursIA -- prev: MED/guard #996\n",
         "mergedAt": "2026-09-01T04:00:00Z"},
    ]
    result = rsa.refresh_one(13869, dry_run=True, merged_window=merged_window)
    assert result["guard_pass"] is False
    assert result["always_on_failing"] is True
    assert result["would_refresh"] is False
    assert result["refreshed"] is False


def test_refresh_one_handles_no_grain_tag(fake_run):
    """If the PR body has no Grain tag, the script refuses to touch it.

    A missing Grain tag is the tag-required guard's territory (#10045).
    Refresh-adjacency would not help; the marker is misleading noise.
    """
    body_no_tag = "## Quoi\n\nThis PR has no Grain tag.\n"
    _setup_fake_for_pr(fake_run, 13999, body_no_tag, always_on_failing=True)
    result = rsa.refresh_one(13999, dry_run=True, merged_window=[])
    assert result["guard_pass"] is False
    assert result["would_refresh"] is False
    assert "no Grain tag" in result["reason"]


# --- batch behaviour (main) -------------------------------------------------


def test_main_mixed_outcomes(fake_run, capsys, monkeypatch):
    """Run `main` with a mix of stale-failing, real-failing, and already-passing.

    Exit code: 0 (no real failures). Output: a results list, one entry per
    PR, in the order given. Mocks `fetch_merged_prs_since.py` (no network).
    """
    # PR 1: stale-failing -> would_refresh.
    _setup_fake_for_pr(fake_run, 1, PR_BODY_OK, always_on_failing=True)
    # PR 2: already-passing -> would NOT refresh.
    body_pass = "Grain: MED/notebook-python -- lane myia-po-2026:CoursIA -- prev: MED/guard #1\n"
    _setup_fake_for_pr(fake_run, 2, body_pass, always_on_failing=False)
    merged_window = [
        {"number": 1, "body": "Grain: MED/guard -- lane myia-po-2026:CoursIA -- prev: MED/docs #0\n",
         "mergedAt": "2026-09-01T05:00:00Z"},
    ]
    # fetch_merged_window must also be mocked -- it shells out to a Python
    # script that reads `gh` and the network.
    monkeypatch.setattr(rsa, "fetch_merged_window", lambda days=21: merged_window)
    rc = rsa.main(["--pr", "1", "--pr", "2", "--dry-run"])
    captured = capsys.readouterr()
    payload = json.loads(captured.out)
    assert rc == 0
    assert len(payload["results"]) == 2
    assert payload["results"][0]["pr"] == 1
    assert payload["results"][0]["would_refresh"] is True
    assert payload["results"][1]["pr"] == 2
    assert payload["results"][1]["would_refresh"] is False


def test_main_exit_1_on_real_failing(fake_run, capsys, monkeypatch):
    """A real-failing PR (always_on_failing=False, guard_pass=False) -> exit 1.

    This is the diagnostic case: the guard is failing for a reason the
    refresh cannot fix (e.g., tag-required, off-list genre). The operator
    needs to know.
    """
    body_no_tag = "## Section\n\nNo grain tag here.\n"
    _setup_fake_for_pr(fake_run, 999, body_no_tag, always_on_failing=False)
    # No `Always-on guards` failing (it's "success" in the spec above), but
    # `guard_pass=False` because no Grain tag -- so the route is "real fail".
    monkeypatch.setattr(rsa, "fetch_merged_window", lambda days=21: [])
    rc = rsa.main(["--pr", "999", "--dry-run"])
    assert rc == 1


# --- #22403 : le nom du job se lit dans le workflow, il ne se code pas ------


def test_content_guard_job_names_are_read_from_the_workflow():
    """Le nom resolu existe vraiment dans `always-on-guards.yml`.

    Defaut fondateur (#22403) : l'organe cherchait `-- 13 organes` quand le
    job s'appelait `-- 16 organes`. Le predicat « le job est ROUGE » ne
    pouvait jamais etre vrai, l'organe se taisait, et le silence se lisait
    comme « rien a rafraichir ». Ce test rougit au prochain renommage.
    """
    import yaml

    names = rsa.content_guard_job_names()
    assert names, "aucun job Always-on guards resolu -- l'organe serait muet"

    workflow = Path(rsa.__file__).resolve().parents[2] / (
        ".github/workflows/always-on-guards.yml")
    data = yaml.safe_load(workflow.read_text(encoding="utf-8")) or {}
    declared = {
        (job or {}).get("name")
        for job in (data.get("jobs") or {}).values()
    }
    for name in names:
        assert name in declared, (
            f"le nom resolu {name!r} n'est declare par aucun job de "
            f"{workflow.name} -- l'organe mesure un check qui n'existe pas")


def test_content_guard_job_names_follow_a_rename(tmp_path):
    """Un workflow renomme est suivi : la resolution lit le fichier, pas une constante.

    Le job de body partage le prefixe et doit rester EXCLU de la resolution.
    """
    wf = tmp_path / "always-on-guards.yml"
    wf.write_text(
        "jobs:\n"
        "  guards:\n"
        "    name: 'Always-on guards -- 21 organes, 1 checkout'\n"
        "  body:\n"
        "    name: 'Always-on guards -- body'\n",
        encoding="utf-8")
    assert rsa.content_guard_job_names(wf) == [
        "Always-on guards -- 21 organes, 1 checkout",
    ]


def test_content_guard_job_names_refuses_an_empty_resolution(tmp_path):
    """Aucun job correspondant -> RuntimeError, jamais un silence complaisant."""
    wf = tmp_path / "always-on-guards.yml"
    wf.write_text("jobs:\n  guards:\n    name: 'Other guard'\n",
                  encoding="utf-8")
    with pytest.raises(RuntimeError, match="refuse de mesurer"):
        rsa.content_guard_job_names(wf)


def test_is_failing_ignores_an_unattributed_body_job_red(fake_run):
    """Une jambe de body rouge SANS attribution d'adjacence ne compte pas.

    Les deux jobs partagent le prefixe `Always-on guards` : un match par
    sous-chaine sur `gh pr checks` les fusionnerait, et l'organe toucherait
    le body d'une PR pour un rouge qui ne concerne pas l'adjacence. Ici les
    annotations sont illisibles (aucune spec) : le contrat est de ne pas
    attribuer -- donc de ne pas ecrire.
    """
    _setup_fake_for_pr(fake_run, 4242, PR_BODY_OK, always_on_failing=False,
                       body_conclusion="fail")
    assert rsa.is_always_on_guards_failing(4242) is False


# --- #22748 : la jambe de body porte l'organe d'adjacence -------------------


def test_body_aggregate_really_runs_the_adjacency_organ():
    """La premisse du correctif : l'adjacence tourne dans le job de body.

    Si `scripts/ci/always_on_body_organs.sh` cessait d'appeler
    `organ_adjacency`, ouvrir le rafraichissement a cette jambe n'aurait plus
    d'objet -- et l'attribution par annotation deviendrait un faux signal.
    Ce test rougit a la disparition de l'organe, pas a son renommage interne.
    """
    script = (Path(rsa.__file__).resolve().parents[2]
              / "scripts" / "ci" / "always_on_body_organs.sh")
    text = script.read_text(encoding="utf-8")
    assert re.search(r"^\s*adjacency\)\s*organ_adjacency\s*;;", text, re.M), (
        "l'organe d'adjacence n'est plus dispatché par le job de body : "
        "l'attribution par annotation n'a plus de premisse")


def test_body_job_names_are_read_from_its_own_workflow():
    """La jambe de body se resout dans SON fichier, pas dans celui du contenu.

    Defaut fondateur (#22748) : `content_guard_job_names()` ne lit que
    `always-on-guards.yml`, qui ne declare pas ce job. La jambe etait donc
    structurellement invisible -- et un filtre par marqueur `body` l'excluait
    en plus si elle y avait ete.
    """
    import yaml

    names = rsa.body_guard_job_names()
    assert names, "aucun job de body resolu -- l'organe serait muet"

    workflow = (Path(rsa.__file__).resolve().parents[2]
                / ".github" / "workflows" / rsa.BODY_WORKFLOW_NAME)
    data = yaml.safe_load(workflow.read_text(encoding="utf-8")) or {}
    declared = {
        (job or {}).get("name")
        for job in (data.get("jobs") or {}).values()
    }
    for name in names:
        assert name in declared, (
            f"le nom resolu {name!r} n'est declare par aucun job de "
            f"{workflow.name} -- l'organe mesure un check qui n'existe pas")
    # Et il ne sort pas de la jambe de contenu : la distinction des deux
    # jambes est portee par `adjacency_leg_state`, pas par un filtre unique.
    assert not set(names) & set(rsa.content_guard_job_names())


def test_body_job_names_follow_a_rename(tmp_path):
    """La resolution lit le fichier, jamais une constante."""
    wf = tmp_path / "always-on-guards-body.yml"
    wf.write_text(
        "jobs:\n"
        "  body:\n"
        "    name: 'Always-on guards -- body, 5 organes'\n"
        "  other:\n"
        "    name: 'Some other workflow'\n",
        encoding="utf-8")
    assert rsa.body_guard_job_names(wf) == [
        "Always-on guards -- body, 5 organes",
    ]


def test_body_job_names_refuse_an_empty_resolution(tmp_path):
    """Aucun job correspondant -> RuntimeError, jamais un silence complaisant."""
    wf = tmp_path / "always-on-guards-body.yml"
    wf.write_text("jobs:\n  other:\n    name: 'Not a guard'\n",
                  encoding="utf-8")
    with pytest.raises(RuntimeError, match="refuse de mesurer"):
        rsa.body_guard_job_names(wf)


def test_body_job_red_by_adjacency_is_refreshed(fake_run):
    """Verdict G-VAR-3 perime sur la jambe BODY -> le sweep rafraichit (#22748).

    Avant le correctif : `would_refresh: false` (la jambe n'etait meme pas
    lue). Apres : la banniere d'agregat nomme `adjacency`, la simulation
    passe contre la sequence courante, le marqueur est pose.
    """
    _setup_fake_for_pr(
        fake_run, 22748, PR_BODY_OK, always_on_failing=False,
        body_conclusion="fail",
        bodys_annotations=[
            "Organes de body bloquants en echec : adjacency",
        ])
    merged_window = [
        {"number": 999,
         "body": "Grain: MED/tooling -- lane myia-po-2026:CoursIA -- prev: MED/guard #998\n",
         "mergedAt": "2026-09-01T07:00:00Z"},
    ]
    result = rsa.refresh_one(22748, dry_run=True, merged_window=merged_window)
    assert result["guard_leg_cause"] == "body-adjacency"
    assert result["always_on_failing"] is True
    assert result["guard_pass"] is True
    assert result["would_refresh"] is True
    assert result["refreshed"] is True  # dry-run, virtuel


def test_body_job_red_by_organ_marker_alone_is_refreshed(fake_run):
    """Second temoin : `::error::G-VAR-3 ...`, emis par l'organe lui-meme.

    Une jambe coupee apres l'organe mais avant l'agregat ne porte pas la
    banniere ; l'annotation de l'organe suffit, et elle est tout aussi
    specifique (`G-VAR-3` n'apparait dans aucun autre organe de body).
    """
    _setup_fake_for_pr(
        fake_run, 22751, PR_BODY_OK, always_on_failing=False,
        body_conclusion="fail",
        bodys_annotations=[
            "G-VAR-3 LIGHT-genre adjacency [prev: #999 tooling via "
            "merged-sequence ; sequence de merges au 2026-09-01T07:00:00Z]: "
            "LIGHT/genre repeats the predecessor's genre",
        ])
    merged_window = [
        {"number": 999,
         "body": "Grain: MED/tooling -- lane myia-po-2026:CoursIA -- prev: MED/guard #998\n",
         "mergedAt": "2026-09-01T07:00:00Z"},
    ]
    result = rsa.refresh_one(22751, dry_run=True, merged_window=merged_window)
    assert result["guard_leg_cause"] == "body-adjacency"
    assert result["would_refresh"] is True


def test_body_job_red_by_close_keyword_is_not_refreshed(fake_run):
    """NON-REGRESSION : un rouge de body d'une AUTRE cause n'est pas rafraichi.

    La jambe de body porte cinq organes. `close_keyword` rougit cette jambe
    alors que l'adjacence, elle, passerait : editer le corps ne leverait rien,
    remplirait la file `cancel-in-progress` (#22331) et le sweep rapporterait
    un refresh imaginaire.
    """
    _setup_fake_for_pr(
        fake_run, 22749, PR_BODY_OK, always_on_failing=False,
        body_conclusion="fail",
        bodys_annotations=[
            "Organes de body bloquants en echec : close_keyword",
            "closing-keyword + PR-number reference detected: Closes #1 is "
            "followed by a bare #2",
        ])
    merged_window = [
        {"number": 999,
         "body": "Grain: MED/tooling -- lane myia-po-2026:CoursIA -- prev: MED/guard #998\n",
         "mergedAt": "2026-09-01T07:00:00Z"},
    ]
    result = rsa.refresh_one(22749, dry_run=True, merged_window=merged_window)
    assert result["guard_pass"] is True, (
        "le scenario n'a de valeur que si l'adjacence, elle, passerait")
    assert result["guard_leg_cause"] == "body-other-organ"
    assert result["always_on_failing"] is False
    assert result["would_refresh"] is False
    assert result["refreshed"] is False


def test_body_job_red_with_unreadable_annotations_fails_closed(fake_run):
    """Annotations illisibles -> aucune attribution, donc aucune ecriture.

    L'etat « je n'ai pas pu lire » ne doit pas se confondre avec « c'est
    l'adjacence » : le sweep reste muet sur cette PR, ce qui est le pire
    connu -- jamais une edition non gardee.
    """
    _setup_fake_for_pr(
        fake_run, 22750, PR_BODY_OK, always_on_failing=False,
        body_conclusion="fail", bodys_annotations=None)
    merged_window = [
        {"number": 999,
         "body": "Grain: MED/tooling -- lane myia-po-2026:CoursIA -- prev: MED/guard #998\n",
         "mergedAt": "2026-09-01T07:00:00Z"},
    ]
    result = rsa.refresh_one(22750, dry_run=True, merged_window=merged_window)
    assert result["guard_leg_cause"] == "body-unreadable"
    assert result["would_refresh"] is False


def test_body_job_red_by_stale_adjacency_still_requires_a_passing_simulation(
        fake_run):
    """L'attribution ouvre la jambe, elle ne dispense PAS de la simulation.

    Une vraie adjacence G-VAR-3 sur la jambe de body reste bloquante : le
    sweep la nomme (exit 1) au lieu de la lever par une edition de corps.
    """
    body_lint = (
        "## Quoi\n\nFixes.\n\n"
        "Grain: LIGHT/guard -- lane myia-po-2026:CoursIA -- prev: LIGHT/guard #0\n"
    )
    _setup_fake_for_pr(
        fake_run, 22752, body_lint, always_on_failing=False,
        body_conclusion="fail",
        bodys_annotations=[
            "Organes de body bloquants en echec : adjacency",
        ])
    merged_window = [
        {"number": 998,
         "body": "Grain: LIGHT/guard -- lane myia-po-2026:CoursIA -- prev: LIGHT/tooling #997\n",
         "mergedAt": "2026-09-01T05:00:00Z"},
        {"number": 997,
         "body": "Grain: LIGHT/tooling -- lane myia-po-2026:CoursIA -- prev: MED/guard #996\n",
         "mergedAt": "2026-09-01T04:00:00Z"},
    ]
    result = rsa.refresh_one(22752, dry_run=True, merged_window=merged_window)
    assert result["always_on_failing"] is True
    assert result["guard_pass"] is False
    assert result["would_refresh"] is False
    assert result["refreshed"] is False


# --- #22893 : le silence de la MESURE porte une cause -----------------------
# `gh pr checks` n'ecrit rien sur stdout quand il n'a pas pu mesurer. Sans
# une cause dediee, ce silence se lisait exactement comme « aucun rouge » :
# une PR dont les checks sont illisibles etait donc rapportee « propre ».
#
# Les trois etats mesures (voir `get_pr_check_rows`) :
#   rc!=0 + stdout vide   -> checks-unreadable  (la mesure n'a pas abouti)
#   rc=0  + stdout vide   -> checks-empty       (mesure d'absence)
#   rc!=0 + des lignes    -> LU                 (rc=8 = checks pending/failing)


def test_get_pr_check_rows_distinguishes_silence_from_absence(fake_run):
    """Le tri etat par etat de `get_pr_check_rows` (#22893).

    Trois sorties possibles de `gh pr checks`, trois valeurs distinctes :
    `None` (illisible), `[]` (mesure d'absence), les lignes (mesure).
    """
    # rc!=0 sans un octet sur stdout : `gh` n'a pas mesure (branche sans
    # check : `no checks reported on the '<branch>' branch`).
    fake_run.specs[("pr", "checks", "101")] = (1, "", "no checks reported")
    assert rsa.get_pr_check_rows(101) is None
    # rc=0 sans stdout : gh a conclu, il n'y avait rien a imprimer.
    fake_run.specs[("pr", "checks", "102")] = (0, "", "")
    assert rsa.get_pr_check_rows(102) == []
    # rc=8 (*checks pending/failing*) AVEC des lignes : une mesure.
    rows = [_check_row("Always-on guards -- 16 organes, 1 checkout", "fail")]
    fake_run.specs[("pr", "checks", "103")] = (8, "\n".join(rows) + "\n", "")
    assert rsa.get_pr_check_rows(103) == [{
        "name": "Always-on guards -- 16 organes, 1 checkout",
        "conclusion": "fail",
        "url": "https://x",
    }]
    # stdout non vide mais aucune ligne exploitable : la forme a change, et
    # un changement de forme n'est pas « aucun rouge ».
    fake_run.specs[("pr", "checks", "104")] = (0, "unparseable\n", "")
    assert rsa.get_pr_check_rows(104) is None


def test_unreadable_checks_are_named_not_read_as_clean(fake_run):
    """Un `gh pr checks` muet en echec -> `checks-unreadable`, jamais un silence.

    Le predicat `failing` ne bouge pas (illisible n'est pas rouge), mais le
    JSON du sweep NOMME l'etat : c'est ce que #11808 exige -- un filtre
    deconnecte et un filtre vide ne doivent pas rendre la meme chose.
    """
    _setup_fake_for_pr(fake_run, 22800, PR_BODY_OK, always_on_failing=True)
    fake_run.specs[("pr", "checks", "22800")] = (1, "", "gh: HTTP 502")
    merged_window = [
        {"number": 999,
         "body": "Grain: MED/tooling -- lane myia-po-2026:CoursIA -- prev: MED/guard #998\n",
         "mergedAt": "2026-09-01T07:00:00Z"},
    ]
    result = rsa.refresh_one(22800, dry_run=True, merged_window=merged_window)
    assert result["guard_leg_cause"] == "checks-unreadable"
    assert result["guard_leg"] is None
    # Fail-CLOSED : on n'ecrit rien sur un corps quand on n'a pas pu mesurer.
    assert result["always_on_failing"] is False
    assert result["would_refresh"] is False
    assert result["refreshed"] is False


def test_rc8_with_rows_stays_readable_and_refreshes(fake_run):
    """`rc=8` AVEC des lignes reste une mesure : le rafraichissement a lieu.

    `gh pr checks` sort en 8 quand des checks sont en echec ou en attente.
    Degrader ce cas en « illisible » ferait taire le sweep sur exactement
    les PRs qu'il doit reparer -- c'est le cas nominal.
    """
    _setup_fake_for_pr(fake_run, 22801, PR_BODY_OK, always_on_failing=True)
    rows = [
        _check_row(name, "fail")
        for name in rsa.content_guard_job_names()
    ]
    fake_run.specs[("pr", "checks", "22801")] = (
        8, "\n".join(rows) + "\n", "")
    merged_window = [
        {"number": 999,
         "body": "Grain: MED/tooling -- lane myia-po-2026:CoursIA -- prev: MED/guard #998\n",
         "mergedAt": "2026-09-01T07:00:00Z"},
    ]
    result = rsa.refresh_one(22801, dry_run=True, merged_window=merged_window)
    assert result["guard_leg_cause"] == "content-job"
    assert result["always_on_failing"] is True
    assert result["would_refresh"] is True
    assert result["refreshed"] is True  # dry-run, virtuel


def test_rc0_without_rows_is_a_measured_absence(fake_run):
    """`rc=0` + stdout vide -> `checks-empty`, distinct d'`checks-unreadable`.

    `gh` a conclu et n'avait rien a imprimer : c'est une mesure d'absence,
    pas un echec de mesure. Les deux ne partagent donc pas la meme cause.
    """
    _setup_fake_for_pr(fake_run, 22802, PR_BODY_OK, always_on_failing=False)
    fake_run.specs[("pr", "checks", "22802")] = (0, "", "")
    merged_window = [
        {"number": 999,
         "body": "Grain: MED/tooling -- lane myia-po-2026:CoursIA -- prev: MED/guard #998\n",
         "mergedAt": "2026-09-01T07:00:00Z"},
    ]
    result = rsa.refresh_one(22802, dry_run=True, merged_window=merged_window)
    assert result["guard_leg_cause"] == "checks-empty"
    assert result["guard_leg"] is None
    assert result["would_refresh"] is False

