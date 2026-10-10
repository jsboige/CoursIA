"""Regression tests for an unreadable base in the kernel-drift organ (#15553).

The class: the CI checkout is ``fetch-depth: 0`` + ``filter: blob:none``, and
the base branch can advance while the job runs. ``git merge-base`` then fails
with ``Could not read <sha>`` on a base whose commits DO exist on the remote.
The organ used to die on a bare ``RuntimeError`` -- an empty JSON artifact and
a red check-run that a reader of the rollup could not tell apart from a
measured drift.

Measured 2026-10-09 on PR #19853: 3 of 10 sampled failures of this workflow
were this class (branches ``feature/otca-real-grid``,
``feature/14442-gt-intros-sweep``, ``fix/17151-complexity-findings``), while
the same guard went green twice the same day on the very same head.

The remediation mirrors ``scripts/ci/fast_lane.py``, the sibling organ that
closed the same ticket: refetch the exact remote-tracking ref, retry once,
and fail closed with an explicit infrastructure marker if the base is still
unreadable.

Scope of the class (review #20161). The refetch does NOT close the door by
itself: ``--filter=blob:none`` brings COMMITS, while ``git diff --name-only``
reads TREES and ``git show`` reads BLOBS -- and the promisor race is a
property of the partial clone, not of ``merge-base`` alone. Every object
read that follows the base resolution carries the same marking; the tests
below pin the two that were still bare (``changed_notebooks``, ``read_blob``)
as well as the limit of the marking (a legitimately absent blob is not an
infrastructure failure).
"""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import check_kernel_drift as ckd


def _completed(returncode=0, stdout="", stderr="", args=None):
    return subprocess.CompletedProcess(args if args is not None else [],
                                       returncode, stdout, stderr)


def test_unreadable_merge_base_refetches_exact_remote_tracking_ref(monkeypatch):
    calls = []
    results = iter([
        _completed(1, stderr="error: Could not read deadbeef"),
        _completed(0),
        _completed(0, stdout="abc123\n"),
    ])

    def fake_run(cmd, **kwargs):
        calls.append(cmd)
        return next(results)

    monkeypatch.setattr(subprocess, "run", fake_run)

    assert ckd.resolve_base("origin/main") == "abc123"
    assert calls == [
        ["git", "merge-base", "origin/main", "HEAD"],
        ["git", "fetch", "--refetch", "--filter=blob:none", "origin",
         "+refs/heads/main:refs/remotes/origin/main"],
        ["git", "merge-base", "origin/main", "HEAD"],
    ]


def test_unreadable_after_refetch_stays_fail_closed(monkeypatch):
    results = iter([
        _completed(1, stderr="error: Could not read deadbeef"),
        _completed(0),
        _completed(128, stderr="error: Could not read deadbeef"),
    ])
    monkeypatch.setattr(subprocess, "run", lambda *a, **k: next(results))

    with pytest.raises(ckd.BaseUnreadable) as exc:
        ckd.resolve_base("origin/main")

    message = str(exc.value)
    assert "[infrastructure][fail-closed]" in message
    assert "aucun verdict de drift n'a ete calcule" in message
    assert "Could not read deadbeef" in message


def test_refetch_failure_is_fail_closed_and_names_the_fetch_error(monkeypatch):
    results = iter([
        _completed(1, stderr="error: Could not read deadbeef"),
        _completed(128, stderr="fatal: could not fetch"),
    ])
    monkeypatch.setattr(subprocess, "run", lambda *a, **k: next(results))

    with pytest.raises(ckd.BaseUnreadable) as exc:
        ckd.resolve_base("origin/main")

    message = str(exc.value)
    assert "[infrastructure][fail-closed]" in message
    assert "refetch=fatal: could not fetch" in message


def test_non_origin_base_is_not_refetchable_and_stays_fail_closed(monkeypatch):
    """Une base locale n'a pas de ref distant a recharger : fail-closed."""
    results = iter([
        _completed(1, stderr="fatal: Not a valid object name"),
    ])
    monkeypatch.setattr(subprocess, "run", lambda *a, **k: next(results))

    with pytest.raises(ckd.BaseUnreadable) as exc:
        ckd.resolve_base("deadbeef")

    assert "base ref non refetchable" in str(exc.value)


def test_unreadable_base_emits_json_and_rc1(monkeypatch, capsys):
    """Controle negatif de #15553 (acceptance 4) : un remede qui rendrait
    l'organe silencieux serait pire que le rouge."""
    results = iter([
        _completed(1, stderr="error: Could not read deadbeef"),
        _completed(0),
        _completed(128, stderr="error: Could not read deadbeef"),
    ])
    monkeypatch.setattr(subprocess, "run", lambda *a, **k: next(results))

    rc = ckd.main_with_args(["origin/main", "--json"])

    assert rc == 1
    payload = json.loads(capsys.readouterr().out)
    assert payload["findings"] == []
    assert "[infrastructure][fail-closed]" in payload["infrastructure_error"]


def _write_nb(path, version):
    notebook = {
        "cells": [{"cell_type": "code", "execution_count": 1, "id": "c1",
                   "outputs": [], "source": ["1 + 1"]}],
        "metadata": {"kernelspec": {"name": "python3",
                                    "display_name": "Python"},
                     "language_info": {"version": version}},
        "nbformat": 4, "nbformat_minor": 5,
    }
    path.write_text(json.dumps(notebook), encoding="utf-8")


def test_measured_drift_still_fails_the_run(monkeypatch, tmp_path, capsys):
    """Controle positif : base lisible + derive reelle reste un rouge.

    C'est la garde contre le remede qui rendrait l'organe muet.
    """
    def run_git(*args):
        return subprocess.run(["git", *args], cwd=tmp_path, check=True,
                              capture_output=True, text=True,
                              encoding="utf-8", errors="replace")

    run_git("init", "-q")
    run_git("config", "user.email", "t@t")
    run_git("config", "user.name", "t")
    notebook = tmp_path / "nb.ipynb"
    _write_nb(notebook, "3.13.3")
    run_git("add", "nb.ipynb")
    run_git("commit", "-qm", "base")
    base = run_git("rev-parse", "HEAD").stdout.strip()

    _write_nb(notebook, "3.12.0")          # 3.13 -> 3.12 : non canonique
    run_git("commit", "-qam", "drift")

    monkeypatch.chdir(tmp_path)
    monkeypatch.delenv("PR_BODY_FILE", raising=False)

    rc = ckd.main_with_args([base, "--json"])
    payload = json.loads(capsys.readouterr().out)

    assert rc == 1
    assert payload["findings"], "une derive reelle doit rester un rouge"
    assert "infrastructure_error" not in payload


def test_unreadable_diff_is_marked_infrastructure(monkeypatch, capsys):
    """Un `git diff` qui ne resout pas un objet rendait le meme artefact vide.

    `--filter=blob:none` ramene des commits ; le diff lit des arbres. La course
    peut donc frapper cette lecture comme elle frappe `merge-base`.
    """
    results = iter([
        _completed(0, stdout="abc123\n"),                        # merge-base OK
        _completed(1, stderr="error: Could not read deadbeef"),   # diff KO
    ])
    monkeypatch.setattr(subprocess, "run", lambda *a, **k: next(results))

    rc = ckd.main_with_args(["origin/main", "--json"])

    assert rc == 1
    payload = json.loads(capsys.readouterr().out)
    assert payload["findings"] == []
    assert "[infrastructure][fail-closed]" in payload["infrastructure_error"]
    assert "Could not read deadbeef" in payload["infrastructure_error"]
    assert "diff --name-only" in payload["infrastructure_error"]


def test_unreadable_blob_is_marked_infrastructure(monkeypatch, capsys):
    """Idem pour `git show` : le refetch blob:none ne ramene pas les blobs."""
    results = iter([
        _completed(0, stdout="abc123\n"),                        # merge-base OK
        _completed(0, stdout="nb.ipynb\n"),                      # diff : 1 carnet
        _completed(1, stderr="error: Could not read deadbeef"),   # show KO
    ])
    monkeypatch.setattr(subprocess, "run", lambda *a, **k: next(results))

    rc = ckd.main_with_args(["origin/main", "--json"])

    assert rc == 1
    payload = json.loads(capsys.readouterr().out)
    assert payload["findings"] == []
    assert "[infrastructure][fail-closed]" in payload["infrastructure_error"]
    assert "show abc123:nb.ipynb" in payload["infrastructure_error"]


def test_unreadable_diff_raises_base_unreadable(monkeypatch):
    """Le marquage est porte par la lecture elle-meme, pas seulement par _run."""
    monkeypatch.setattr(
        subprocess, "run",
        lambda *a, **k: _completed(1, stderr="error: Could not read deadbeef"))

    with pytest.raises(ckd.BaseUnreadable) as exc:
        ckd.changed_notebooks("abc123")

    message = str(exc.value)
    assert "[infrastructure][fail-closed]" in message
    assert "aucun verdict de drift n'a ete calcule" in message


def test_absent_blob_is_not_an_infrastructure_failure(monkeypatch):
    """Controle negatif du marquage : un blob legitimement absent reste None.

    Sans cette garde, la marque absorberait le chemin normal « ce carnet
    n'existait pas dans la base » -- c'est-a-dire une vraie mesure.
    """
    monkeypatch.setattr(
        subprocess, "run",
        lambda *a, **k: _completed(
            1, stderr="fatal: path 'nb.ipynb' does not exist in 'abc123'"))

    assert ckd.read_blob("abc123", "nb.ipynb") is None
