#!/usr/bin/env python3
"""Tests for `scripts/notebook_tools/credited_examples_sweep.py` (#19101).

Le balayage est concu pour etre injectable : `sweep()` prend ses appels
reseau et git en parametres, donc tout se teste hors ligne. Les controles
epinglent les trois pieges qui rendraient le balayage trompeur :

  - un lot qui ATTEINT le plafond de l'API de recherche n'est pas un compte ;
  - le label ne se pose que si TOUS les diffs ont reussi (#18761) ;
  - un merge-base indisponible est NOMME, jamais un diff silencieux contre la
    mauvaise base.
"""
from __future__ import annotations

import datetime as dt
import importlib.util
import sys
from pathlib import Path

_SCRIPT = Path(__file__).resolve().parent.parent / "notebook_tools" / "credited_examples_sweep.py"
_spec = importlib.util.spec_from_file_location("credited_examples_sweep", _SCRIPT)
assert _spec and _spec.loader, f"could not load {_SCRIPT}"
_mod = importlib.util.module_from_spec(_spec)
sys.modules["credited_examples_sweep"] = _mod
_spec.loader.exec_module(_mod)

NOW = dt.datetime(2026, 10, 5, 12, 0, tzinfo=dt.timezone.utc)


class _FakeResult:
    def __init__(self, lost=0, diff_errors=0):
        self._s = {
            "credited_lost_unexempted": lost,
            "credited_diff_errors": diff_errors,
        }

    def as_payload(self):
        return {"summary": self._s}


def _pr(number, files=None, base="a" * 40, head="b" * 40):
    return {
        "number": number,
        "baseRefOid": base,
        "headRefOid": head,
        "files": files or [],
        "mergedAt": NOW.isoformat(),
    }


def _nb(path, change="MODIFIED"):
    return {"path": path, "changeType": change}


IPY = "MyIA.AI.Notebooks/Search/Part1/x.ipynb"
MD = "MyIA.AI.Notebooks/Search/Part1/README.md"


def _run_sweep(prs):
    """Drive `sweep` with the network and git fully injected (offline)."""
    return _mod.sweep(
        "o/r", Path("."), 24, NOW,
        fetch_merged=lambda repo, since: prs,
        fetch_body=lambda repo, number: "",
        base_of=lambda repo_dir, b, h: "deadbeef",
        check=lambda paths, base_ref="", head_ref="", pr_body="": _FakeResult(),
    )


class TestFiltering:
    def test_only_ipynb_paths_are_kept(self):
        pr = _pr(1, [_nb(IPY), _nb(MD)])
        assert _mod.ipynb_paths(pr) == [IPY]

    def test_deleted_notebooks_are_excluded(self):
        """Un carnet supprime n'a plus rien a compter (--diff-filter=d)."""
        pr = _pr(1, [_nb(IPY, "DELETED")])
        assert _mod.ipynb_paths(pr) == []

    def test_added_notebooks_are_not_measured(self):
        """Un carnet neuf n'existe pas dans la base : `git show` sort en 128.

        Ce n'est PAS une erreur de mesure (#18761) -- et la compter comme telle
        bloquait le label pour les carnets MODIFIES de la meme PR.
        """
        pr = _pr(1, [_nb(IPY, "ADDED")])
        assert _mod.ipynb_paths(pr) == []
        modified, added, renamed = _mod._ipynb_by_change(pr)
        assert modified == [] and added == [IPY] and renamed == []

    def test_added_and_modified_split_in_the_same_pr(self):
        other = "MyIA.AI.Notebooks/Search/Part1/y.ipynb"
        pr = _pr(1, [_nb(other, "ADDED"), _nb(IPY, "MODIFIED")])
        modified, added, renamed = _mod._ipynb_by_change(pr)
        assert modified == [IPY] and added == [other] and renamed == []

    def test_a_purely_additive_pr_is_named_not_dropped(self):
        rows, errs = _run_sweep([_pr(1, [_nb(IPY, "ADDED")])])
        assert len(rows) == 1 and rows[0]["notebooks"] == 0
        assert rows[0]["added_notebooks"] == 1
        assert rows[0]["would_label"] is False
        assert errs == []

    def test_a_renamed_notebook_is_declared_unmeasured_not_lost_free(self):
        """Un renommage PEUT perdre des exemples : on ne le dit pas « sans perte ».

        La base est a un autre chemin (`previousFilename` non expose par
        `gh pr view --json files`), donc la comparaison est impossible. Le
        carnet ne doit ni etre mesure contre le mauvais chemin, ni etre tu.
        """
        pr = _pr(1, [_nb(IPY, "RENAMED")])
        assert _mod.ipynb_paths(pr) == []
        modified, added, renamed = _mod._ipynb_by_change(pr)
        assert modified == [] and added == [] and renamed == [IPY]
        rows, errs = _run_sweep([pr])
        assert len(rows) == 1 and rows[0]["renamed_notebooks"] == 1
        assert rows[0]["notebooks"] == 0
        assert rows[0]["would_label"] is False

    def test_a_renamed_notebook_does_not_block_the_other_notebooks(self):
        """Le faux positif d'erreur produisait un faux zero de pertes (#18761).

        Un carnet renomme dans la meme PR ne doit plus empecher la mesure des
        carnets modifies -- c'est le defaut que la separation corrige.
        """
        other = "MyIA.AI.Notebooks/Search/Part1/y.ipynb"
        pr = _pr(1, [_nb(other, "RENAMED"), _nb(IPY, "MODIFIED")])

        def check(paths, base_ref="", head_ref="", pr_body=""):
            assert [str(p).endswith("x.ipynb") for p in paths] == [True], paths
            return _FakeResult(lost=2, diff_errors=0)

        rows, errs = _mod.sweep(
            "o/r", Path("."), 24, NOW,
            fetch_merged=lambda repo, since: [pr],
            fetch_body=lambda repo, number: "",
            base_of=lambda *a: "deadbeef",
            check=check,
        )
        assert rows[0]["would_label"] is True, rows
        assert rows[0]["renamed_notebooks"] == 1
        assert errs == []

    def test_a_pr_without_notebook_is_skipped_by_the_sweep(self):
        rows, errs = _run_sweep([_pr(1, [_nb(MD)])])
        assert rows == [] and errs == []

    def test_modified_notebook_is_kept(self):
        pr = _pr(1, [_nb(IPY, "MODIFIED")])
        assert _mod.ipynb_paths(pr) == [IPY]


class TestSearchCapIsNotACount:
    def test_a_batch_at_the_cap_raises(self):
        def run(argv):
            return [{} for _ in range(_mod.SEARCH_RESULT_CAP)]

        try:
            _mod.merged_prs("o/r", NOW - dt.timedelta(hours=24), run=run)
        except RuntimeError as exc:
            assert "plafond" in str(exc)
        else:
            raise AssertionError("un lot au plafond doit lever, pas passer")

    def test_a_batch_under_the_cap_passes(self):
        rows = _mod.merged_prs("o/r", NOW - dt.timedelta(hours=24),
                               run=lambda argv: [{"number": 1}])
        assert rows == [{"number": 1}]

    def test_the_window_is_asked_on_merge_time(self):
        seen = {}

        def run(argv):
            seen["argv"] = argv
            return []

        _mod.merged_prs("o/r", NOW - dt.timedelta(hours=24), run=run)
        argv = seen["argv"]
        assert "--search" in argv
        assert any(a.startswith("merged:>=") for a in argv), argv
        assert argv[argv.index("--limit") + 1] == str(_mod.SEARCH_RESULT_CAP)


class TestSweepVerdicts:
    def _one(self, lost, diff_errors, *, bases="ok"):
        pr = _pr(1, [_nb(IPY)])

        def fetch_merged(repo, since):
            return [pr]

        def fetch_body(repo, number):
            return ""

        def base_of(repo_dir, b, h):
            return "deadbeef" if bases == "ok" else None

        def check(paths, base_ref="", head_ref="", pr_body=""):
            return _FakeResult(lost=lost, diff_errors=diff_errors)

        return _mod.sweep("o/r", Path("."), 24, NOW,
                          fetch_merged=fetch_merged, fetch_body=fetch_body,
                          base_of=base_of, check=check)

    def test_a_loss_with_clean_diffs_is_labelled(self):
        rows, errs = self._one(2, 0)
        assert rows[0]["would_label"] is True
        assert errs == []

    def test_a_broken_diff_never_labels_even_with_a_loss(self):
        """#18761 : un diff casse n'est pas un zero mesure, ni un label."""
        rows, errs = self._one(3, 1)
        assert rows[0]["would_label"] is False
        assert rows[0]["credited_lost_unexempted"] == 3

    def test_zero_loss_does_not_label(self):
        rows, _ = self._one(0, 0)
        assert rows[0]["would_label"] is False

    def test_a_missing_merge_base_is_named_and_the_pr_is_still_measured(self):
        rows, errs = self._one(1, 0, bases="missing")
        assert len(errs) == 1 and "merge-base" in errs[0]
        assert rows[0]["would_label"] is True

    def test_an_unreadable_body_is_named_and_the_pr_is_skipped(self):
        pr = _pr(1, [_nb(IPY)])

        def boom(repo, number):
            raise RuntimeError("gh failed (1): not found")

        rows, errs = _mod.sweep(
            "o/r", Path("."), 24, NOW,
            fetch_merged=lambda repo, since: [pr],
            fetch_body=boom,
            base_of=lambda *a: "deadbeef",
            check=lambda *a, **k: _FakeResult(1, 0),
        )
        assert rows == []
        assert len(errs) == 1 and "body illisible" in errs[0]
