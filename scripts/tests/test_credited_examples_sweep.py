#!/usr/bin/env python3
"""Tests for `scripts/notebook_tools/credited_examples_sweep.py` (#19101).

Le balayage est concu pour etre injectable : `sweep()` prend ses appels
reseau et git en parametres, donc tout se teste hors ligne. Les controles
epinglent les pieges qui rendraient le balayage trompeur, dont les trois
mesures de la review #19215 :

  - la forme REELLE de `gh pr list --json` ne porte NI `files` NI
    `changeType` (mesure gh 2.83.2) : la nature des fichiers vient de
    `pr_files`, par GraphQL pagine -- jamais du lot ;
  - un carnet supprime (#19040 a supprime GameTheory-18d) est ecarte sans
    planter, et n'empeche pas la mesure des carnets modifies de la PR ;
  - le cote « apres » est la tete de la PR (`headRefOid`), pas l'arbre du
    moment ; un commit de tete inatteignable est NOMME, la PR ecartee ;
  - un lot qui ATTEINT le plafond de l'API de recherche n'est pas un compte ;
  - le label ne se pose que si TOUS les diffs ont reussi (#18761) ;
  - un merge-base indisponible est NOMME, jamais un diff silencieux contre
    la mauvaise base.
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

IPY = "MyIA.AI.Notebooks/Search/Part1/x.ipynb"
MD = "MyIA.AI.Notebooks/Search/Part1/README.md"


class _FakeResult:
    def __init__(self, lost=0, diff_errors=0):
        self._s = {
            "credited_lost_unexempted": lost,
            "credited_diff_errors": diff_errors,
        }

    def as_payload(self):
        return {"summary": self._s}


class _Proc:
    def __init__(self, rc):
        self.returncode = rc


def _pr(number, base="a" * 40, head="b" * 40):
    """La forme EXACTE rendue par `gh pr list --json number,baseRefOid,headRefOid,mergedAt` :
    pas de cle `files` -- les fichiers (et leur `changeType`) viennent de
    `pr_files`, en GraphQL. C'est l'ecart que masquaient les tests d'avant,
    qui injectaient des lots deja classes."""
    return {
        "number": number,
        "baseRefOid": base,
        "headRefOid": head,
        "mergedAt": NOW.isoformat(),
    }


def _nb(path, change="MODIFIED"):
    """Un noeud GraphQL `pullRequest.files.nodes { path changeType }`."""
    return {"path": path, "changeType": change}


def _files_of(mapping):
    def fetch_files(repo, number):
        return mapping[number]
    return fetch_files


def _sweep(prs, *, files=None, body=None, base_of=None, ensure=None, check=None):
    """Drive `sweep` with the network and git fully injected (offline)."""
    if files is None:
        files = {}
    fetch_files = _files_of(files) if isinstance(files, dict) else files
    return _mod.sweep(
        "o/r", Path("."), 24, NOW,
        fetch_merged=lambda repo, since: prs,
        fetch_files=fetch_files,
        fetch_body=body or (lambda repo, number: ""),
        base_of=base_of or (lambda repo_dir, b, h: "deadbeef"),
        ensure=ensure or (lambda repo_dir, sha: True),
        check=check or (lambda paths, base_ref="", head_ref="", pr_body="":
                        _FakeResult()),
    )


class TestGhFormIsNotTheFilesSource:
    """Review #19215, point 1 : `gh pr list --json files` ne rend pas
    `changeType` -- tout le classement ADDED/DELETED/RENAMED etait mort en
    production (repli « tout MODIFIED »), et les tests d'avant l'ignoraient
    en injectant des dicts deja classes."""

    def test_the_real_gh_pr_list_form_has_no_files_and_still_measures(self):
        pr = _pr(1)
        assert "files" not in pr, "la forme reelle de gh pr list ne porte pas files"
        rows, errs = _sweep([pr], files={1: [_nb(IPY)]})
        assert len(rows) == 1 and rows[0]["notebooks"] == 1 and errs == []

    def test_merged_prs_asks_exactly_the_four_fields(self):
        seen = {}

        def run(argv):
            seen["argv"] = argv
            return []

        _mod.merged_prs("o/r", NOW - dt.timedelta(hours=24), run=run)
        argv = seen["argv"]
        assert argv[argv.index("--json") + 1] == "number,baseRefOid,headRefOid,mergedAt"
        assert "files" not in argv[argv.index("--json") + 1]

    def test_an_unreadable_files_query_names_the_pr_and_continues(self):
        def fetch_files(repo, number):
            if number == 1:
                raise RuntimeError("gh failed (1): graphql timeout")
            return [_nb(IPY)]

        rows, errs = _sweep([_pr(1), _pr(2)], files=fetch_files)
        assert [r["number"] for r in rows] == [2]
        assert len(errs) == 1 and "fichiers illisibles" in errs[0]

    def test_pages_are_followed_to_the_cursor(self):
        """Une PR de carnet peut deplacer plus de 100 fichiers : la requete
        GraphQL pagine au curseur, et le lot est la concatenation des pages."""
        pages = [
            {"data": {"repository": {"pullRequest": {"files": {
                "nodes": [{"path": f"n{i}.ipynb", "changeType": "MODIFIED"}
                          for i in range(100)],
                "pageInfo": {"hasNextPage": True, "endCursor": "CUR1"}}}}}},
            {"data": {"repository": {"pullRequest": {"files": {
                "nodes": [{"path": "last.ipynb", "changeType": "DELETED"}],
                "pageInfo": {"hasNextPage": False}}}}}},
        ]
        calls = []

        def run(argv):
            calls.append(argv)
            return pages[len(calls) - 1]

        nodes = _mod.pr_files("o/r", 7, run=run)
        assert len(nodes) == 101
        assert nodes[-1]["changeType"] == "DELETED"
        assert "cursor=CUR1" in calls[1], f"le curseur de la 1re page doit servir : {calls[1]}"
        assert "cursor=CUR1" not in calls[0]


class TestFiltering:
    def test_only_ipynb_paths_are_kept(self):
        assert _mod.ipynb_paths([_nb(IPY), _nb(MD)]) == [IPY]

    def test_deleted_notebooks_are_excluded(self):
        """Un carnet supprime n'a plus rien a compter (--diff-filter=d)."""
        assert _mod.ipynb_paths([_nb(IPY, "DELETED")]) == []

    def test_a_deleted_notebook_no_longer_crashes_the_sweep(self):
        """Regression #19215 (cause 1 de la review) : GameTheory-18d,
        supprime par #19040, etait classe MODIFIED (changeType absent du lot)
        puis ouvert -> FileNotFoundError, hors de tout garde. Avec la source
        GraphQL il est ecarte ET les carnets modifies de la meme PR restent
        mesures."""
        gone = "MyIA.AI.Notebooks/GameTheory/GameTheory-18d-Humour-Banc-Dur-Python.ipynb"
        rows, errs = _sweep(
            [_pr(19040)],
            files={19040: [_nb(gone, "DELETED"), _nb(IPY, "MODIFIED")]},
        )
        assert errs == []
        assert rows[0]["notebooks"] == 1 and rows[0]["paths"] == [IPY]

    def test_added_notebooks_are_not_measured(self):
        """Un carnet neuf n'existe pas dans la base : `git show` sort en 128.

        Ce n'est PAS une erreur de mesure (#18761) -- et la compter comme telle
        bloquait le label pour les carnets MODIFIES de la meme PR.
        """
        modified, added, renamed = _mod._ipynb_by_change([_nb(IPY, "ADDED")])
        assert modified == [] and added == [IPY] and renamed == []

    def test_added_and_modified_split_in_the_same_pr(self):
        other = "MyIA.AI.Notebooks/Search/Part1/y.ipynb"
        modified, added, renamed = _mod._ipynb_by_change(
            [_nb(other, "ADDED"), _nb(IPY, "MODIFIED")])
        assert modified == [IPY] and added == [other] and renamed == []

    def test_a_purely_additive_pr_is_named_not_dropped(self):
        rows, errs = _sweep([_pr(1)], files={1: [_nb(IPY, "ADDED")]})
        assert len(rows) == 1 and rows[0]["notebooks"] == 0
        assert rows[0]["added_notebooks"] == 1
        assert rows[0]["would_label"] is False
        assert errs == []

    def test_a_renamed_notebook_is_declared_unmeasured_not_lost_free(self):
        """Un renommage PEUT perdre des exemples : on ne le dit pas « sans perte ».

        La base est a un autre chemin (`previousFilename` hors du jeu GraphQL
        demande ici), donc la comparaison est impossible. Le carnet ne doit ni
        etre mesure contre le mauvais chemin, ni etre tu.
        """
        modified, added, renamed = _mod._ipynb_by_change([_nb(IPY, "RENAMED")])
        assert modified == [] and added == [] and renamed == [IPY]
        rows, errs = _sweep([_pr(1)], files={1: [_nb(IPY, "RENAMED")]})
        assert len(rows) == 1 and rows[0]["renamed_notebooks"] == 1
        assert rows[0]["notebooks"] == 0
        assert rows[0]["would_label"] is False

    def test_a_renamed_notebook_does_not_block_the_other_notebooks(self):
        """Le faux positif d'erreur produisait un faux zero de pertes (#18761).

        Un carnet renomme dans la meme PR ne doit plus empecher la mesure des
        carnets modifies -- c'est le defaut que la separation corrige.
        """
        other = "MyIA.AI.Notebooks/Search/Part1/y.ipynb"
        seen = []

        def check(paths, base_ref="", head_ref="", pr_body=""):
            seen.append([str(p) for p in paths])
            return _FakeResult(lost=2, diff_errors=0)

        rows, errs = _sweep(
            [_pr(1)],
            files={1: [_nb(other, "RENAMED"), _nb(IPY, "MODIFIED")]},
            check=check,
        )
        assert rows[0]["would_label"] is True, rows
        assert rows[0]["renamed_notebooks"] == 1
        assert seen == [[str(Path(IPY))]]
        assert errs == []

    def test_a_pr_without_notebook_is_skipped_by_the_sweep(self):
        rows, errs = _sweep([_pr(1)], files={1: [_nb(MD)]})
        assert rows == [] and errs == []

    def test_modified_notebook_is_kept(self):
        assert _mod.ipynb_paths([_nb(IPY, "MODIFIED")]) == [IPY]


class TestHeadIsThePrHead:
    """Review #19215, point 2 : le cote « apres » est la tete de la PR, pas
    l'arbre de travail du moment du balayage."""

    def test_the_check_receives_the_head_of_the_pr(self):
        captured = {}

        def check(paths, base_ref="", head_ref="", pr_body=""):
            captured["base_ref"] = base_ref
            captured["head_ref"] = head_ref
            return _FakeResult(1, 0)

        _sweep([_pr(1, base="a" * 40, head="c" * 40)],
               files={1: [_nb(IPY)]}, check=check)
        # cote « apres » : la TETE de la PR, pas l'arbre du moment
        assert captured["head_ref"] == "c" * 40
        # cote « avant » : le merge-base rendu par base_of, pas la base brute
        assert captured["base_ref"] == "deadbeef"

    def test_a_local_commit_short_circuits_without_fetch(self):
        calls = []

        def run(argv):
            calls.append(argv)
            return _Proc(0)

        assert _mod.ensure_commit(Path("."), "b" * 40, run=run) is True
        assert len(calls) == 1, "le probe suffit, pas de fetch"
        assert "cat-file" in calls[0]

    def test_a_missing_commit_is_fetched_then_reconfirmed(self):
        seq = [_Proc(1), _Proc(0), _Proc(0)]  # probe manque, fetch, probe ok

        def run(argv):
            return seq.pop(0)

        assert _mod.ensure_commit(Path("."), "b" * 40, run=run) is True
        assert not seq

    def test_a_still_missing_commit_returns_false(self):
        seq = [_Proc(1), _Proc(0), _Proc(1)]  # meme apres fetch, introuvable

        def run(argv):
            return seq.pop(0)

        assert _mod.ensure_commit(Path("."), "b" * 40, run=run) is False
        assert not seq

    def test_an_unreachable_head_names_the_pr_and_skips_the_measurement(self):
        """Une PR squash-mergee dont le headRefOid a disparu n'est JAMAIS
        mesuree contre l'arbre du jour -- elle est ecartee, en erreur nommee."""
        seen = []

        def check(*a, **k):
            seen.append(a)
            return _FakeResult(9, 0)

        rows, errs = _sweep([_pr(1)], files={1: [_nb(IPY)]},
                            ensure=lambda repo_dir, sha: False, check=check)
        assert rows == [] and seen == []
        assert len(errs) == 1 and "inatteignable" in errs[0]

    def test_a_missing_merge_base_is_named_and_the_pr_is_still_measured(self):
        rows, errs = _sweep([_pr(1)], files={1: [_nb(IPY)]},
                            base_of=lambda repo_dir, b, h: None,
                            check=lambda *a, **k: _FakeResult(1, 0))
        assert len(errs) == 1 and "merge-base" in errs[0]
        assert rows[0]["would_label"] is True


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
    def _one(self, lost, diff_errors):
        return _sweep(
            [_pr(1)], files={1: [_nb(IPY)]},
            check=lambda *a, **k: _FakeResult(lost, diff_errors),
        )

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

    def test_an_unreadable_body_is_named_and_the_pr_is_skipped(self):
        def boom(repo, number):
            raise RuntimeError("gh failed (1): not found")

        rows, errs = _sweep([_pr(1)], files={1: [_nb(IPY)]}, body=boom)
        assert rows == []
        assert len(errs) == 1 and "body illisible" in errs[0]
