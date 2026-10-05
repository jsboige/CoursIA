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
import json
import subprocess
import sys

import pytest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "notebook_tools"))

import check_pr_exercises as _cpe  # noqa: E402

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


def _nb(path, change="MODIFIED", previous=None):
    """Un noeud GraphQL `pullRequest.files.nodes { path changeType previousFilename }`.

    `previous` n'est pose que quand il est fourni : un noeud sans la cle simule
    la reponse degradee (renommage sous seuil de similarite) que #19251 doit
    continuer de nommer NON MESURE, pas de mesurer contre le mauvais chemin.
    """
    node = {"path": path, "changeType": change}
    if previous is not None:
        node["previousFilename"] = previous
    return node


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
        check=check or (lambda paths, base_ref="", head_ref="", pr_body="",
                        base_path_of=None: _FakeResult()),
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
        modified, added, renamed_m, renamed_u = _mod._ipynb_by_change(
            [_nb(IPY, "ADDED")])
        assert modified == [] and added == [IPY]
        assert renamed_m == [] and renamed_u == []

    def test_added_and_modified_split_in_the_same_pr(self):
        other = "MyIA.AI.Notebooks/Search/Part1/y.ipynb"
        modified, added, renamed_m, renamed_u = _mod._ipynb_by_change(
            [_nb(other, "ADDED"), _nb(IPY, "MODIFIED")])
        assert modified == [IPY] and added == [other]
        assert renamed_m == [] and renamed_u == []

    def test_a_purely_additive_pr_is_named_not_dropped(self):
        rows, errs = _sweep([_pr(1)], files={1: [_nb(IPY, "ADDED")]})
        assert len(rows) == 1 and rows[0]["notebooks"] == 0
        assert rows[0]["added_notebooks"] == 1
        assert rows[0]["would_label"] is False
        assert errs == []

    def test_a_renamed_notebook_without_previous_is_unmeasured_not_lost_free(self):
        """Un renommage sans `previousFilename` PEUT perdre des exemples : on ne
        le dit pas « sans perte ».

        `previousFilename` manque (renommage sous seuil de similarite, ou
        reponse d'API degradee) : la base est a un autre chemin inconnu, donc la
        comparaison est impossible. Le carnet ne doit ni etre mesure contre le
        mauvais chemin, ni etre tu (#19251 preserve ce repli).
        """
        modified, added, renamed_m, renamed_u = _mod._ipynb_by_change(
            [_nb(IPY, "RENAMED")])
        assert modified == [] and added == []
        assert renamed_m == [] and renamed_u == [IPY]
        rows, errs = _sweep([_pr(1)], files={1: [_nb(IPY, "RENAMED")]})
        assert len(rows) == 1 and rows[0]["renamed_notebooks"] == 1
        assert rows[0]["renamed_measured"] == 0
        assert rows[0]["notebooks"] == 0
        assert rows[0]["would_label"] is False

    def test_a_renamed_notebook_with_previous_is_measured_as_modified(self):
        """#19251 : quand `previousFilename` est connu, un renommage est mesure.

        Sa tete se lit au nouveau chemin, sa base a l'ancien -- un `git mv`
        suivi d'une edition peut perdre des exemples comme un MODIFIED.
        """
        old = "MyIA.AI.Notebooks/Search/Part1/y.ipynb"
        new = "MyIA.AI.Notebooks/Search/Part2/y.ipynb"
        modified, added, renamed_m, renamed_u = _mod._ipynb_by_change(
            [_nb(new, "RENAMED", previous=old)])
        assert modified == [] and added == []
        assert renamed_m == [(new, old)] and renamed_u == []
        rows, errs = _sweep(
            [_pr(1)], files={1: [_nb(new, "RENAMED", previous=old)]},
            check=lambda paths, base_ref="", head_ref="", pr_body="",
            base_path_of=None: _FakeResult(lost=3, diff_errors=0),
        )
        assert errs == []
        assert rows[0]["renamed_notebooks"] == 1
        assert rows[0]["renamed_measured"] == 1
        assert rows[0]["notebooks"] == 1
        assert rows[0]["credited_lost_unexempted"] == 3
        assert rows[0]["would_label"] is True

    def test_the_base_path_of_a_rename_reaches_the_check(self):
        """Le contrat de la carte : `base_path_of` porte la correspondance
        nouveau chemin -> ancien chemin, pour le cote base du diff credite."""
        old = "MyIA.AI.Notebooks/Search/Part1/y.ipynb"
        new = "MyIA.AI.Notebooks/Search/Part2/y.ipynb"
        seen = {}

        def check(paths, base_ref="", head_ref="", pr_body="", base_path_of=None):
            seen["paths"] = [str(p) for p in paths]
            seen["map"] = dict(base_path_of or {})
            return _FakeResult()

        _sweep(
            [_pr(1)], files={1: [_nb(new, "RENAMED", previous=old)]},
            check=check,
        )
        assert seen["paths"] == [str(Path(new))]
        # la carte est clee en POSIX (le chemin tel que rendu par GraphQL), pas
        # dans la forme native du systeme : c'est ce que `check_notebooks`
        # normalise avant de la consulter (cf. le test de lookup ci-dessous).
        assert seen["map"] == {new: old}

    def test_a_renamed_notebook_does_not_block_the_other_notebooks(self):
        """Le faux positif d'erreur produisait un faux zero de pertes (#18761).

        Un carnet renomme SANS chemin de base dans la meme PR ne doit pas
        empecher la mesure des carnets modifies -- c'est le defaut que la
        separation corrige.
        """
        other = "MyIA.AI.Notebooks/Search/Part1/y.ipynb"
        seen = []

        def check(paths, base_ref="", head_ref="", pr_body="", base_path_of=None):
            seen.append([str(p) for p in paths])
            return _FakeResult(lost=2, diff_errors=0)

        rows, errs = _sweep(
            [_pr(1)],
            files={1: [_nb(other, "RENAMED"), _nb(IPY, "MODIFIED")]},
            check=check,
        )
        assert rows[0]["would_label"] is True, rows
        assert rows[0]["renamed_notebooks"] == 1
        assert rows[0]["renamed_measured"] == 0
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

        def check(paths, base_ref="", head_ref="", pr_body="", base_path_of=None):
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


class TestARenamedNotebookNoLongerTakesDownTheSweep:
    """Review #19215 (5411248369), la mesure qui a fait tomber `--hours 72`.

    #18788 a MODIFIE ICT-45-InoculationBifurcation-9B ; #19153 l'a ensuite
    RENOMME en ICT-42b. Pour #18788 le chemin est donc MODIFIED, mais il
    n'existe plus dans l'arbre du jour : `check_notebooks` comptait les
    exercices sur cet arbre et levait un FileNotFoundError, ce qui emportait
    TOUT le balayage -- les autres PR de la fenetre n'etaient pas mesurees.
    """

    def test_a_failing_check_names_the_pr_and_the_others_are_still_measured(self):
        def check(paths, base_ref="", head_ref="", pr_body="", base_path_of=None):
            if paths and "ICT-45" in str(paths[0]):
                raise FileNotFoundError(
                    "MyIA.AI.Notebooks/IIT/ICT-Series/ICT-45-...ipynb")
            return _FakeResult()

        rows, errs = _sweep(
            [_pr(18788), _pr(18789)],
            files={18788: [_nb("MyIA.AI.Notebooks/IIT/ICT-Series/ICT-45-x.ipynb")],
                   18789: [_nb(IPY)]},
            check=check,
        )
        assert [r["number"] for r in rows] == [18789], \
            "un carnet illisible ne doit pas emporter les autres PR"
        assert len(errs) == 1
        assert errs[0].startswith("#18788:")
        assert "carnet illisible" in errs[0]
        assert "renomme ou supprime apres merge" in errs[0]
        assert "FileNotFoundError" in errs[0], \
            "le nom de l'exception doit rester lisible dans le repli"

    def test_only_a_missing_notebook_is_named_other_errors_still_propagate(self):
        """La portee du `except` est etroite : un bug du compteur ne doit pas
        se derober en « carnet renomme ». Un repli trop large remplacerait une
        panne par un chiffre manquant, ce que la fenetre ne distinguerait pas
        d'une PR sans perte."""
        def check(paths, base_ref="", head_ref="", pr_body="", base_path_of=None):
            raise RuntimeError("bug du compteur")

        with pytest.raises(RuntimeError):
            _sweep([_pr(7)], files={7: [_nb(IPY)]}, check=check)


def _notebook_json(n_exercises):
    """Un carnet minimal : N paires (en-tete `### Exercice i` + stub TODO)."""
    cells = []
    for i in range(1, n_exercises + 1):
        cells.append({"cell_type": "markdown", "metadata": {},
                      "source": [f"### Exercice {i}\n", "A completer.\n"]})
        cells.append({"cell_type": "code", "metadata": {}, "execution_count": None,
                      "outputs": [], "source": ["# TODO etudiant\n",
                                                "result = None\n"]})
    return {"cells": cells, "metadata": {}, "nbformat": 4, "nbformat_minor": 5}


def _git(repo, *args):
    subprocess.run(
        ["git", "-C", str(repo), "-c", "user.name=t", "-c", "user.email=t@t",
         "-c", "core.autocrlf=false", *args],
        check=True, capture_output=True, text=True, encoding="utf-8",
        errors="replace",
    )


class TestTheCountReadsTheRevisionNotTheTree:
    """Review #19215 : `check_notebooks` comptait les exercices sur l'ARBRE DU
    JOUR (`count_exercises_in_notebook(path)`), alors que le diff credite lit
    deja le blob de `head_ref`. Deux consequences, une panne et un chiffre
    faux -- les deux sont epinglees ici sur un depot git reel."""

    REL = "MyIA.AI.Notebooks/Search/Part1/x.ipynb"

    def _repo_with_head(self, tmp_path, *, tree):
        """Depot a deux commits ; la tete porte 3 exercices.

        ``tree`` : ce que l'arbre de travail contient a la fin -- ``None``
        (carnet renomme/supprime depuis), ou un carnet d'un autre nombre
        d'exercices (l'arbre a bouge depuis le merge)."""
        repo = tmp_path / "repo"
        (repo / Path(self.REL).parent).mkdir(parents=True)
        target = repo / self.REL
        _git(repo, "init", "-q")
        target.write_text(json.dumps(_notebook_json(1)), encoding="utf-8")
        _git(repo, "add", "-A")
        _git(repo, "commit", "-q", "-m", "base")
        base = subprocess.run(["git", "-C", str(repo), "rev-parse", "HEAD"],
                              capture_output=True, text=True, check=True,
                              encoding="utf-8", errors="replace").stdout.strip()
        target.write_text(json.dumps(_notebook_json(3)), encoding="utf-8")
        _git(repo, "add", "-A")
        _git(repo, "commit", "-q", "-m", "head")
        head = subprocess.run(["git", "-C", str(repo), "rev-parse", "HEAD"],
                              capture_output=True, text=True, check=True,
                              encoding="utf-8", errors="replace").stdout.strip()
        if tree is None:
            target.unlink()
        else:
            target.write_text(json.dumps(_notebook_json(tree)), encoding="utf-8")
        return repo, base, head

    def _count(self, result):
        """Le compte du carnet mesure, quel que soit son seau."""
        for bucket in (result.ok, result.sub_threshold, result.parse_errors,
                       result.out_of_corpus):
            for verdict in bucket:
                if verdict.path.endswith("x.ipynb"):
                    return verdict.count
        raise AssertionError("le carnet n'apparait dans aucun seau du resultat")

    def test_a_modified_notebook_absent_from_the_tree_is_counted_from_the_blob(
            self, tmp_path, monkeypatch):
        """Le cas #18788 puis #19153 : ICT-45 modifie, puis renomme."""
        repo, base, head = self._repo_with_head(tmp_path, tree=None)
        monkeypatch.chdir(repo)
        result = _cpe.check_notebooks([Path(self.REL)], base_ref=base, head_ref=head)
        assert self._count(result) == 3, \
            "le compte doit venir du blob de tete, pas de l'arbre (absent)"

    def test_the_tree_version_never_wins_over_the_pr_head(self, tmp_path, monkeypatch):
        """Meme quand le chemin existe, c'est la revision de la PR qui compte."""
        repo, base, head = self._repo_with_head(tmp_path, tree=1)
        monkeypatch.chdir(repo)
        result = _cpe.check_notebooks([Path(self.REL)], base_ref=base, head_ref=head)
        assert self._count(result) == 3, \
            "1 exercice dans l'arbre, 3 dans la tete : la tete est la mesure"

    def test_without_a_head_ref_the_tree_still_serves(self, tmp_path, monkeypatch):
        """Retro-compatibilite : l'appel sans tete (CLI locale) lit l'arbre."""
        repo, _base, _head = self._repo_with_head(tmp_path, tree=2)
        monkeypatch.chdir(repo)
        result = _cpe.check_notebooks([Path(self.REL)])
        assert self._count(result) == 2


def _credited_notebook_json(n, *, tag):
    """Un carnet a ``n`` exemples credits, chacun d'identite distincte.

    L'identite d'un exemple credite est ``(credit, cell_id)`` : un exemple
    conserve au renommage garde le MEME ``cell_id`` des deux cotes, sinon il
    se lirait comme perdu puis reajoute. ``tag`` sert a distinguer des carnets
    differents d'un meme test, pas la base de la tete.
    """
    cells = []
    for i in range(1, n + 1):
        cells.append({
            "cell_type": "markdown", "id": f"{tag}-ex{i}", "metadata": {},
            "source": [f"### Exemple {i}\n", f"[crédité #{1000 + i}]\n"],
        })
        cells.append({
            "cell_type": "code", "id": f"{tag}-c{i}", "metadata": {},
            "execution_count": 1, "outputs": [], "source": [f"print({i})\n"],
        })
    return {"cells": cells, "metadata": {}, "nbformat": 4, "nbformat_minor": 5}


class TestARenamedNotebookIsMeasuredAtItsOldPath:
    """#19251 : un RENAMED dont `previousFilename` est connu est MESURE.

    Le renommage est le cas aveugle qui a motive #19251 : la base est a un
    autre chemin, donc `base:path` ne trouve rien. Sans la correspondance, la
    mesure tombe -- et une mesure tombee se lirait soit comme zero perte (si
    on avalait l'erreur), soit comme un diff en erreur (honnete mais inutile).
    Ici on epingle la VRAIE mesure : le carnet renomme qui perd un exemple
    credite est vu, sur un depot git reel.
    """

    OLD = "MyIA.AI.Notebooks/Search/Part1/moved.ipynb"
    NEW = "MyIA.AI.Notebooks/Search/Part2/moved.ipynb"

    def _repo_with_rename(self, tmp_path, *, keep=2):
        """Commit base : 3 exemples credites a OLD. Commit tete : `git mv` vers
        NEW, ``keep`` exemples conserves (identites stables) -- ``keep=2`` perd
        le 3e, ``keep=3`` ne perd rien."""
        repo = tmp_path / "repo"
        (repo / Path(self.OLD).parent).mkdir(parents=True)
        _git(repo, "init", "-q")
        (repo / self.OLD).write_text(
            json.dumps(_credited_notebook_json(3, tag="ex")), encoding="utf-8")
        _git(repo, "add", "-A")
        _git(repo, "commit", "-q", "-m", "base")
        base = subprocess.run(["git", "-C", str(repo), "rev-parse", "HEAD"],
                              capture_output=True, text=True, check=True,
                              encoding="utf-8", errors="replace").stdout.strip()
        (repo / Path(self.NEW).parent).mkdir(parents=True)
        _git(repo, "mv", self.OLD, self.NEW)
        (repo / self.NEW).write_text(
            json.dumps(_credited_notebook_json(keep, tag="ex")), encoding="utf-8")
        _git(repo, "add", "-A")
        _git(repo, "commit", "-q", "-m", "head")
        head = subprocess.run(["git", "-C", str(repo), "rev-parse", "HEAD"],
                              capture_output=True, text=True, check=True,
                              encoding="utf-8", errors="replace").stdout.strip()
        return repo, base, head

    def _verdict(self, result, name):
        for bucket in (result.ok, result.sub_threshold, result.parse_errors):
            for v in bucket:
                if v.path.endswith(name):
                    return v
        raise AssertionError("le carnet n'apparait dans aucun seau")

    def test_the_loss_of_a_renamed_notebook_is_measured(self, tmp_path, monkeypatch):
        repo, base, head = self._repo_with_rename(tmp_path)
        monkeypatch.chdir(repo)
        result = _cpe.check_notebooks(
            [Path(self.NEW)], base_ref=base, head_ref=head,
            base_path_of={self.NEW: self.OLD},
        )
        verdict = self._verdict(result, "moved.ipynb")
        assert verdict.credited_diff_status == "ok", \
            "avec previousFilename, le diff doit etre calcule, pas en erreur"
        assert verdict.credited_lost_unexempted == 1, \
            "l'exemple credite perdu au renommage doit etre vu"

    def test_a_rename_without_loss_is_not_a_false_positive(
            self, tmp_path, monkeypatch):
        """Un renommage qui ne perd rien ne doit pas etre signale.

        Sans ce controle, la mesure du renommage pourrait crier a la perte sur
        un simple `git mv` -- le faux positif que #19251 doit eviter autant que
        l'angle mort qu'il ferme.
        """
        repo, base, head = self._repo_with_rename(tmp_path, keep=3)
        monkeypatch.chdir(repo)
        result = _cpe.check_notebooks(
            [Path(self.NEW)], base_ref=base, head_ref=head,
            base_path_of={self.NEW: self.OLD},
        )
        verdict = self._verdict(result, "moved.ipynb")
        assert verdict.credited_diff_status == "ok"
        assert verdict.credited_lost_unexempted == 0, \
            "aucun exemple perdu au renommage : rien a signaler"

    def test_without_the_mapping_the_rename_is_not_silently_a_zero(
            self, tmp_path, monkeypatch):
        """Sans `previousFilename`, on ne MESURE pas -- et surtout on ne rend
        pas « zero perte » : le diff reste en erreur, que #18761 refuse de
        convertir en label. Un zero silencieux serait le vrai mensonge."""
        repo, base, head = self._repo_with_rename(tmp_path)
        monkeypatch.chdir(repo)
        result = _cpe.check_notebooks(
            [Path(self.NEW)], base_ref=base, head_ref=head)
        verdict = self._verdict(result, "moved.ipynb")
        assert verdict.credited_diff_status.startswith("error:"), \
            "base absente a ce chemin : le diff doit etre en erreur, pas a zero"
        assert verdict.credited_lost_unexempted == 0
