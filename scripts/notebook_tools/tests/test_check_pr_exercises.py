"""Tests for scripts/notebook_tools/check_pr_exercises.py

Issue #8814 acceptance 3 -- CONTROLE POSITIF OBLIGATOIRE: a gate that cannot
fail is green for the wrong reason (#8680, #8782). These tests prove the
advisory can actually fire (a standard notebook below 3 exercises is flagged)
and that it honours the corpus/kind exemptions of count_exercises.py rather
than re-implementing them (acceptance 4).

Pure functions on tmp_path notebooks -- no I/O on the real repo.
"""

import json
import sys
from io import StringIO
from pathlib import Path

_tools_dir = str(Path(__file__).resolve().parent.parent)
if _tools_dir not in sys.path:
    sys.path.insert(0, _tools_dir)

import check_pr_exercises as cpe  # noqa: E402


def _write_nb(path: Path, cells: list[dict]) -> Path:
    nb = {"cells": cells, "metadata": {}, "nbformat": 4, "nbformat_minor": 5}
    path.write_text(json.dumps(nb), encoding="utf-8")
    return path


def _split_source(source: str) -> list[str]:
    if not source:
        return []
    return source.splitlines(keepends=True)


def _md(source: str) -> dict:
    return {"cell_type": "markdown", "source": _split_source(source), "metadata": {}}


def _code(source: str) -> dict:
    return {
        "cell_type": "code",
        "source": _split_source(source),
        "metadata": {},
        "execution_count": None,
        "outputs": [],
    }


def _exercises(n: int) -> list[dict]:
    """A notebook with ``n`` exercise stubs (markdown header + stub code)."""
    cells: list[dict] = [_md("# Titre du cours")]
    for i in range(1, n + 1):
        cells.append(_md(f"### Exercice {i} : sujet {i}"))
        cells.append(_code("# TODO etudiant\npass"))
    return cells


# ---------------------------------------------------------------------------
# ACCEPTANCE 3 -- controle positif: the advisory CAN flag a sub-threshold nb
# ---------------------------------------------------------------------------

class TestPositiveControl:
    def test_standard_below_threshold_is_flagged(self, tmp_path):
        """A STANDARD notebook with 0 exercises must land in sub_threshold.

        This is the controle positif for issue #8814 acceptance 3: a gate
        that never fires is green for the wrong reason. The title deliberately
        avoids the word "exercice" -- the counter counts any SINGULAR exercise
        word in a header (verified firsthand by this test failing at count==1
        when the fixture said "Cours sans exercice"), so a zero-exercise
        fixture must not mention the word at all.
        """
        nb = _write_nb(tmp_path / "Course-Lesson.ipynb", [_md("# Cours de logique")])
        result = cpe.check_notebooks([nb])
        assert len(result.sub_threshold) == 1
        v = result.sub_threshold[0]
        assert v.kind == "standard"
        assert v.threshold == 3
        assert v.count == 0
        assert v.status == "sub_threshold"

    def test_standard_one_exercise_still_below_threshold(self, tmp_path):
        """1 < 3 for a standard notebook -- still flagged (not a quiet pass)."""
        nb = _write_nb(tmp_path / "Course-Lesson.ipynb", _exercises(1))
        result = cpe.check_notebooks([nb])
        assert len(result.sub_threshold) == 1
        assert result.sub_threshold[0].count == 1

    def test_standard_three_exercises_is_ok(self, tmp_path):
        """The true negative: 3 exercises meets the threshold (not flagged)."""
        nb = _write_nb(tmp_path / "Course-Lesson.ipynb", _exercises(3))
        result = cpe.check_notebooks([nb])
        assert len(result.sub_threshold) == 0
        assert len(result.ok) == 1
        assert result.ok[0].status == "ok"


# ---------------------------------------------------------------------------
# ACCEPTANCE 4 -- consume count_exercises.py classification (no re-impl)
# ---------------------------------------------------------------------------

class TestExemptionsConsumed:
    def test_setup_exempt_never_flagged(self, tmp_path):
        """A setup notebook (threshold 0) with 0 exercises is OK, not flagged.

        Proves the advisory consumes classify_notebook's exemption rather than
        applying a blanket threshold 3 (which would false-flag every setup nb).
        """
        nb = _write_nb(tmp_path / "01-Setup-Env.ipynb", [_md("# Setup seulement")])
        result = cpe.check_notebooks([nb])
        assert len(result.sub_threshold) == 0
        assert len(result.ok) == 1
        assert result.ok[0].kind == "setup"
        assert result.ok[0].threshold == 0

    def test_lean_exempt_never_flagged(self, tmp_path):
        """A Lean notebook carries its own (lenient) threshold, not 3."""
        nb = _write_nb(tmp_path / "DecInfer-9-Lean-Gittins.ipynb", [_md("# Lean cours")])
        result = cpe.check_notebooks([nb])
        assert len(result.sub_threshold) == 0
        assert result.ok[0].kind == "lean"

    def test_artifact_out_of_corpus(self, tmp_path):
        """A research/quantbook artifact is out of corpus -- never flagged."""
        nb = _write_nb(tmp_path / "research.ipynb", [_md("# pas un cours")])
        result = cpe.check_notebooks([nb])
        assert len(result.sub_threshold) == 0
        assert len(result.out_of_corpus) == 1
        assert result.out_of_corpus[0].threshold is None
        assert result.out_of_corpus[0].kind in {"artifact", "tooling"}


# ---------------------------------------------------------------------------
# ACCEPTANCE 5 -- advisory: ALWAYS exit 0 (the label is the signal, not rc)
# ---------------------------------------------------------------------------

class TestAdvisoryContract:
    def test_main_returns_zero_even_when_subthreshold(self, tmp_path, capsys):
        nb = _write_nb(tmp_path / "Course-Lesson.ipynb", [_md("# vide")])
        rc = cpe.main(["--paths", str(nb)])
        assert rc == 0
        out = capsys.readouterr().out
        assert "Below threshold" in out

    def test_main_returns_zero_when_all_ok(self, tmp_path, capsys):
        nb = _write_nb(tmp_path / "Course-Lesson.ipynb", _exercises(3))
        rc = cpe.main(["--paths", str(nb)])
        assert rc == 0
        out = capsys.readouterr().out
        assert "meet their threshold" in out

    def test_json_payload_has_label_and_summary(self, tmp_path, capsys):
        nb = _write_nb(tmp_path / "Course-Lesson.ipynb", _exercises(2))
        rc = cpe.main(["--paths", str(nb), "--json"])
        assert rc == 0
        payload = json.loads(capsys.readouterr().out)
        # Two distinct labels (#8819): below_threshold + unparseable.
        assert payload["labels"]["below_threshold"]["name"] == "exercises-below-threshold"
        assert payload["labels"]["unparseable"]["name"] == "exercises-unparseable"
        assert payload["summary"]["below_threshold"] == 1
        assert payload["summary"]["unverified"] == 0
        assert payload["summary"]["in_corpus"] == 1
        assert len(payload["sub_threshold"]) == 1
        assert payload["sub_threshold"][0]["threshold"] == 3
        assert payload["sub_threshold"][0]["count"] == 2

    def test_json_payload_zero_when_conforming(self, tmp_path, capsys):
        nb = _write_nb(tmp_path / "Course-Lesson.ipynb", _exercises(3))
        cpe.main(["--paths", str(nb), "--json"])
        payload = json.loads(capsys.readouterr().out)
        assert payload["summary"]["below_threshold"] == 0
        assert payload["summary"]["unverified"] == 0

    def test_no_paths_is_zero(self, capsys):
        rc = cpe.main([])
        assert rc == 0


# ---------------------------------------------------------------------------
# ACCEPTANCE 3 (#8819) -- controle positif: an UNREAD notebook is NOT conforming
# ---------------------------------------------------------------------------

class TestParseErrorNotConforming:
    """Issue #8819: a notebook the checker could not read must NOT pass silently.

    This is the defect the follow-up fixes: a corrupt notebook landed in
    parse_errors, summary.sub_threshold stayed 0, and the workflow claimed
    conformity over a notebook it never measured. The controle positif proves
    the gate now raises a SEPARATE label for the unverified case and refuses
    to assert "all conform".
    """

    def test_corrupt_notebook_lands_in_parse_errors_not_subthreshold(self, tmp_path):
        """A corrupt .ipynb is unverified, not conforming."""
        (tmp_path / "Course-Lesson.ipynb").write_text(
            "{ this is not valid json ", encoding="utf-8"
        )
        nb = tmp_path / "Course-Lesson.ipynb"
        result = cpe.check_notebooks([nb])
        assert len(result.parse_errors) == 1
        assert len(result.sub_threshold) == 0
        assert result.parse_errors[0].status == "parse_error"

    def test_corrupt_notebook_raises_unverified_label_count(self, tmp_path, capsys):
        """The JSON payload exposes unverified > 0 so the workflow raises a label.

        Before #8819: unverified notebooks were invisible to the label decision
        (sub_threshold=0 -> "all conform"). Now unverified is the FIRST summary
        key and its count drives the `exercises-unparseable` label.
        """
        (tmp_path / "Course-Lesson.ipynb").write_text(
            "not json at all", encoding="utf-8"
        )
        cpe.main(["--paths", str(tmp_path / "Course-Lesson.ipynb"), "--json"])
        payload = json.loads(capsys.readouterr().out)
        assert payload["summary"]["unverified"] == 1
        assert payload["summary"]["below_threshold"] == 0
        assert payload["labels"]["unparseable"]["count"] == 1

    def test_text_output_does_not_claim_conformity_when_unverified(self, tmp_path, capsys):
        """Critère 2: the closing line must NOT say 'all meet threshold' when a
        notebook is unverified -- that was the original false-claim defect."""
        (tmp_path / "Course-Lesson.ipynb").write_text(
            "broken {", encoding="utf-8"
        )
        cpe.main(["--paths", str(tmp_path / "Course-Lesson.ipynb")])
        out = capsys.readouterr().out
        assert "NOT verified" in out
        assert "meet their threshold" not in out

    def test_corrupt_notebook_still_exits_zero(self, tmp_path, capsys):
        """Advisory contract preserved: unverified raises a label, never a red job."""
        (tmp_path / "Course-Lesson.ipynb").write_text(
            "broken", encoding="utf-8"
        )
        rc = cpe.main(["--paths", str(tmp_path / "Course-Lesson.ipynb")])
        assert rc == 0

    def test_in_corpus_counts_unverified(self, tmp_path, capsys):
        """An unparseable notebook IS in the corpus (just unread), so in_corpus
        must count it -- not silently drop it from the denominator."""
        (tmp_path / "Course-Lesson.ipynb").write_text(
            "broken", encoding="utf-8"
        )
        cpe.main(["--paths", str(tmp_path / "Course-Lesson.ipynb"), "--json"])
        payload = json.loads(capsys.readouterr().out)
        assert payload["summary"]["in_corpus"] == 1

    def test_subthreshold_and_parse_error_coexist_distinctly(self, tmp_path):
        """A PR with one below-threshold notebook AND one corrupt one raises BOTH
        labels -- they are independent states, never collapsed."""
        good_below = _write_nb(tmp_path / "Course-Below.ipynb", _exercises(1))
        (tmp_path / "Course-Broken.ipynb").write_text("broken", encoding="utf-8")
        result = cpe.check_notebooks([good_below, tmp_path / "Course-Broken.ipynb"])
        assert len(result.sub_threshold) == 1
        assert len(result.parse_errors) == 1


# ---------------------------------------------------------------------------
# Path collection (stdin from `git diff --name-only`, dedup, skip deleted)
# ---------------------------------------------------------------------------

class TestPathCollection:
    def test_stdin_paths_collected(self, tmp_path, monkeypatch):
        a = _write_nb(tmp_path / "Course-A.ipynb", _exercises(0))
        b = _write_nb(tmp_path / "Course-B.ipynb", _exercises(3))
        monkeypatch.setattr(sys, "stdin", StringIO(f"{a}\n{b}\n"))
        paths = cpe._collect_paths([], from_stdin=True)
        assert {p.name for p in paths} == {"Course-A.ipynb", "Course-B.ipynb"}

    def test_dedup_paths(self, tmp_path):
        a = _write_nb(tmp_path / "Course-A.ipynb", _exercises(0))
        paths = cpe._collect_paths([str(a), str(a)], from_stdin=False)
        assert len(paths) == 1

    def test_nonexistent_path_skipped(self, tmp_path, capsys):
        paths = cpe._collect_paths(
            [str(tmp_path / "ghost.ipynb")], from_stdin=False
        )
        assert paths == []
        assert "does not exist" in capsys.readouterr().err

    def test_non_ipynb_ignored(self, tmp_path):
        f = tmp_path / "README.md"
        f.write_text("not a notebook")
        assert cpe._collect_paths([str(f)], from_stdin=False) == []
