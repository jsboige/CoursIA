"""Tests pytest pour scan_d1_d3_d4_d5.py (Phase 1 EPIC #9768).

Cible 33+ tests sur les axes :
- Signature numerique (changed_from, from_numbers)
- Extraction de nombres depuis outputs Jupyter (formats varies)
- Extraction de nombres depuis prose markdown (filtres D1_PROSE_MIN/MAX)
- Classification commits (non-substantiel / restore / rename)
- Detecteurs individuels (D1, D3, D4, D5)
- Orchestration forensic_scan
- CLI --check (exit codes)

Reference : scripts/notebook_tools/scan_d1_d3_d4_d5.py
"""

from __future__ import annotations

import io
import json
import sys
from pathlib import Path

import pytest

# Permettre l'import du module parent.
_HERE = Path(__file__).resolve().parent
_TOOLS = _HERE.parent
if str(_TOOLS) not in sys.path:
    sys.path.insert(0, str(_TOOLS))

from scan_d1_d3_d4_d5 import (  # noqa: E402
    NotebookRevision,
    NotebookForensic,
    NumericSignature,
    ForensicFinding,
    NON_SUBSTANTIAL_PREFIXES,
    RESTORE_VERBS,
    RENAME_VERBS,
    D1_PROSE_MIN,
    D1_PROSE_MAX,
    D1_PROXIMITY_REL,
    RELATIVE_JUMP_THRESHOLD,
    SIGNATURE_CHANGE_THRESHOLD,
    MIN_NUMBER_VALUE,
    MAX_NUMBER_VALUE,
    _is_non_substantial,
    _has_restore_verb,
    _has_rename_verb,
    _extract_numbers_from_text,
    extract_output_numbers,
    extract_prose_numbers,
    detect_d1,
    detect_d3,
    detect_d4,
    detect_d5,
    forensic_scan,
    render_text,
    main,
)


# ============================================================================ #
#  NumericSignature
# ============================================================================ #


class TestNumericSignature:
    """Tests sur la signature numerique (mecanisme central D3/D4/D5)."""

    def test_from_empty(self):
        sig = NumericSignature.from_numbers([])
        assert sig.median == 0.0
        assert sig.std == 0.0
        assert sig.count == 0

    def test_from_single(self):
        sig = NumericSignature.from_numbers([42.0])
        assert sig.median == 42.0
        assert sig.std == 0.0  # std=0 sur 1 valeur (cas documente)
        assert sig.count == 1

    def test_from_many_median(self):
        # [1,2,3,4,5] -> median = 3 (index 2 sur 5 elements, sorted)
        sig = NumericSignature.from_numbers([1, 2, 3, 4, 5])
        assert sig.median == 3.0
        assert sig.count == 5
        assert sig.std > 0

    def test_from_many_even_count(self):
        # [1,2,3,4] -> median = 3 (index 2 sur 4 elements)
        sig = NumericSignature.from_numbers([1, 2, 3, 4])
        assert sig.median == 3.0
        assert sig.count == 4

    def test_changed_from_above_threshold(self):
        # Mediane bouge de 50%, au-dessus de SIGNATURE_CHANGE_THRESHOLD (5%).
        prev = NumericSignature(median=1.0, std=0.5, count=10)
        cur = NumericSignature(median=1.5, std=0.5, count=10)
        assert cur.changed_from(prev) is True

    def test_changed_from_below_threshold(self):
        # Mediane bouge de 1%, sous le seuil.
        prev = NumericSignature(median=1.0, std=0.5, count=10)
        cur = NumericSignature(median=1.01, std=0.5, count=10)
        assert cur.changed_from(prev) is False

    def test_changed_from_zero_to_nonzero(self):
        prev = NumericSignature(median=0.0, std=0.0, count=5)
        cur = NumericSignature(median=0.5, std=0.0, count=5)
        assert cur.changed_from(prev) is True

    def test_changed_from_empty_signature(self):
        # Si l'une des signatures est vide, pas de saut.
        prev = NumericSignature()
        cur = NumericSignature(median=1.0, count=5)
        assert cur.changed_from(prev) is False

    def test_changed_from_std_only(self):
        # Mediane stable, std qui bouge.
        prev = NumericSignature(median=1.0, std=0.1, count=10)
        cur = NumericSignature(median=1.0, std=0.5, count=10)
        assert cur.changed_from(prev) is True


# ============================================================================ #
#  Extraction de nombres depuis texte brut
# ============================================================================ #


class TestExtractNumbersFromText:
    """Tests sur l'extraction de nombres depuis du texte brut."""

    def test_simple_numbers(self):
        nums = _extract_numbers_from_text("Result: 3.14 and 42")
        assert 3.14 in nums
        assert 42 in nums

    def test_negative_numbers(self):
        nums = _extract_numbers_from_text("delta = -1.5e-3")
        assert -1.5e-3 in nums or any(abs(n + 1.5e-3) < 1e-9 for n in nums)

    def test_scientific_notation(self):
        # 6.626e-34 est sous MIN_NUMBER_VALUE (1e-6), donc il EST filtre.
        # C'est la garde anti-bruit : on ne veut pas polluer la signature avec
        # des constantes physiques.
        nums = _extract_numbers_from_text("phi = 6.626e-34")
        assert not any(n > 0 for n in nums)

    def test_scientific_notation_in_range(self):
        # En revanche, un nombre en notation scientifique dans la plage
        # [MIN_NUMBER_VALUE, MAX_NUMBER_VALUE] survit.
        nums = _extract_numbers_from_text("x = 1.5e-3")
        assert any(abs(n - 1.5e-3) < 1e-9 for n in nums)

    def test_filters_trivial_numbers(self):
        # Les nombres sous MIN_NUMBER_VALUE sont filtres.
        nums = _extract_numbers_from_text("epsilon 1e-9 should be filtered")
        # 1e-9 est inferieur a 1e-6, donc filtre
        assert not any(abs(n) < MIN_NUMBER_VALUE for n in nums)

    def test_filters_huge_numbers(self):
        # Les nombres au-dessus de MAX_NUMBER_VALUE sont filtres.
        nums = _extract_numbers_from_text("timestamp 999999999999 should be filtered")
        assert not any(n > MAX_NUMBER_VALUE for n in nums)

    def test_empty_text(self):
        nums = _extract_numbers_from_text("")
        assert nums == []

    def test_no_numbers(self):
        nums = _extract_numbers_from_text("aucun nombre ici")
        assert nums == []

    def test_multiple_occurrences(self):
        nums = _extract_numbers_from_text("a=1, b=1, c=1")
        assert len(nums) == 3


# ============================================================================ #
#  Extraction de nombres depuis outputs Jupyter
# ============================================================================ #


class TestExtractOutputNumbers:
    """Tests sur extract_output_numbers (formats Jupyter varies)."""

    def test_empty_notebook(self):
        nb_json = json.dumps({"cells": []})
        cells_count, nums = extract_output_numbers(nb_json)
        assert cells_count == 0
        assert nums == []

    def test_invalid_json(self):
        cells_count, nums = extract_output_numbers("not json at all")
        assert cells_count == 0
        assert nums == []

    def test_text_output(self):
        nb = {
            "cells": [
                {
                    "cell_type": "code",
                    "outputs": [{"output_type": "stream", "text": "Result: 42.5"}],
                }
            ]
        }
        cells_count, nums = extract_output_numbers(json.dumps(nb))
        assert cells_count == 1
        assert 42.5 in nums

    def test_data_text_plain_string(self):
        nb = {
            "cells": [
                {
                    "cell_type": "code",
                    "outputs": [{"data": {"text/plain": "0.42"}}],
                }
            ]
        }
        cells_count, nums = extract_output_numbers(json.dumps(nb))
        assert 0.42 in nums

    def test_data_text_plain_list(self):
        nb = {
            "cells": [
                {
                    "cell_type": "code",
                    "outputs": [{"data": {"text/plain": ["0.42", "0.43"]}}],
                }
            ]
        }
        cells_count, nums = extract_output_numbers(json.dumps(nb))
        assert 0.42 in nums
        assert 0.43 in nums

    def test_error_output_skipped(self):
        nb = {
            "cells": [
                {
                    "cell_type": "code",
                    "outputs": [{"output_type": "error", "ename": "ValueError", "evalue": "0.42"}],
                }
            ]
        }
        cells_count, nums = extract_output_numbers(json.dumps(nb))
        assert cells_count == 1
        # 0.42 dans le message d'erreur : on ignore les erreurs.
        assert 0.42 not in nums

    def test_mixed_outputs(self):
        nb = {
            "cells": [
                {
                    "cell_type": "code",
                    "outputs": [
                        {"text": "a=1"},
                        {"data": {"text/plain": "b=2"}},
                        {"output_type": "error", "evalue": "c=3"},
                    ],
                }
            ]
        }
        cells_count, nums = extract_output_numbers(json.dumps(nb))
        assert 1 in nums
        assert 2 in nums
        assert 3 not in nums  # erreur exclue

    def test_markdown_cells_excluded(self):
        nb = {
            "cells": [
                {"cell_type": "markdown", "source": ["# Title 42"]},
                {"cell_type": "code", "outputs": [{"text": "result 100"}]},
            ]
        }
        cells_count, nums = extract_output_numbers(json.dumps(nb))
        assert cells_count == 1  # seule la code cell compte
        assert 42 not in nums  # markdown exclu
        assert 100 in nums


# ============================================================================ #
#  Extraction de nombres depuis prose markdown (filtres D1)
# ============================================================================ #


class TestExtractProseNumbers:
    """Tests sur extract_prose_numbers (filtres D1_PROSE_MIN/MAX)."""

    def test_filters_below_min(self):
        nb = {"cells": [{"cell_type": "markdown", "source": ["x = 0.0001"]}]}
        out = extract_prose_numbers(json.dumps(nb))
        # 0.0001 < D1_PROSE_MIN=1e-3, donc filtre
        assert out == []

    def test_filters_above_max(self):
        nb = {"cells": [{"cell_type": "markdown", "source": ["Epic #4588"]}]}
        out = extract_prose_numbers(json.dumps(nb))
        # 4588 > D1_PROSE_MAX=1e3, donc filtre
        assert out == []

    def test_filters_negative(self):
        nb = {"cells": [{"cell_type": "markdown", "source": ["delta = -1"]}]}
        out = extract_prose_numbers(json.dumps(nb))
        # -1 est <= 0, donc filtre
        assert out == []

    def test_keeps_typical_measurement(self):
        nb = {"cells": [{"cell_type": "markdown", "source": ["Phi = 0.69"]}]}
        out = extract_prose_numbers(json.dumps(nb))
        assert len(out) == 1
        assert out[0][1] == pytest.approx(0.69)
        assert out[0][0] == 0  # cell index

    def test_keeps_integer_in_range(self):
        nb = {"cells": [{"cell_type": "markdown", "source": ["alpha = 5"]}]}
        out = extract_prose_numbers(json.dumps(nb))
        assert len(out) == 1
        assert out[0][1] == 5.0

    def test_multiple_values(self):
        nb = {
            "cells": [
                {
                    "cell_type": "markdown",
                    "source": ["alpha = 0.5\nbeta = 0.3\ngamma = 100"],
                }
            ]
        }
        out = extract_prose_numbers(json.dumps(nb))
        assert len(out) == 3
        values = {v for _, v in out}
        assert 0.5 in values
        assert 0.3 in values
        # 100 est dans [D1_PROSE_MIN, D1_PROSE_MAX], donc garde
        assert 100 in values

    def test_code_cells_excluded(self):
        nb = {
            "cells": [
                {"cell_type": "code", "source": ["x = 0.5"]},
                {"cell_type": "markdown", "source": ["y = 0.5"]},
            ]
        }
        out = extract_prose_numbers(json.dumps(nb))
        # Seul 0.5 du markdown cell[1] survit
        assert len(out) == 1
        assert out[0][0] == 1

    def test_invalid_json(self):
        out = extract_prose_numbers("not json")
        assert out == []


# ============================================================================ #
#  Classification des commits
# ============================================================================ #


class TestCommitClassification:
    """Tests sur les predicats de classification d'un commit."""

    def test_non_substantial_docs(self):
        assert _is_non_substantial("docs(readme): update links") is True

    def test_non_substantial_chore(self):
        assert _is_non_substantial("chore(repo): cleanup archives") is True

    def test_non_substantial_refactor(self):
        assert _is_non_substantial("refactor(ict): simplify helpers") is True

    def test_non_substantial_style(self):
        assert _is_non_substantial("style(lint): fix whitespace") is True

    def test_non_substantial_test(self):
        assert _is_non_substantial("test(ict): add regression") is True

    def test_substantial_feat(self):
        # feat() n'est PAS dans NON_SUBSTANTIAL_PREFIXES.
        assert _is_non_substantial("feat(ict): new detector") is False

    def test_substantial_fix_major(self):
        # fix() n'est PAS dans NON_SUBSTANTIAL_PREFIXES (trop large).
        assert _is_non_substantial("fix(ict): correct calibration") is False

    def test_substantial_data(self):
        # data(dataset): ajoute des donnees -> substantiel
        assert _is_non_substantial("data(qc): add Binance CSV") is False

    def test_case_insensitive(self):
        assert _is_non_substantial("DOCS(readme): MAJ") is True
        assert _is_non_substantial("Chore(repo): cleanup") is True

    def test_restore_verb(self):
        assert _has_restore_verb("restore(notebook): rollback outputs") is True
        assert _has_restore_verb("revert(#9416): back out broken commit") is True
        assert _has_restore_verb("rollback after outage") is True
        assert _has_restore_verb("resurrect old notebook") is True

    def test_no_restore_verb(self):
        assert _has_restore_verb("feat(ict): add module") is False
        assert _has_restore_verb("fix(ict): correct typo") is False

    def test_rename_verb(self):
        assert _has_rename_verb("relocate(notebook): move to archive") is True
        assert _has_rename_verb("rename(dir): cleaner structure") is True
        assert _has_rename_verb("reorganize(repos): merge families") is True
        assert _has_rename_verb("move to production") is True
        assert _has_rename_verb("homogenize(naming): consistent prefix") is True
        assert _has_rename_verb("repackage modules") is True

    def test_no_rename_verb(self):
        assert _has_rename_verb("feat(ict): new detector") is False


# ============================================================================ #
#  Detecteurs D3, D4, D5 (avec revisions simulees)
# ============================================================================ #


def _rev(sha: str, subject: str, nums: list[float], *, non_substantial: bool = False) -> NotebookRevision:
    return NotebookRevision(
        sha=sha,
        subject=subject,
        is_non_substantial=non_substantial,
        numbers_in_outputs=nums,
        cells_count=3,
    )


class TestDetectD3:
    """Tests sur detect_d3 (restauration partielle)."""

    def test_no_findings_no_restore(self):
        revs = [
            _rev("aaa", "feat(ict): new", [1, 2, 3]),
            _rev("bbb", "feat(ict): update", [4, 5, 6]),
        ]
        assert detect_d3(revs) == []

    def test_restore_without_change(self):
        # Restore qui ne change PAS la signature : pas un D3+.
        revs = [
            _rev("aaa", "feat(ict): some change", [1, 2, 3]),
            _rev("bbb", "restore: rollback to aaa", [1, 2, 3]),  # memes nums
        ]
        assert detect_d3(revs) == []

    def test_restore_with_change(self):
        # Restore qui CHANGE la signature : D3+.
        revs = [
            _rev("aaa", "feat(ict): some change", [1, 2, 3]),
            _rev("bbb", "restore: rollback to aaa", [10, 20, 30]),  # different
        ]
        findings = detect_d3(revs)
        assert len(findings) == 1
        assert findings[0].category == "D3"
        assert findings[0].sha == "bbb"

    def test_revert_with_change(self):
        revs = [
            _rev("aaa", "feat(ict): change", [5, 5, 5]),
            _rev("bbb", "revert(#123): back out", [10, 10, 10]),
        ]
        findings = detect_d3(revs)
        assert len(findings) == 1
        assert findings[0].subject.startswith("revert")


class TestDetectD4:
    """Tests sur detect_d4 (rename transportant une valeur)."""

    def test_rename_without_change(self):
        revs = [
            _rev("aaa", "feat(ict): some content", [1, 2, 3]),
            _rev("bbb", "rename(dir): cleanup", [1, 2, 3]),
        ]
        assert detect_d4(revs) == []

    def test_rename_with_change(self):
        revs = [
            _rev("aaa", "feat(ict): some content", [1, 2, 3]),
            _rev("bbb", "relocate: move to archive", [10, 20, 30]),
        ]
        findings = detect_d4(revs)
        assert len(findings) == 1
        assert findings[0].category == "D4"
        assert findings[0].sha == "bbb"

    def test_relocate_with_change(self):
        revs = [
            _rev("aaa", "feat(ict): init", [5, 5, 5]),
            _rev("bbb", "move to better location", [10, 10, 10]),
        ]
        findings = detect_d4(revs)
        assert len(findings) == 1


class TestDetectD5:
    """Tests sur detect_d5 (saut sous commit non-substantiel)."""

    def test_no_finding_under_substantial(self):
        # Saut numerique sous commit substantiel = OK (feat/fix n'est pas non-sub).
        revs = [
            _rev("aaa", "feat(ict): change", [1, 2, 3]),
            _rev("bbb", "feat(ict): bigger change", [10, 20, 30]),
        ]
        assert detect_d5(revs) == []

    def test_finding_under_docs(self):
        # Saut numerique sous docs = D5+ (les docs ne devraient pas changer les outputs).
        revs = [
            _rev("aaa", "feat(ict): content", [1, 2, 3]),
            _rev(
                "bbb",
                "docs(readme): typo fix",
                [10, 20, 30],
                non_substantial=True,
            ),
        ]
        findings = detect_d5(revs)
        assert len(findings) == 1
        assert findings[0].category == "D5"
        assert findings[0].sha == "bbb"

    def test_no_finding_below_threshold(self):
        # Saut de 10% sous docs = pas un D5 (seuil = 20%).
        revs = [
            _rev("aaa", "feat(ict): content", [1.0, 1.1, 1.2]),
            _rev(
                "bbb",
                "docs: minor",
                [1.1, 1.2, 1.3],
                non_substantial=True,
            ),
        ]
        assert detect_d5(revs) == []

    def test_empty_outputs(self):
        revs = [
            _rev("aaa", "feat(ict): empty", []),
            _rev("bbb", "docs: empty", [], non_substantial=True),
        ]
        assert detect_d5(revs) == []


# ============================================================================ #
#  Render / orchestration
# ============================================================================ #


class TestRenderText:
    """Tests sur render_text (sortie texte)."""

    def test_empty_results(self):
        out = render_text([])
        assert "| Notebook |" in out
        assert "## Detail" in out

    def test_sain_notebook_in_table(self):
        nb = NotebookForensic(
            path="foo.ipynb",
            total_revisions=5,
            verdict="SAIN",
            findings=[],
            notes="aucune degenerescence",
        )
        out = render_text([nb])
        assert "foo.ipynb" in out
        assert "SAIN" in out

    def test_findings_in_detail(self):
        nb = NotebookForensic(
            path="bar.ipynb",
            total_revisions=3,
            verdict="D3+",
            findings=[
                ForensicFinding(
                    category="D3",
                    sha="abc123",
                    subject="restore old",
                    detail="mediane 1 -> 5",
                )
            ],
            notes="",
        )
        out = render_text([nb])
        assert "bar.ipynb" in out
        assert "D3" in out
        assert "abc123" in out


# ============================================================================ #
#  CLI --check
# ============================================================================ #


class TestCLI:
    """Tests sur le CLI (mode --check, formats)."""

    def test_check_exits_1_on_pathological(self, tmp_path: Path, monkeypatch, capsys):
        # Cree un mini-repo git avec un notebook pathologique.
        import subprocess
        repo = tmp_path / "mini_repo"
        repo.mkdir()
        subprocess.run(["git", "init", "-q"], cwd=str(repo), check=True)
        subprocess.run(["git", "config", "user.email", "test@test"], cwd=str(repo), check=True)
        subprocess.run(["git", "config", "user.name", "Test"], cwd=str(repo), check=True)

        # Cree un notebook simple.
        nb = {
            "cells": [
                {"cell_type": "markdown", "source": ["Phi = 0.69"]},
                {
                    "cell_type": "code",
                    "outputs": [{"text": "0.42"}],  # DIFFERENT de 0.69 en prose
                },
            ]
        }
        nb_path = repo / "test.ipynb"
        nb_path.write_text(json.dumps(nb))

        subprocess.run(["git", "add", "test.ipynb"], cwd=str(repo), check=True)
        subprocess.run(["git", "commit", "-q", "-m", "init"], cwd=str(repo), check=True)

        # Lance le CLI en mode check.
        rc = main(["--repo", str(repo), "--check", "test.ipynb"])
        # Avec 1 orphelin / 1 mesure = 100% > 30%, donc D1+ => exit 1.
        assert rc == 1

    def test_check_exits_0_on_clean(self, tmp_path: Path):
        import subprocess
        repo = tmp_path / "mini_repo"
        repo.mkdir()
        subprocess.run(["git", "init", "-q"], cwd=str(repo), check=True)
        subprocess.run(["git", "config", "user.email", "test@test"], cwd=str(repo), check=True)
        subprocess.run(["git", "config", "user.name", "Test"], cwd=str(repo), check=True)

        # Notebook sans prose mesurable, avec outputs : pas de D1.
        nb = {
            "cells": [
                {"cell_type": "markdown", "source": ["# Title"]},
                {"cell_type": "code", "outputs": [{"text": "0.42"}]},
            ]
        }
        nb_path = repo / "test.ipynb"
        nb_path.write_text(json.dumps(nb))
        subprocess.run(["git", "add", "test.ipynb"], cwd=str(repo), check=True)
        subprocess.run(["git", "commit", "-q", "-m", "init"], cwd=str(repo), check=True)

        rc = main(["--repo", str(repo), "--check", "test.ipynb"])
        assert rc == 0

    def test_json_format(self, tmp_path: Path, capsys):
        import subprocess
        repo = tmp_path / "mini_repo"
        repo.mkdir()
        subprocess.run(["git", "init", "-q"], cwd=str(repo), check=True)
        subprocess.run(["git", "config", "user.email", "t@t"], cwd=str(repo), check=True)
        subprocess.run(["git", "config", "user.name", "T"], cwd=str(repo), check=True)

        nb = {"cells": [{"cell_type": "markdown", "source": ["a"]}]}
        nb_path = repo / "x.ipynb"
        nb_path.write_text(json.dumps(nb))
        subprocess.run(["git", "add", "x.ipynb"], cwd=str(repo), check=True)
        subprocess.run(["git", "commit", "-q", "-m", "init"], cwd=str(repo), check=True)

        rc = main(["--repo", str(repo), "--format", "json", "x.ipynb"])
        captured = capsys.readouterr()
        assert rc == 0
        data = json.loads(captured.out)
        assert isinstance(data, list)
        assert len(data) == 1
        assert data[0]["path"].endswith("x.ipynb")
