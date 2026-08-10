#!/usr/bin/env python3
"""Tests for ``scripts/translation/check_translation_parity.py`` — the parity
gate of the i18n translation pipeline (Epic #10038 grain B).

Covers the 4 invariants from issue #10041 §2 + the falsifications demanded
by the grain B acceptance + 1 legitimate-case test (FR in code cell =
PASS, per corollaire D2).

stdlib-only (json/pathlib/re/argparse/pytest). Hermetic — no network,
no filesystem side effects beyond tmp_path fixtures.

Mirror of the test pattern established by ``test_check_perimeter.py``
(grain E) and ``test_check_translation_sync.py`` (T2 drift).
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
TRANSLATION_DIR = HERE.parent
sys.path.insert(0, str(TRANSLATION_DIR))

import check_translation_parity as p  # noqa: E402


# ---------------------------------------------------------------------------
# Helpers — notebook builders (return path to .ipynb)
# ---------------------------------------------------------------------------


def _write_nb(path: Path, cells: list[dict]) -> None:
    """Write a minimal valid nbformat 4.5 notebook to ``path``."""
    path.parent.mkdir(parents=True, exist_ok=True)
    nb = {
        "cells": cells,
        "metadata": {},
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    path.write_text(json.dumps(nb, ensure_ascii=False), encoding="utf-8")


def _code_cell(cid: str, source: str, outputs: list | None = None,
               execution_count: int | None = 1) -> dict:
    return {
        "cell_type": "code",
        "id": cid,
        "metadata": {},
        "execution_count": execution_count,
        "outputs": outputs if outputs is not None else [],
        "source": [line + "\n" for line in source.split("\n") if line is not None]
        if source
        else [],
    }


def _md_cell(cid: str, source: str) -> dict:
    return {
        "cell_type": "markdown",
        "id": cid,
        "metadata": {},
        "source": [line + "\n" for line in source.split("\n") if line is not None]
        if source
        else [],
    }


def _write_pair(
    root: Path,
    stem: str,
    src_cells: list[dict],
    trd_cells: list[dict],
    lang: str = "en",
) -> tuple[Path, Path]:
    """Write ``{stem}.ipynb`` and ``{stem}_{lang}.ipynb`` under root."""
    src_path = root / f"{stem}.ipynb"
    trd_path = root / f"{stem}_{lang}.ipynb"
    _write_nb(src_path, src_cells)
    _write_nb(trd_path, trd_cells)
    return src_path, trd_path


# ---------------------------------------------------------------------------
# Nominal — well-formed pair satisfies all 4 invariants
# ---------------------------------------------------------------------------


def test_nominal_pair_passes_all_invariants(tmp_path):
    """A T4-style rendered notebook (code byte-identical, md all translated)
    must produce 0 violations and verdict OK."""
    src_cells = [
        _md_cell("c1", "# Titre\n\nUn paragraphe d'introduction."),
        _code_cell("c2", "x = 1\nprint(x)", outputs=[], execution_count=1),
        _md_cell("c3", "## Section\n\nExplication detaillee."),
    ]
    trd_cells = [
        _md_cell("c1", "# Title\n\nAn intro paragraph."),
        _code_cell("c2", "x = 1\nprint(x)", outputs=[], execution_count=1),
        _md_cell("c3", "## Section\n\nDetailed explanation."),
    ]
    src, trd = _write_pair(tmp_path, "Demo-01", src_cells, trd_cells)
    src_records, src_err = p.load_cells(src)
    trd_records, trd_err = p.load_cells(trd)
    assert src_err is None
    assert trd_err is None
    anomalies = p.check_invariants(src_records, trd_records)
    blocking = [a for a in anomalies if a.verdict != "FR_CONTAM"]
    assert blocking == []


# ---------------------------------------------------------------------------
# Falsification 1 — modify one byte in code cell -> CODE_DRIFT
# ---------------------------------------------------------------------------


def test_falsif_1_code_byte_modification_yields_code_drift(tmp_path):
    """Modifying a single byte in a code cell must trigger CODE_DRIFT on the
    ``source`` field of that cell."""
    src_cells = [
        _code_cell("c1", "x = 1", outputs=[], execution_count=1),
    ]
    trd_cells = [
        # T4 invariant violated : code byte-drift.
        _code_cell("c1", "x = 2", outputs=[], execution_count=1),
    ]
    src, trd = _write_pair(tmp_path, "Drift-01", src_cells, trd_cells)
    src_records, _ = p.load_cells(src)
    trd_records, _ = p.load_cells(trd)
    anomalies = p.check_invariants(src_records, trd_records)
    code_drifts = [a for a in anomalies if a.verdict == "CODE_DRIFT"]
    assert len(code_drifts) >= 1
    fields = {a.detail.get("field") for a in code_drifts}
    assert "source" in fields


def test_falsif_1b_execution_count_drift_yields_code_drift(tmp_path):
    """Code byte-identical but execution_count differs -> CODE_DRIFT on EC field."""
    src_cells = [_code_cell("c1", "x = 1", outputs=[], execution_count=1)]
    trd_cells = [_code_cell("c1", "x = 1", outputs=[], execution_count=2)]
    src, trd = _write_pair(tmp_path, "Drift-01b", src_cells, trd_cells)
    src_records, _ = p.load_cells(src)
    trd_records, _ = p.load_cells(trd)
    anomalies = p.check_invariants(src_records, trd_records)
    code_drifts = [a for a in anomalies if a.verdict == "CODE_DRIFT"]
    fields = {a.detail.get("field") for a in code_drifts}
    assert "execution_count" in fields


# ---------------------------------------------------------------------------
# Falsification 2 — add output absent from source -> OUTPUT_FABRICATED
# ---------------------------------------------------------------------------


def test_falsif_2_added_output_yields_output_fabricated(tmp_path):
    """A translation cell whose ``outputs`` array is non-empty while the source
    cell has ``outputs == []`` must trigger OUTPUT_FABRICATED."""
    src_cells = [
        _code_cell("c1", "x = 1", outputs=[], execution_count=None),
    ]
    trd_cells = [
        _code_cell(
            "c1", "x = 1",
            outputs=[
                {
                    "output_type": "stream",
                    "name": "stdout",
                    "text": ["fake\n"],
                }
            ],
            execution_count=1,
        ),
    ]
    src, trd = _write_pair(tmp_path, "Fab-01", src_cells, trd_cells)
    src_records, _ = p.load_cells(src)
    trd_records, _ = p.load_cells(trd)
    anomalies = p.check_invariants(src_records, trd_records)
    fabricated = [a for a in anomalies if a.verdict == "OUTPUT_FABRICATED"]
    assert len(fabricated) == 1
    assert fabricated[0].cell_id == "c1"


# ---------------------------------------------------------------------------
# Falsification 3 — delete a cell -> STRUCTURE_DRIFT
# ---------------------------------------------------------------------------


def test_falsif_3_cell_deletion_yields_structure_drift(tmp_path):
    """Translation missing a cell that the source has -> STRUCTURE_DRIFT."""
    src_cells = [
        _md_cell("c1", "# Title"),
        _md_cell("c2", "Body"),
        _md_cell("c3", "Conclusion"),
    ]
    trd_cells = [
        _md_cell("c1", "# Title"),
        _md_cell("c3", "Conclusion"),  # c2 deleted
    ]
    src, trd = _write_pair(tmp_path, "Struct-01", src_cells, trd_cells)
    src_records, _ = p.load_cells(src)
    trd_records, _ = p.load_cells(trd)
    anomalies = p.check_invariants(src_records, trd_records)
    drifts = [a for a in anomalies if a.verdict == "STRUCTURE_DRIFT"]
    assert len(drifts) == 1
    assert "c2" in drifts[0].detail.get("deleted_cells", [])


def test_falsif_3b_cell_reorder_yields_structure_drift(tmp_path):
    """Same cell set, different order -> STRUCTURE_DRIFT with reorder flag."""
    src_cells = [
        _md_cell("c1", "A"),
        _md_cell("c2", "B"),
    ]
    trd_cells = [
        _md_cell("c2", "B"),
        _md_cell("c1", "A"),
    ]
    src, trd = _write_pair(tmp_path, "Struct-01b", src_cells, trd_cells)
    src_records, _ = p.load_cells(src)
    trd_records, _ = p.load_cells(trd)
    anomalies = p.check_invariants(src_records, trd_records)
    drifts = [a for a in anomalies if a.verdict == "STRUCTURE_DRIFT"]
    assert len(drifts) == 1
    assert drifts[0].detail.get("reorder_detected") is True


# ---------------------------------------------------------------------------
# FR_CONTAM — markdown identical to FR
# ---------------------------------------------------------------------------


def test_fr_contam_advisory_default_does_not_block(tmp_path):
    """A markdown cell with text identical to the FR source must emit FR_CONTAM
    but in advisory mode (detail.advisory=True), exit 0 under default policy."""
    src_cells = [_md_cell("c1", "# Titre\n\nUn paragraphe detaille.")]
    trd_cells = [_md_cell("c1", "# Titre\n\nUn paragraphe detaille.")]
    src, trd = _write_pair(tmp_path, "Contam-01", src_cells, trd_cells)
    src_records, _ = p.load_cells(src)
    trd_records, _ = p.load_cells(trd)
    anomalies = p.check_invariants(src_records, trd_records)  # default strict_fr=False
    fr_contam = [a for a in anomalies if a.verdict == "FR_CONTAM"]
    assert len(fr_contam) == 1
    assert fr_contam[0].detail.get("advisory") is True


def test_fr_contam_strict_blocks(tmp_path):
    """Under ``strict_fr=True``, FR_CONTAM must be added to the blocking list.
    The CLI gate promotes advisory -> blocking via the strict_fr flag (tested
    end-to-end below)."""
    src_cells = [_md_cell("c1", "# Titre\n\nUn paragraphe detaille.")]
    trd_cells = [_md_cell("c1", "# Titre\n\nUn paragraphe detaille.")]
    src, trd = _write_pair(tmp_path, "Contam-01b", src_cells, trd_cells)
    src_records, _ = p.load_cells(src)
    trd_records, _ = p.load_cells(trd)
    anomalies = p.check_invariants(src_records, trd_records, strict_fr=True)
    fr_contam = [a for a in anomalies if a.verdict == "FR_CONTAM"]
    assert len(fr_contam) == 1
    # Under strict_fr, the advisory marker is NOT set (the anomaly becomes blocking).
    assert "advisory" not in fr_contam[0].detail


# ---------------------------------------------------------------------------
# FR_CONTAM — by-design-English source cell (#10298)
# A markdown cell copied verbatim from an EN research doc is legitimately
# identical FR -> _en (the source is already English). FR_CONTAM must NOT fire.
# ---------------------------------------------------------------------------

# Substantial EN text (0% French diacritics, > 80 alpha chars) — mimics the real
# deep_research_optimization cell (calibration: real FR cells measure >= 2.6%).
_BY_DESIGN_EN_TEXT = (
    "# Deep Research: Sector Momentum Optimization\n\n"
    "## Objective\nMaximize Sharpe ratio for the Sector Momentum strategy.\n\n"
    "## Strategy Overview\n"
    "- Assets: sector ETFs\n"
    "- Signal: Dual momentum (relative strength plus absolute momentum)\n"
    "- Rebalancing: Monthly rotation to top-performing sectors\n"
    "- Risk Management: VIX filter to skip rebalancing in high-volatility regimes\n"
)
# Substantial FR text (carries diacritics) — must STILL flag under strict_fr.
_REAL_FR_TEXT = (
    "# Recherche Approfondie : Optimisation de la Dynamique Sectorielle\n\n"
    "## Objectif\nMaximiser le ratio de Sharpe pour la stratégie de momentum sectoriel.\n"
    "## Analyse\nLes métriques de performance sont calculées à partir des rendements passés."
)


def test_by_design_english_source_not_flagged_strict(tmp_path):
    """A long EN source cell (0% French diacritics) identical FR -> _en is NOT
    FR_CONTAM even under strict_fr — the source is already English, no FR lost."""
    src_cells = [_md_cell("c1", _BY_DESIGN_EN_TEXT)]
    trd_cells = [_md_cell("c1", _BY_DESIGN_EN_TEXT)]  # identical render (legitimate)
    src, trd = _write_pair(tmp_path, "ByDesignEN-01", src_cells, trd_cells)
    src_records, _ = p.load_cells(src)
    trd_records, _ = p.load_cells(trd)
    anomalies = p.check_invariants(src_records, trd_records, strict_fr=True)
    assert not [a for a in anomalies if a.verdict == "FR_CONTAM"]


def test_by_design_english_does_not_suppress_real_fr(tmp_path):
    """The heuristic must NOT suppress a real FR cell of similar length — a
    French source carries diacritics (>= 2% measured), which clears the threshold.
    Negative control: the detector keeps its discriminating power."""
    src_cells = [_md_cell("c1", _REAL_FR_TEXT)]
    trd_cells = [_md_cell("c1", _REAL_FR_TEXT)]  # untranslated real FR -> genuine contam
    src, trd = _write_pair(tmp_path, "ByDesignEN-02", src_cells, trd_cells)
    src_records, _ = p.load_cells(src)
    trd_records, _ = p.load_cells(trd)
    anomalies = p.check_invariants(src_records, trd_records, strict_fr=True)
    fr_contam = [a for a in anomalies if a.verdict == "FR_CONTAM"]
    assert len(fr_contam) == 1, "real FR cell must still flag (heuristic not over-suppressing)"


def test_by_design_english_short_cell_still_flagged(tmp_path):
    """A short FR fragment without diacritics ('# Code') is NOT whitelisted — the
    min-length guard prevents the heuristic from masking short untranslated cells."""
    src_cells = [_md_cell("c1", "# Code")]
    trd_cells = [_md_cell("c1", "# Code")]
    src, trd = _write_pair(tmp_path, "ByDesignEN-03", src_cells, trd_cells)
    src_records, _ = p.load_cells(src)
    trd_records, _ = p.load_cells(trd)
    anomalies = p.check_invariants(src_records, trd_records, strict_fr=True)
    assert len([a for a in anomalies if a.verdict == "FR_CONTAM"]) == 1


# ---------------------------------------------------------------------------
# Legitimate case (corollaire D2) — FR text inside a CODE cell is OK
# ---------------------------------------------------------------------------


def test_fr_in_code_cell_is_legitimate(tmp_path):
    """Per corollaire D2 of issue #10041 : FR string literals inside code cells
    (e.g. ``print("Bonjour")``) are legitimate and MUST NOT trigger any verdict.
    Only code bytes + outputs + execution_count are checked; the code itself can
    legitimately contain FR text."""
    src_cells = [
        _code_cell(
            "c1",
            'msg = "Bonjour le monde"\nprint(msg)',
            outputs=[
                {
                    "output_type": "stream",
                    "name": "stdout",
                    "text": ["Bonjour le monde\n"],
                }
            ],
            execution_count=1,
        ),
    ]
    trd_cells = [
        _code_cell(
            "c1",
            'msg = "Bonjour le monde"\nprint(msg)',
            outputs=[
                {
                    "output_type": "stream",
                    "name": "stdout",
                    "text": ["Bonjour le monde\n"],
                }
            ],
            execution_count=1,
        ),
    ]
    src, trd = _write_pair(tmp_path, "FrCode-01", src_cells, trd_cells)
    src_records, _ = p.load_cells(src)
    trd_records, _ = p.load_cells(trd)
    anomalies = p.check_invariants(src_records, trd_records, strict_fr=True)
    assert anomalies == []


# ---------------------------------------------------------------------------
# load_cells — error paths
# ---------------------------------------------------------------------------


def test_load_cells_missing_file_returns_error(tmp_path):
    records, err = p.load_cells(tmp_path / "no_such_nb.ipynb")
    assert records == []
    assert err is not None
    assert "absent" in err


def test_load_cells_malformed_json_returns_error(tmp_path):
    nb_path = tmp_path / "broken.ipynb"
    nb_path.write_text("{ this is not json", encoding="utf-8")
    records, err = p.load_cells(nb_path)
    assert records == []
    assert err is not None
    assert "illisible" in err


def test_load_cells_missing_id_returns_error(tmp_path):
    """nbformat < 4.5 (no ``id`` on cells) is a hard error — without ids, the
    gate cannot establish correspondence."""
    nb = {
        "cells": [{"cell_type": "code", "source": ["x = 1\n"], "metadata": {}}],
        "metadata": {},
        "nbformat": 4,
        "nbformat_minor": 4,
    }
    nb_path = tmp_path / "no_ids.ipynb"
    nb_path.write_text(json.dumps(nb), encoding="utf-8")
    records, err = p.load_cells(nb_path)
    assert "id" in err


# ---------------------------------------------------------------------------
# discover_pairs — pure-pair enumeration
# ---------------------------------------------------------------------------


def test_discover_pairs_finds_both_directions(tmp_path):
    """A pair (src + _en) must be discovered once, regardless of walk order."""
    src_cells = [_md_cell("c1", "A")]
    trd_cells = [_md_cell("c1", "A-en")]
    _write_pair(tmp_path, "X-01", src_cells, trd_cells, lang="en")
    pairs = p.discover_pairs(tmp_path, ["en"])
    assert len(pairs) == 1
    src_path, trd_path, stem, lang = pairs[0]
    assert stem == "X-01"
    assert lang == "en"
    assert src_path.name == "X-01.ipynb"
    assert trd_path.name == "X-01_en.ipynb"


def test_discover_pairs_handles_orphan_translation(tmp_path):
    """A translation file with no source sibling must be picked up as orphan
    (STRUCTURE_DRIFT downstream)."""
    nb_path = tmp_path / "Orphan-01_en.ipynb"
    nb = {
        "cells": [_md_cell("c1", "A")],
        "metadata": {},
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    nb_path.write_text(json.dumps(nb), encoding="utf-8")
    pairs = p.discover_pairs(tmp_path, ["en"])
    # The orphan is found (its source path is missing, but the iteration sees it).
    found = any(p[1].name == "Orphan-01_en.ipynb" for p in pairs)
    assert found


def test_discover_pairs_lang_filter_excludes_other_langs(tmp_path):
    """A ``_ru`` translation must not appear in a scan restricted to ``en``."""
    _write_pair(
        tmp_path, "Multi-01",
        [_md_cell("c1", "FR")],
        [_md_cell("c1", "EN")],
        lang="en",
    )
    _write_pair(
        tmp_path, "Multi-01",
        [_md_cell("c1", "FR")],
        [_md_cell("c1", "RU")],
        lang="ru",
    )
    pairs_en = p.discover_pairs(tmp_path, ["en"])
    assert all(lang == "en" for _, _, _, lang in pairs_en)
    assert len(pairs_en) == 1


# ---------------------------------------------------------------------------
# End-to-end — CLI exit codes
# ---------------------------------------------------------------------------


def test_cli_nominal_returns_zero(tmp_path, capsys, monkeypatch):
    """A clean pair under the gate must produce exit 0 + verdict OK."""
    src_cells = [_md_cell("c1", "FR body"), _code_cell("c2", "x = 1",
                  outputs=[], execution_count=1)]
    trd_cells = [_md_cell("c1", "EN body"), _code_cell("c2", "x = 1",
                  outputs=[], execution_count=1)]
    _write_pair(tmp_path, "Clean-01", src_cells, trd_cells)
    monkeypatch.setattr(sys, "argv", [
        "check_translation_parity.py",
        "--repo-root", str(tmp_path),
        "--langs", "en",
        "--json-only",
    ])
    rc = p.main()
    out = capsys.readouterr().out
    report = json.loads(out)
    assert rc == 0
    assert report["verdict"] in ("OK", "OK_WITH_ADVISORIES")
    assert report["pair_count"] == 1


def test_cli_blocks_on_code_drift(tmp_path, capsys, monkeypatch):
    """A pair with CODE_DRIFT must exit 1 with verdict PARITY_VIOLATION."""
    src_cells = [_code_cell("c1", "x = 1", outputs=[], execution_count=1)]
    trd_cells = [_code_cell("c1", "x = 99", outputs=[], execution_count=1)]
    _write_pair(tmp_path, "Bad-01", src_cells, trd_cells)
    monkeypatch.setattr(sys, "argv", [
        "check_translation_parity.py",
        "--repo-root", str(tmp_path),
        "--langs", "en",
        "--json-only",
    ])
    rc = p.main()
    out = capsys.readouterr().out
    report = json.loads(out)
    assert rc == 1
    assert report["verdict"] == "PARITY_VIOLATION"
    assert report["blocking_count"] == 1


def test_cli_strict_fr_blocks_on_fr_contam(tmp_path, capsys, monkeypatch):
    """Under ``--strict-fr``, an FR_CONTAM cell must produce exit 1."""
    src_cells = [_md_cell("c1", "# Un titre detaille\n\nLong body.")]
    trd_cells = [_md_cell("c1", "# Un titre detaille\n\nLong body.")]
    _write_pair(tmp_path, "Contam-strict", src_cells, trd_cells)
    monkeypatch.setattr(sys, "argv", [
        "check_translation_parity.py",
        "--repo-root", str(tmp_path),
        "--langs", "en",
        "--strict-fr",
        "--json-only",
    ])
    rc = p.main()
    out = capsys.readouterr().out
    report = json.loads(out)
    assert rc == 1


def test_cli_repo_root_missing_returns_two(tmp_path, capsys, monkeypatch):
    """--repo-root pointing at a non-existent dir must exit 2 (filesystem error)."""
    monkeypatch.setattr(sys, "argv", [
        "check_translation_parity.py",
        "--repo-root", str(tmp_path / "nope"),
        "--langs", "en",
        "--json-only",
    ])
    rc = p.main()
    assert rc == 2


# ---------------------------------------------------------------------------
# Reference — live state (manual)
# ---------------------------------------------------------------------------


def test_full_repo_state_passes_parity():
    """Reference test against the live ``xxx_<lang>.ipynb`` artifacts on main.

    This is NOT a hermetic test — it asserts the actual state of the repo
    passes its own parity gate. If this fails, either (a) a translation was
    hand-edited (must re-render via T4), or (b) the parity invariants need
    extending to cover a regression introduced by T4 itself.

    Expected state today (post-grain A MERGED): exactly one pair —
    ``FT-01-Introduction-FineTuning_en.ipynb`` — and it must satisfy all
    invariants including strict-fr (because grain A proved byte-identity
    + structure + no-FR-leak on md).
    """
    repo_root = HERE.parent.parent.parent  # scripts/translation/tests/ → repo root
    pairs = p.discover_pairs(repo_root, ["en", "ru"])
    # We expect exactly one pair: FT-01-Introduction-FineTuning (en only).
    # Other PRs (grain E #10047) may have brought additional pairs; we check
    # each one is OK.
    assert len(pairs) >= 1, "no translation pairs found on main"
    for src_path, trd_path, stem, lang in pairs:
        src_cells, src_err = p.load_cells(src_path)
        trd_cells, trd_err = p.load_cells(trd_path)
        assert src_err is None, f"source unreadable : {src_path} ({src_err})"
        assert trd_err is None, f"translation unreadable : {trd_path} ({trd_err})"
        anomalies = p.check_invariants(src_cells, trd_cells, strict_fr=True)
        blocking = [
            a
            for a in anomalies
            if a.verdict in ("CODE_DRIFT", "STRUCTURE_DRIFT", "OUTPUT_FABRICATED")
        ]
        fr_contam_strict = [a for a in anomalies if a.verdict == "FR_CONTAM"]
        assert blocking == [], (
            f"pair {stem}_{lang} has blocking anomalies : {blocking}"
        )
        assert fr_contam_strict == [], (
            f"pair {stem}_{lang} has FR_CONTAM under strict_fr : {fr_contam_strict}"
        )
