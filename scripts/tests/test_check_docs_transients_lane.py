"""Tests for scripts/check_docs_transients_lane.py -- the transient-reports lane (#14623).

Covers both directions of the contract (inside the lane: dated name + frozen
header + agreeing dates; outside: no stray report header in header position),
the exemptions (lane README, docs/archive/, quoted convention), the CLI exit
codes, and the real repository tree.
"""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import check_docs_transients_lane as lane

HEADER = "> RAPPORT — 2026-09-29 — perimetre d'exemple — figé"


@pytest.fixture()
def tree(tmp_path: Path) -> Path:
    """Minimal repo-shaped tree: lane + archive + one perennial doc."""
    (tmp_path / "docs" / "transients").mkdir(parents=True)
    (tmp_path / "docs" / "archive").mkdir(parents=True)
    (tmp_path / "docs" / "reference").mkdir(parents=True)
    (tmp_path / "docs" / "transients" / "README.md").write_text(
        "# Rapports transients\n", encoding="utf-8"
    )
    (tmp_path / "docs" / "reference" / "doc.md").write_text(
        "# Reference vivante\n", encoding="utf-8"
    )
    return tmp_path


def _write_report(tree: Path, name: str, body: str) -> Path:
    path = tree / "docs" / "transients" / name
    path.write_text(body, encoding="utf-8")
    return path


def _reasons(report: dict) -> list[str]:
    return [finding["reason"].split(":")[0] for finding in report["findings"]]


def test_empty_lane_is_conforme(tree: Path) -> None:
    report = lane.run(root=tree)
    assert report["verdict"] == "CONFORME"
    assert report["findings"] == []
    assert report["lane_files"] == 0
    assert report["outside_scanned"] == 1  # docs/reference/doc.md only


def test_lane_file_conforme(tree: Path) -> None:
    _write_report(tree, "2026-09-29-audit-exemple.md", f"# Audit\n{HEADER}\n\ntexte\n")
    report = lane.run(root=tree)
    assert report["verdict"] == "CONFORME", report["findings"]
    assert report["lane_files"] == 1


def test_lane_readme_is_exempt(tree: Path) -> None:
    # README.md carries no date prefix and no header by design.
    report = lane.run(root=tree)
    assert report["findings"] == []


def test_missing_date_prefix_is_a_violation(tree: Path) -> None:
    _write_report(tree, "audit-sans-date.md", f"# Audit\n{HEADER}\n")
    report = lane.run(root=tree)
    assert report["verdict"] == "VIOLATION"
    assert _reasons(report) == ["NO_DATE_PREFIX"]


def test_missing_header_is_a_violation(tree: Path) -> None:
    _write_report(tree, "2026-09-29-sans-en-tete.md", "# Audit\n\ntexte\n")
    report = lane.run(root=tree)
    assert report["verdict"] == "VIOLATION"
    assert _reasons(report) == ["NO_HEADER"]


def test_header_date_must_match_filename(tree: Path) -> None:
    _write_report(
        tree, "2026-09-28-decalage.md", f"# Audit\n{HEADER}\n"
    )  # header says 09-29
    report = lane.run(root=tree)
    assert report["verdict"] == "VIOLATION"
    assert _reasons(report) == ["DATE_MISMATCH"]


def test_stray_header_outside_lane_is_flagged(tree: Path) -> None:
    (tree / "docs" / "reference" / "doc.md").write_text(
        f"{HEADER}\n# Reference\n", encoding="utf-8"
    )
    report = lane.run(root=tree)
    assert report["verdict"] == "VIOLATION"
    assert _reasons(report) == ["STRAY_REPORT_HEADER"]


def test_archive_is_exempt(tree: Path) -> None:
    (tree / "docs" / "archive" / "vieux-rapport.md").write_text(
        f"{HEADER}\n# Vieux rapport\n", encoding="utf-8"
    )
    report = lane.run(root=tree)
    assert report["verdict"] == "CONFORME", report["findings"]


def test_quoted_header_deep_in_document_is_ignored(tree: Path) -> None:
    body = "# Doc perenne\n\n" + "\n".join(f"ligne {i}" for i in range(12)) + f"\n\n{HEADER}\n"
    (tree / "docs" / "reference" / "doc.md").write_text(body, encoding="utf-8")
    report = lane.run(root=tree)
    assert report["verdict"] == "CONFORME", report["findings"]


def test_dash_and_accent_variants_are_tolerated(tree: Path) -> None:
    tolerant = "> RAPPORT - 2026-09-29 - perimetre - fige"
    _write_report(tree, "2026-09-29-variantes.md", f"# Audit\n{tolerant}\n")
    report = lane.run(root=tree)
    assert report["verdict"] == "CONFORME", report["findings"]


def test_cli_exit_codes_and_json(tree: Path, capsys: pytest.CaptureFixture) -> None:
    _write_report(tree, "audit-sans-date.md", f"# Audit\n{HEADER}\n")
    assert lane.main(["--root", str(tree), "--json"]) == 1
    payload = json.loads(capsys.readouterr().out)
    assert payload["verdict"] == "VIOLATION"

    (tree / "docs" / "transients" / "audit-sans-date.md").unlink()
    assert lane.main(["--root", str(tree)]) == 0
    assert "CONFORME" in capsys.readouterr().out


def test_real_tree_is_conforme() -> None:
    """Wiring: the repository's own tree must satisfy the convention."""
    report = lane.run()
    assert report["verdict"] == "CONFORME", report["findings"]


# --- Third direction: archive entry ban (--base, tranche 2 #14623) ---


def _archive_file(tree: Path, rel: str, body: str = "# Rapport\n") -> Path:
    path = tree / rel
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(body, encoding="utf-8")
    return path


def test_archive_creation_dated_name_is_flagged(tree: Path) -> None:
    _archive_file(tree, "docs/archive/2026-09-30-sweep-9999.md")
    findings = lane.scan_archive_additions(
        tree, [("A", "", "docs/archive/2026-09-30-sweep-9999.md")]
    )
    assert _reasons({"findings": findings}) == ["ARCHIVE_NEW_REPORT"]


def test_archive_creation_frozen_header_is_flagged(tree: Path) -> None:
    _archive_file(
        tree,
        "docs/archive/analyse.md",  # not dated: the header alone triggers
        f"{HEADER}\n# Analyse\n",
    )
    findings = lane.scan_archive_additions(
        tree, [("A", "", "docs/archive/analyse.md")]
    )
    assert _reasons({"findings": findings}) == ["ARCHIVE_NEW_REPORT"]


def test_archive_creation_without_signature_passes(tree: Path) -> None:
    _archive_file(tree, "docs/archive/INDEX.md", "# Index\n")
    findings = lane.scan_archive_additions(
        tree, [("A", "", "docs/archive/INDEX.md")]
    )
    assert findings == []


def test_archive_rename_is_a_reclassification_and_passes(tree: Path) -> None:
    # R100 = move into the archive: permitted, whatever the signature.
    _archive_file(tree, "docs/archive/2026-09-30-deplace.md")
    findings = lane.scan_archive_additions(
        tree,
        [("R100", "docs/transients/2026-09-30-deplace.md",
          "docs/archive/2026-09-30-deplace.md")],
    )
    assert findings == []


def test_archive_modification_of_existing_stock_passes(tree: Path) -> None:
    _archive_file(tree, "docs/archive/2026-07-11-sweep-5975.md")
    findings = lane.scan_archive_additions(
        tree, [("M", "", "docs/archive/2026-07-11-sweep-5975.md")]
    )
    assert findings == []


def test_git_failure_is_a_finding_not_a_pass(tree: Path) -> None:
    findings = lane.scan_archive_additions(tree, None)
    assert _reasons({"findings": findings}) == ["GIT_DIFF_FAILED"]


def test_run_with_base_wires_archive_findings(
    tree: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    _archive_file(tree, "docs/archive/2026-09-30-essai.md")
    monkeypatch.setattr(
        lane,
        "_git_archive_entries",
        lambda root, base: [("A", "", "docs/archive/2026-09-30-essai.md")],
    )
    report = lane.run(root=tree, base="origin/main")
    assert report["verdict"] == "VIOLATION"
    assert _reasons(report) == ["ARCHIVE_NEW_REPORT"]
    assert report["archive_base"] == "origin/main"
    assert report["archive_entries"] == 1


def test_run_without_base_skips_archive_direction(
    tree: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    # No --base: the organ keeps its historical two-direction contract.
    called = []
    monkeypatch.setattr(
        lane, "_git_archive_entries", lambda root, base: called.append(base)
    )
    report = lane.run(root=tree)
    assert report["verdict"] == "CONFORME", report["findings"]
    assert called == []
    assert report["archive_base"] is None


def test_cli_base_flag_reports_archive_line(
    tree: Path, monkeypatch: pytest.MonkeyPatch, capsys: pytest.CaptureFixture
) -> None:
    monkeypatch.setattr(
        lane, "_git_archive_entries", lambda root, base: []
    )
    assert lane.main(["--root", str(tree), "--base", "origin/main"]) == 0
    out = capsys.readouterr().out
    assert "archive" in out and "origin/main" in out