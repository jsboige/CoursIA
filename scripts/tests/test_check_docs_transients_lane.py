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


# --- distillation -- the fourth direction (#14623) --------------------------


def test_undated_slug_strips_the_lane_date_prefix() -> None:
    assert (
        lane._undated_slug("2026-08-10-variation-genre-census.md")
        == "variation-genre-census"
    )
    # Not in the lane's naming convention: nothing to strip, nothing to match.
    assert lane._undated_slug("README.md") is None
    assert lane._undated_slug("notes-diverses.md") is None


def test_distillation_flags_a_report_cited_only_by_navigation(
    tree: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """A sidebar entry proves reachability, not that the conclusion landed."""
    name = "2026-09-29-audit-exemple.md"
    _write_report(tree, name, f"# Audit\n{HEADER}\n\ntexte\n")
    monkeypatch.setattr(
        lane,
        "_git_citations",
        lambda root, needles: {name: {"_quarto.yml", "docs/README.md"}},
    )

    report = lane.run(root=tree, distillation=True)

    assert report["verdict"] == "CONFORME", "advisory by default: no exit change"
    summary = report["distillation"]
    assert summary["measured"] is True
    assert summary["reports"] == 1
    assert summary["distilled"] == 0
    assert summary["index_only"] == [name]
    assert _reasons(report) == []  # not in ``findings`` without --strict
    assert [f["reason"].split(":")[0] for f in report["distillation_findings"]] == [
        "DISTILLATION_MISSING"
    ]
    assert "_quarto.yml" in report["distillation_findings"][0]["reason"]


def test_distillation_accepts_a_perennial_citation(
    tree: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    name = "2026-09-29-audit-exemple.md"
    _write_report(tree, name, f"# Audit\n{HEADER}\n\ntexte\n")
    monkeypatch.setattr(
        lane,
        "_git_citations",
        lambda root, needles: {name: {".claude/rules/une-regle.md"}},
    )

    report = lane.run(root=tree, distillation=True)

    assert report["distillation"]["distilled"] == 1
    assert report["distillation"]["index_only"] == []
    assert report["distillation_findings"] == []


def test_distillation_matches_the_undated_name_a_perennial_still_cites(
    tree: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """Control against the false negative this organ itself hit.

    ``variation-genre-census.md`` was written in the perennial tree, then moved
    into the lane as ``2026-08-10-variation-genre-census.md``. The perennial
    that cites it still carries the old name -- matching only the dated
    basename reports it undistilled, which is false (measured on
    ``scripts/variation_light_cap.py``).
    """
    name = "2026-08-10-variation-genre-census.md"
    _write_report(tree, name, f"# Census\n{HEADER}\n\ntexte\n")
    monkeypatch.setattr(
        lane,
        "_git_citations",
        lambda root, needles: {
            name: set(),
            "variation-genre-census": {"scripts/variation_light_cap.py"},
        },
    )

    report = lane.run(root=tree, distillation=True)

    assert report["distillation"]["distilled"] == 1, report["distillation"]
    assert report["distillation"]["index_only"] == []


def test_distillation_is_off_by_default(
    tree: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """The historical two-direction contract must not pay for the new sense."""
    name = "2026-09-29-audit-exemple.md"
    _write_report(tree, name, f"# Audit\n{HEADER}\n\ntexte\n")
    called: list[set[str]] = []
    monkeypatch.setattr(
        lane, "_git_citations", lambda root, needles: called.append(needles) or {}
    )

    report = lane.run(root=tree)

    assert called == []
    assert report["distillation"] is None
    assert report["distillation_findings"] == []


def test_strict_distillation_turns_the_measurement_into_a_finding(
    tree: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    name = "2026-09-29-audit-exemple.md"
    _write_report(tree, name, f"# Audit\n{HEADER}\n\ntexte\n")
    monkeypatch.setattr(
        lane, "_git_citations", lambda root, needles: {name: {"_quarto.yml"}}
    )

    report = lane.run(root=tree, strict_distillation=True)

    assert report["verdict"] == "VIOLATION"
    assert _reasons(report) == ["DISTILLATION_MISSING"]


def test_cli_strict_distillation_exits_one(
    tree: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    name = "2026-09-29-audit-exemple.md"
    _write_report(tree, name, f"# Audit\n{HEADER}\n\ntexte\n")
    monkeypatch.setattr(
        lane, "_git_citations", lambda root, needles: {name: {"docs/README.md"}}
    )

    assert lane.main(["--root", str(tree), "--strict-distillation"]) == 1
    assert lane.main(["--root", str(tree), "--distillation"]) == 0


def test_unmeasurable_distillation_is_not_a_pass(
    tree: Path, monkeypatch: pytest.MonkeyPatch
) -> None:
    """git unreachable: the sense was not run, which is never an acquittal."""
    name = "2026-09-29-audit-exemple.md"
    _write_report(tree, name, f"# Audit\n{HEADER}\n\ntexte\n")
    monkeypatch.setattr(lane, "_git_citations", lambda root, needles: None)

    report = lane.run(root=tree, distillation=True)

    assert report["distillation"]["measured"] is False
    assert [f["reason"].split(":")[0] for f in report["distillation_findings"]] == [
        "DISTILLATION_UNMEASURABLE"
    ]
    assert report["verdict"] == "CONFORME"  # advisory
    assert lane.main(["--root", str(tree), "--strict-distillation"]) == 1


def test_git_citations_reads_the_real_repository() -> None:
    """Positive control on the real instrument, not on a stub.

    Every other test monkeypatches ``_git_citations``; without this one the
    suite would still pass if the git wiring were broken (the blind spot of
    testing a detector only through its own substitution).
    """
    root = Path(__file__).resolve().parents[2]
    citations = lane._git_citations(root, {"check_docs_transients_lane"})

    assert citations is not None, "git must be able to answer inside the repo"
    hits = citations["check_docs_transients_lane"]
    assert any(hit.endswith("check_docs_transients_lane.py") for hit in hits), hits
    assert all(not hit.startswith("docs/transients/") for hit in hits)
    assert all(not hit.startswith("docs/archive/") for hit in hits)