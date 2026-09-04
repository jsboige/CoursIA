"""Tests for compare_lake_manifests (EPIC #4362 step-1 scanner)."""
from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import compare_lake_manifests as clm  # noqa: E402


def write_lake(root: Path, name: str, packages: list[dict], toolchain: str = "leanprover/lean4:v4.32.1") -> Path:
    lake_dir = root / name
    lake_dir.mkdir(parents=True)
    (lake_dir / "lake-manifest.json").write_text(
        json.dumps({"version": "1.2.0", "packages": packages}), encoding="utf-8"
    )
    if toolchain:
        (lake_dir / "lean-toolchain").write_text(toolchain, encoding="utf-8")
    return lake_dir


def git_pkg(name: str, rev: str) -> dict:
    return {"name": name, "type": "git", "rev": rev, "url": f"https://example.com/{name}.git"}


CORE = [git_pkg("mathlib", "aa11"), git_pkg("batteries", "bb22")]


def test_identical_manifests_form_one_cluster(tmp_path):
    write_lake(tmp_path, "alpha", CORE)
    write_lake(tmp_path, "beta", CORE)

    lakes, skipped = clm.discover_manifests(tmp_path, {})
    report = clm.build_report(lakes, skipped)

    assert len(report["identity_clusters"]) == 1
    assert sorted(report["identity_clusters"][list(report["identity_clusters"])[0]]["lakes"]) == ["alpha", "beta"]
    assert report["divergent_vs_reference"] == []


def test_divergent_rev_is_reported_with_package(tmp_path):
    write_lake(tmp_path, "alpha", CORE)
    write_lake(tmp_path, "beta", [git_pkg("mathlib", "aa11"), git_pkg("batteries", "OTHER")])

    lakes, skipped = clm.discover_manifests(tmp_path, {})
    report = clm.build_report(lakes, skipped)

    assert len(report["divergent_vs_reference"]) == 1
    div = report["divergent_vs_reference"][0]
    assert div["lake"] == "beta"
    assert div["diffs_vs_reference"] == [
        {"package": "batteries", "reference": "bb22", "lake": "OTHER"}
    ]


def test_extra_own_package_is_a_divergence_not_a_conflict(tmp_path):
    """social_choice_lean_peters / mimo_lean shape: core pins identical, one
    additional own dependency. The scanner must report the addition -- shared
    revs stay provably identical. The core cluster has the plurality (as in
    the real parc: 20 core lakes vs 1 lake with an own dep)."""
    write_lake(tmp_path, "core_lake", CORE)
    write_lake(tmp_path, "core_lake_2", CORE)
    write_lake(tmp_path, "plus_own", CORE + [git_pkg("own_dep", "cc33")])

    lakes, _ = clm.discover_manifests(tmp_path, {})
    report = clm.build_report(lakes, [])

    div = {d["lake"]: d for d in report["divergent_vs_reference"]}
    assert div["plus_own"]["diffs_vs_reference"] == [
        {"package": "own_dep", "reference": None, "lake": "cc33"}
    ]


def test_documented_exclusions_are_skipped_with_reason(tmp_path):
    write_lake(tmp_path, "conway_cgt_lean", CORE)
    write_lake(tmp_path, "normal_lake", CORE)

    lakes, skipped = clm.discover_manifests(tmp_path, clm.DEFAULT_EXCLUDES)

    assert [l.path.name for l in lakes] == ["normal_lake"]
    assert skipped == [
        (Path("conway_cgt_lean") / "lake-manifest.json", clm.DEFAULT_EXCLUDES["conway_cgt_lean"])
    ]


def test_empty_pin_tree_is_not_divergent(tmp_path):
    write_lake(tmp_path, "with_deps", CORE)
    write_lake(tmp_path, "no_deps", [])

    lakes, _ = clm.discover_manifests(tmp_path, {})
    report = clm.build_report(lakes, [])

    assert report["no_dependency_lakes"] == ["no_deps"]
    assert report["divergent_vs_reference"] == []


def test_lake_inside_dot_lake_packages_is_ignored(tmp_path):
    write_lake(tmp_path, "real", CORE)
    nested = tmp_path / "real" / ".lake" / "packages" / "mathlib"
    nested.mkdir(parents=True)
    (nested / "lake-manifest.json").write_text('{"version": "1.2.0", "packages": []}', encoding="utf-8")

    lakes, _ = clm.discover_manifests(tmp_path, {})

    assert len(lakes) == 1
    assert lakes[0].path.name == "real"


def test_toolchain_is_read(tmp_path):
    write_lake(tmp_path, "alpha", CORE, toolchain="leanprover/lean4:v4.33.1")

    lakes, _ = clm.discover_manifests(tmp_path, {})

    assert lakes[0].toolchain == "leanprover/lean4:v4.33.1"


def test_text_render_mentions_reference_cluster(tmp_path):
    write_lake(tmp_path, "alpha", CORE)

    lakes, _ = clm.discover_manifests(tmp_path, {})
    report = clm.build_report(lakes, [])
    text = clm.render_text(report)

    assert "Identity clusters" in text
    assert "[REFERENCE]" in text
    assert "mathlib=aa11" in text


def test_no_manifests_returns_exit_2(tmp_path, capsys):
    assert clm.main(["--root", str(tmp_path)]) == 2
    assert "no lake-manifest.json found" in capsys.readouterr().err
