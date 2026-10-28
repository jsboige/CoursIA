"""Tests de l'organe des versions de bibliotheques (#23073).

L'organe repond a une question simple : « quelle version de bibliotheque
charge un carnet, et est-elle celle que la serie de reference a fixee ? ».
Trois classes de defaut justifient l'organe :

1. **Retrogradation** -- une PR abaisse un epinglage (le carnet passe de
   IKVM 8.15.0 a 8.14.0) ;
2. **Divergence historique** -- l'epinglage etait deja la, la PR n'y touche
   pas : ce n'est pas une regression introduite, c'est une derive a
   traiter par la convergence ;
3. **Provisionnement etranger** -- le carnet telecharge depuis une source
   hors de l'organe de serie (le cas #23047 : `tweetyproject.org/builds/1.28/`
   repond 404 et l'organe de serie telecharge depuis Maven Central).

Les tests ci-dessous pinnent les trois, plus les invariants du manifeste
(la version d'un organe de serie n'est jamais recopie) et le contrat de
l'allowlist (une entree sans motif ecrit est refusee).
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[3]
TOOLS_DIR = REPO_ROOT / "scripts" / "notebook_tools"
sys.path.insert(0, str(TOOLS_DIR))

import check_lib_versions as clv  # noqa: E402

MANIFEST_PATH = TOOLS_DIR / "lib_versions_manifest.json"


# --------------------------------------------------------------------------
# Helpers
# --------------------------------------------------------------------------
def _notebook(cells: list[str]) -> dict:
    """Construit un carnet minimal (cellules code)."""
    return {
        "cells": [
            {"cell_type": "code", "source": [text], "metadata": {}, "outputs": []}
            for text in cells
        ],
        "metadata": {},
        "nbformat": 4,
        "nbformat_minor": 5,
    }


def _write_notebook(tmp_path: Path, name: str, cells: list[str]) -> Path:
    path = tmp_path / name
    path.write_text(json.dumps(_notebook(cells)), encoding="utf-8")
    return path


def _manifest_with(tmp_path: Path, libraries: list[dict], allowlist: list[dict] | None = None):
    path = tmp_path / "manifest.json"
    path.write_text(
        json.dumps({"schema_version": 1, "libraries": libraries, "allowlist": allowlist or []}),
        encoding="utf-8",
    )
    return clv.load_manifest(path)


# --------------------------------------------------------------------------
# Comparaison de versions
# --------------------------------------------------------------------------
def test_version_comparison_is_numeric_not_lexicographic():
    assert clv.compare_versions("8.14.0", "8.15.0") < 0
    assert clv.compare_versions("9.11.4210", "9.15.6755") < 0
    assert clv.compare_versions("3.1.0", "3.0.5") > 0
    assert clv.compare_versions("8.15.0", "8.15.0") == 0


def test_version_comparison_handles_non_numeric_segment():
    assert clv.compare_versions("1.0.0-preview", "1.0.0") < 0
    # Comparaison segment par segment, comme NuGet : 4 < 23, donc 0.4.x est
    # inferieur a 0.23.0 (les versions 0.x ne se comparent pas comme des
    # decimaux).
    assert clv.compare_versions("0.4.2504.701", "0.23.0") < 0
    assert clv.compare_versions("0.23.0", "0.22.3") > 0


# --------------------------------------------------------------------------
# Manifeste
# --------------------------------------------------------------------------
def test_manifest_points_to_the_series_organ_without_copying_its_value():
    """Le manifeste NE recopie pas la version d'un organe de serie."""
    raw = json.loads(MANIFEST_PATH.read_text(encoding="utf-8"))
    tweety = next(e for e in raw["libraries"] if e["id"] == "Tweety")
    assert tweety["canonical_source"] == "organ"
    assert "canonical" not in tweety
    assert tweety["organ_symbol"] == "TWEETY_VERSION"

    manifest = clv.load_manifest(MANIFEST_PATH)
    canonical, error = manifest.libraries["Tweety"].resolve_canonical(REPO_ROOT)
    assert error is None
    assert canonical == "1.30"


def test_manifest_covers_the_libraries_required_by_the_issue():
    manifest = clv.load_manifest(MANIFEST_PATH)
    required = {
        "Tweety",
        "IKVM",
        "IKVM.Image",
        "pythonnet",
        "Google.OrTools",
        "dotNetRDF",
        "Microsoft.ML",
        "SkiaSharp",
    }
    assert required <= set(manifest.libraries)


def test_every_declared_divergence_carries_a_written_reason():
    raw = json.loads(MANIFEST_PATH.read_text(encoding="utf-8"))
    for entry in raw["libraries"]:
        for divergence in entry.get("divergences", []):
            assert divergence.get("decision") in {"to_converge", "justified"}
            assert divergence.get("reason", "").strip(), (
                f"{entry['id']} {divergence.get('version')} : motif manquant"
            )


def test_allowlist_entry_without_a_reason_is_refused():
    """Une allowlist sans motif ecrit n'est pas une justification."""
    raw = json.loads(MANIFEST_PATH.read_text(encoding="utf-8"))
    allowlist = raw.get("allowlist", [])
    for entry in allowlist:
        assert entry.get("reason", "").strip(), "une entree d'allowlist porte un motif"


# --------------------------------------------------------------------------
# Collecte des epinglages
# --------------------------------------------------------------------------
def test_nuget_pin_is_collected_with_or_without_space():
    manifest = clv.load_manifest(MANIFEST_PATH)
    payload = _notebook(['#r "nuget:IKVM,8.14.0"', '#r "nuget: pythonnet, 3.1.0"'])
    pins = clv.pins_from_payload(payload, manifest)
    found = {(p.library, p.version) for p in pins}
    assert ("IKVM", "8.14.0") in found
    assert ("pythonnet", "3.1.0") in found


def test_unknown_package_is_not_a_pin():
    manifest = clv.load_manifest(MANIFEST_PATH)
    payload = _notebook(['#r "nuget: ClosedXML, 0.102.3"'])
    assert clv.pins_from_payload(payload, manifest) == []


def test_local_redeclaration_of_the_series_symbol_is_collected():
    """Un carnet qui reecrit TWEETY_VERSION porte un epinglage a part entiere."""
    manifest = clv.load_manifest(MANIFEST_PATH)
    payload = _notebook(['TWEETY_VERSION = "1.28"', 'BASE = "https://x/"'])
    pins = clv.pins_from_payload(payload, manifest)
    local = [p for p in pins if p.ecosystem == "local_const"]
    assert len(local) == 1
    assert local[0].version == "1.28"


# --------------------------------------------------------------------------
# Controles positifs et negatifs (criteres d'acceptation de #23073)
# --------------------------------------------------------------------------
def test_positive_control_tweety_archive_is_red():
    """Le carnet archive de #23047 porte 1.28 et un chemin de provisionnement mort."""
    manifest = clv.load_manifest(MANIFEST_PATH)
    canonicals, errors = clv.resolve_canonicals(manifest, REPO_ROOT)
    assert not errors
    notebook = REPO_ROOT / "MyIA.AI.Notebooks" / "SymbolicAI" / "_archive" / "Tweety.ipynb"
    assert notebook.is_file(), "le carnet archive doit exister dans le depot"
    pins = clv.pins_from_file(notebook, manifest)
    findings = clv.state_findings(notebook.as_posix(), pins, manifest, canonicals)
    kinds = {f["kind"] for f in findings}
    assert "foreign_provisioning" in kinds
    assert "downgrade" in kinds
    versions = {f["version"] for f in findings if f["kind"] == "downgrade"}
    assert "1.28" in versions


def test_positive_control_ikvm_814_is_red():
    """Un carnet en IKVM 8.14.0 s'ecarte de la canonique 8.15.0."""
    manifest = clv.load_manifest(MANIFEST_PATH)
    canonicals, _errors = clv.resolve_canonicals(manifest, REPO_ROOT)
    payload = _notebook(['#r "nuget:IKVM,8.14.0"'])
    findings = clv.state_findings("x.ipynb", clv.pins_from_payload(payload, manifest), manifest, canonicals)
    assert any(f["kind"] == "downgrade" and f["version"] == "8.14.0" for f in findings)


def test_negative_control_aligned_notebook_is_green():
    manifest = clv.load_manifest(MANIFEST_PATH)
    canonicals, _errors = clv.resolve_canonicals(manifest, REPO_ROOT)
    payload = _notebook(['#r "nuget:IKVM,8.15.0"', '#r "nuget:IKVM.Image,8.15.0"'])
    findings = clv.state_findings("x.ipynb", clv.pins_from_payload(payload, manifest), manifest, canonicals)
    assert findings == []


# --------------------------------------------------------------------------
# Semantique du delta base -> tete
# --------------------------------------------------------------------------
def test_delta_ignores_a_legacy_pin_the_pr_does_not_touch():
    """Une derive historique ne rougit pas une PR qui ne touche pas l'epinglage."""
    manifest = clv.load_manifest(MANIFEST_PATH)
    canonicals, _errors = clv.resolve_canonicals(manifest, REPO_ROOT)
    legacy = clv.pins_from_payload(_notebook(['#r "nuget:IKVM,8.14.0"']), manifest)
    head = clv.pins_from_payload(
        _notebook(['#r "nuget:IKVM,8.14.0"', 'print("contenu sans rapport")']), manifest
    )
    assert clv.delta_findings("x.ipynb", legacy, head, manifest, canonicals) == []


def test_delta_flags_a_downgrade_introduced_by_the_pr():
    manifest = clv.load_manifest(MANIFEST_PATH)
    canonicals, _errors = clv.resolve_canonicals(manifest, REPO_ROOT)
    base = clv.pins_from_payload(_notebook(['#r "nuget:IKVM,8.15.0"']), manifest)
    head = clv.pins_from_payload(_notebook(['#r "nuget:IKVM,8.14.0"']), manifest)
    findings = clv.delta_findings("x.ipynb", base, head, manifest, canonicals)
    assert any(f["kind"] == "downgrade" and f["version"] == "8.14.0" for f in findings)


def test_delta_flags_a_new_notebook_carrying_a_divergent_pin():
    """Un carnet ajoute par la PR n'a pas de base : tous ses epinglages sont nouveaux."""
    manifest = clv.load_manifest(MANIFEST_PATH)
    canonicals, _errors = clv.resolve_canonicals(manifest, REPO_ROOT)
    head = clv.pins_from_payload(_notebook(['#r "nuget:IKVM,8.14.0"']), manifest)
    findings = clv.delta_findings("x.ipynb", [], head, manifest, canonicals)
    assert any(f["kind"] == "downgrade" for f in findings)


def test_delta_stays_green_when_the_pr_aligns_a_legacy_pin():
    """La convergence d'un carnet legacy vers la canonique ne doit pas rougir."""
    manifest = clv.load_manifest(MANIFEST_PATH)
    canonicals, _errors = clv.resolve_canonicals(manifest, REPO_ROOT)
    base = clv.pins_from_payload(_notebook(['#r "nuget:IKVM,8.14.0"']), manifest)
    head = clv.pins_from_payload(_notebook(['#r "nuget:IKVM,8.15.0"']), manifest)
    assert clv.delta_findings("x.ipynb", base, head, manifest, canonicals) == []


def test_foreign_provisioning_is_reported_even_when_the_pr_does_not_touch_it():
    """Le provisionnement etranger pese a l'execution : il est signale sur l'etat."""
    manifest = clv.load_manifest(MANIFEST_PATH)
    canonicals, _errors = clv.resolve_canonicals(manifest, REPO_ROOT)
    cells = ['BASE = "https://tweetyproject.org/builds/1.28/"']
    base = clv.pins_from_payload(_notebook(cells), manifest)
    head = clv.pins_from_payload(_notebook(cells + ['print("x")']), manifest)
    findings = clv.delta_findings("x.ipynb", base, head, manifest, canonicals)
    assert any(f["kind"] == "foreign_provisioning" for f in findings)


# --------------------------------------------------------------------------
# Allowlist
# --------------------------------------------------------------------------
def test_allowlist_suppresses_the_finding_for_the_named_notebook(tmp_path):
    libraries = [
        {
            "id": "IKVM",
            "ecosystem": "nuget",
            "canonical": "8.15.0",
            "canonical_source": "manifest",
        }
    ]
    allowlist = [
        {
            "library": "IKVM",
            "version": "8.14.0",
            "notebooks": ["serie/legacy.ipynb"],
            "reason": "Le carnet teste volontairement l'API 8.14 (cf issue #1234).",
        }
    ]
    manifest = _manifest_with(tmp_path, libraries, allowlist)
    canonicals, _errors = clv.resolve_canonicals(manifest, tmp_path)
    pins = clv.pins_from_payload(_notebook(['#r "nuget:IKVM,8.14.0"']), manifest)
    assert clv.state_findings("serie/legacy.ipynb", pins, manifest, canonicals) == []
    assert clv.state_findings("serie/autre.ipynb", pins, manifest, canonicals) != []


# --------------------------------------------------------------------------
# Recensement
# --------------------------------------------------------------------------
def test_census_returns_rc_zero_and_reports_the_dispersion():
    manifest = clv.load_manifest(MANIFEST_PATH)
    report = clv.run_census(REPO_ROOT, manifest)
    assert report["mode"] == "census"
    assert not report["errors"]
    by_library = {lib["library"]: lib for lib in report["libraries"]}
    ikvm = by_library["IKVM"]
    assert ikvm["multiple_versions"] is True
    versions = {row["version"]: row for row in ikvm["versions"]}
    assert "8.14.0" in versions and "8.15.0" in versions
    assert versions["8.14.0"]["decision"] == "to_converge"
    assert versions["8.15.0"]["decision"] == "canonique"
    # le classement porte un motif ecrit
    assert versions["8.14.0"]["reason"].strip()


def test_census_cli_exits_zero():
    assert clv.main(["--census", "--repo-root", str(REPO_ROOT)]) == 0


# --------------------------------------------------------------------------
# Cablage dans la voie rapide
# --------------------------------------------------------------------------
def _registry():
    sys.path.insert(0, str(REPO_ROOT / "scripts" / "ci"))
    import fast_lane_registry as registry

    return registry


def test_guard_is_registered_as_advisory():
    """Le garde est enregistre, en advisory, et son nom porte la mention."""
    registry = _registry()
    guards = {g.name: g for g in registry.TRANCHE29}
    guard = guards["Library versions guard (advisory, #23073)"]
    assert guard.blocking is False
    assert guard.needs_base is True
    assert "advisory" in guard.name.lower()
    assert "scripts/notebook_tools/check_lib_versions.py" in " ".join(guard.argv)


def test_guard_is_aggregated_by_the_fast_lane_engine():
    """Un groupe non cable n'est jamais execute : le geste doit etre dans l'engine."""
    engine = (REPO_ROOT / "scripts" / "ci" / "fast_lane.py").read_text(encoding="utf-8")
    assert "TRANCHE29" in engine, "le groupe TRANCHE29 n'est pas cable dans fast_lane.py"
