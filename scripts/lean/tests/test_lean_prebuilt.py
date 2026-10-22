"""Tests for scripts/lean/lean_prebuilt.py — etat pre-build d'un lake Lean.

Couvre le contrat de la tranche 1 de #21410 (voie 2) :
- ``compute_fingerprint`` : determinisme, sensibilite aux sources / au
  manifeste / a la toolchain, insensibilite a `.lake/` ;
- ``stamp_project`` / ``project_status`` : ABSENT / UNSTAMPED / PREBUILT /
  STALE, et le refus de marquer du vide ;
- ``resolve_prebuilt`` : un clone equivalent et PREBUILT est trouve, un clone
  aux sources differentes est rejete, l'egalite d'empreinte est la seule
  condition ;
- CLI : codes de sortie 0/1 utilisables comme garde.

Arbres synthetiques sous ``tmp_path`` — aucun build reel, aucun reseau.
"""

import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import lean_prebuilt as lp  # noqa: E402


# ---------------------------------------------------------------------------
# helpers
# ---------------------------------------------------------------------------

def _write(path: Path, text: str = "") -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _make_lake(root: Path, name: str = "conway_lean",
               toolchain: str = "leanprover/lean4:v4.33.0",
               sources: dict | None = None) -> Path:
    lake = root / name
    _write(lake / "lean-toolchain", toolchain + "\n")
    _write(lake / "lakefile.lean", "import Lake\nopen Lake DSL\npackage conway\n")
    _write(lake / "lake-manifest.json", '{"version": "1.1.0", "packages": []}\n')
    for rel, text in (sources or {"Conway/A.lean": "theorem a : True := trivial\n"}).items():
        _write(lake / rel, text)
    return lake


def _mark_built(lake: Path) -> None:
    # Layout canonique de Lake : `.lake/build/lib/<Module>.olean` (points du
    # module en slashs) — le temoin d'artefact de `stamp --module` le recoupe.
    _write(lake / ".lake" / "build" / "lib" / "Conway" / "A.olean", "olean")


# ---------------------------------------------------------------------------
# empreinte
# ---------------------------------------------------------------------------

def test_fingerprint_is_deterministic(tmp_path: Path) -> None:
    lake = _make_lake(tmp_path)
    first = lp.compute_fingerprint(lake)
    second = lp.compute_fingerprint(lake)
    assert first["fingerprint"] == second["fingerprint"]
    assert first["sources"] == 1
    assert first["toolchain"].startswith("leanprover/lean4:")


def test_fingerprint_changes_on_source_edit(tmp_path: Path) -> None:
    lake = _make_lake(tmp_path)
    before = lp.compute_fingerprint(lake)["fingerprint"]
    _write(lake / "Conway" / "A.lean", "theorem a : True := by trivial\n")
    assert lp.compute_fingerprint(lake)["fingerprint"] != before


def test_fingerprint_changes_on_toolchain_edit(tmp_path: Path) -> None:
    lake = _make_lake(tmp_path)
    before = lp.compute_fingerprint(lake)["fingerprint"]
    _write(lake / "lean-toolchain", "leanprover/lean4:v4.34.0\n")
    assert lp.compute_fingerprint(lake)["fingerprint"] != before


def test_fingerprint_changes_on_manifest_edit(tmp_path: Path) -> None:
    lake = _make_lake(tmp_path)
    before = lp.compute_fingerprint(lake)["fingerprint"]
    _write(lake / "lake-manifest.json", '{"version": "1.1.0", "packages": [{"name": "mathlib"}]}\n')
    assert lp.compute_fingerprint(lake)["fingerprint"] != before


def test_fingerprint_ignores_lake_directory(tmp_path: Path) -> None:
    lake = _make_lake(tmp_path)
    before = lp.compute_fingerprint(lake)["fingerprint"]
    _write(lake / ".lake" / "packages" / "mathlib" / "Mathlib.lean", "-- autre contenu\n")
    assert lp.compute_fingerprint(lake)["fingerprint"] == before


def test_fingerprint_includes_nested_sources(tmp_path: Path) -> None:
    lake = _make_lake(tmp_path)
    before = lp.compute_fingerprint(lake)["fingerprint"]
    _write(lake / "Conway" / "Sub" / "B.lean", "theorem b : True := trivial\n")
    after = lp.compute_fingerprint(lake)
    assert after["fingerprint"] != before
    assert after["sources"] == 2


def test_fingerprint_rejects_missing_project(tmp_path: Path) -> None:
    try:
        lp.compute_fingerprint(tmp_path / "absent")
    except FileNotFoundError:
        return
    raise AssertionError("FileNotFoundError attendu")


# ---------------------------------------------------------------------------
# stamp / status
# ---------------------------------------------------------------------------

def test_status_absent_without_build(tmp_path: Path) -> None:
    lake = _make_lake(tmp_path)
    assert lp.project_status(lake)["status"] == lp.STATUS_ABSENT


def test_status_unstamped_with_build_but_no_stamp(tmp_path: Path) -> None:
    lake = _make_lake(tmp_path)
    _mark_built(lake)
    assert lp.project_status(lake)["status"] == lp.STATUS_UNSTAMPED


def test_stamp_roundtrip_gives_prebuilt(tmp_path: Path) -> None:
    lake = _make_lake(tmp_path)
    _mark_built(lake)
    stamped = lp.stamp_project(lake, module="Conway")
    assert stamped["status"] == lp.STATUS_PREBUILT
    assert stamped["stamp"]["module"] == "Conway"
    verdict = lp.project_status(lake)
    assert verdict["status"] == lp.STATUS_PREBUILT
    assert verdict["module"] == "Conway"


def test_stamp_records_artifact_witness(tmp_path: Path) -> None:
    """Le stamp est une declaration : le temoin dit ce que l'arbre contenait."""
    lake = _make_lake(tmp_path)
    _mark_built(lake)
    stamped = lp.stamp_project(lake, module="Conway.A")
    art = stamped["stamp"]["artifact"]
    assert art["present"] is True
    assert art["olean"] == "Conway/A.olean"
    assert len(art["sha256"]) == 64
    verdict = lp.project_status(lake)
    assert verdict["artifact"]["state"] == "MATCH"

    # Build interrompu : d'autres artefacts existent, le module vise manque —
    # le verdict reste PREBUILT (sources intactes) mais le temoin le DIT.
    _write(lake / ".lake" / "build" / "lib" / "Conway" / "B.olean", "x")
    (lake / ".lake" / "build" / "lib" / "Conway" / "A.olean").unlink()
    verdict = lp.project_status(lake)
    assert verdict["status"] == lp.STATUS_PREBUILT
    assert verdict["artifact"]["state"] == "MISSING"


def test_stamp_without_module_has_no_witness(tmp_path: Path) -> None:
    lake = _make_lake(tmp_path)
    _mark_built(lake)
    stamped = lp.stamp_project(lake)
    assert "artifact" not in stamped["stamp"]


def test_status_stale_after_source_edit(tmp_path: Path) -> None:
    lake = _make_lake(tmp_path)
    _mark_built(lake)
    lp.stamp_project(lake)
    _write(lake / "Conway" / "A.lean", "theorem a : True := by trivial\n")
    verdict = lp.project_status(lake)
    assert verdict["status"] == lp.STATUS_STALE
    assert verdict["stamp_fingerprint"] != verdict["fingerprint"]


def test_stamp_refuses_empty_build(tmp_path: Path) -> None:
    lake = _make_lake(tmp_path)
    try:
        lp.stamp_project(lake)
    except ValueError as exc:
        assert "aucun build" in str(exc)
        return
    raise AssertionError("ValueError attendu")


def test_build_present_ignores_empty_build_dir(tmp_path: Path) -> None:
    lake = _make_lake(tmp_path)
    (lake / ".lake" / "build").mkdir(parents=True)
    assert lp.build_present(lake) is False


def test_corrupt_stamp_reads_as_unstamped(tmp_path: Path) -> None:
    lake = _make_lake(tmp_path)
    _mark_built(lake)
    _write(lake / ".lake" / lp.STAMP_NAME, "{not json")
    assert lp.project_status(lake)["status"] == lp.STATUS_UNSTAMPED


# ---------------------------------------------------------------------------
# resolution
# ---------------------------------------------------------------------------

def test_resolve_finds_equivalent_prebuilt_clone(tmp_path: Path) -> None:
    worktree = _make_lake(tmp_path / "worktree")
    clone = _make_lake(tmp_path / "clone")
    _mark_built(clone)
    lp.stamp_project(clone, module="Conway")

    payload = lp.resolve_prebuilt(worktree, [tmp_path])
    assert payload["status"] == lp.STATUS_PREBUILT
    assert Path(payload["path"]) == clone.resolve()
    # La marque du checkout resolu remonte dans le verdict de resolve — sans
    # elle, l'affichage humain imprime une ligne `marque` vide (reserve 3).
    assert payload["module"] == "Conway"
    assert payload["stamped_at"]
    statuses = {str(Path(item["path"])): item["status"] for item in payload["checked"]}
    assert statuses[str(worktree.resolve())] == lp.STATUS_ABSENT


def test_resolve_rejects_clone_with_different_sources(tmp_path: Path) -> None:
    worktree = _make_lake(tmp_path / "worktree")
    clone = _make_lake(tmp_path / "clone")
    _mark_built(clone)
    lp.stamp_project(clone)
    _write(clone / "Conway" / "A.lean", "theorem a : True := by trivial\n")

    payload = lp.resolve_prebuilt(worktree, [tmp_path])
    assert payload["status"] == lp.STATUS_ABSENT
    reasons = {item["path"]: item["status"] for item in payload["checked"]}
    assert reasons[str(clone.resolve())] == "FINGERPRINT_MISMATCH"


def test_resolve_ignores_other_lake_names(tmp_path: Path) -> None:
    worktree = _make_lake(tmp_path / "worktree")
    other = _make_lake(tmp_path / "other", name="grothendieck_lean")
    _mark_built(other)
    lp.stamp_project(other)

    payload = lp.resolve_prebuilt(worktree, [tmp_path])
    assert payload["status"] == lp.STATUS_ABSENT
    # Ecarte par nom, mais CONSIGNE : un resolve en echec doit montrer ce
    # qu'il n'a pas regarde (reserve 2 de la revue Hermes).
    statuses = {item["path"]: item["status"] for item in payload["checked"]}
    assert statuses[str(other.resolve())] == "NAME_MISMATCH"


def test_resolve_prefers_requested_when_prebuilt(tmp_path: Path) -> None:
    lake = _make_lake(tmp_path)
    _mark_built(lake)
    lp.stamp_project(lake)

    payload = lp.resolve_prebuilt(lake, [])
    assert payload["status"] == lp.STATUS_PREBUILT
    assert Path(payload["path"]) == lake.resolve()


# ---------------------------------------------------------------------------
# CLI — codes de sortie utilisables comme garde
# ---------------------------------------------------------------------------

def test_cli_status_exit_codes(tmp_path: Path, capsys) -> None:
    lake = _make_lake(tmp_path)
    assert lp.main(["status", "--project", str(lake), "--json"]) == 1
    capsys.readouterr()  # drainer la sortie du premier appel
    _mark_built(lake)
    lp.stamp_project(lake)
    assert lp.main(["status", "--project", str(lake), "--json"]) == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["status"] == lp.STATUS_PREBUILT


def test_cli_stamp_refusal_exit_1(tmp_path: Path) -> None:
    lake = _make_lake(tmp_path)
    assert lp.main(["stamp", "--project", str(lake)]) == 1


def test_cli_resolve_exit_codes(tmp_path: Path) -> None:
    worktree = _make_lake(tmp_path / "worktree")
    clone = _make_lake(tmp_path / "clone")
    assert lp.main(["resolve", "--project", str(worktree),
                    "--search", str(tmp_path), "--json"]) == 1
    _mark_built(clone)
    lp.stamp_project(clone)
    assert lp.main(["resolve", "--project", str(worktree),
                    "--search", str(tmp_path), "--json"]) == 0


def test_cli_fingerprint_human_output(tmp_path: Path, capsys) -> None:
    lake = _make_lake(tmp_path)
    assert lp.main(["fingerprint", "--project", str(lake)]) == 0
    out = capsys.readouterr().out
    assert "empreinte" in out
    assert "1 sources Lean" in out