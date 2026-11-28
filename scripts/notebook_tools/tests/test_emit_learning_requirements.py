"""Tests de l'organe d'emission des paquets de l'image d'apprentissage (#27545).

Le contrat verifie ici : le manifeste consolide du pli 1.1 est la source
unique, la resolution vient du manifeste (pas de l'organe), et toute exclusion
porte un motif et une source.
"""
from __future__ import annotations

import importlib.util
import json
import sys
from pathlib import Path

MODULE_PATH = (
    Path(__file__).resolve().parents[1] / "emit_learning_requirements.py"
)
SPEC = importlib.util.spec_from_file_location("emit_learning_requirements", MODULE_PATH)
assert SPEC and SPEC.loader
emitter = importlib.util.module_from_spec(SPEC)
sys.modules["emit_learning_requirements"] = emitter
SPEC.loader.exec_module(emitter)


def _manifest(packages: list[dict], conflicts: list[dict] | None = None) -> dict:
    return {
        "schema_version": 1,
        "consolidated_manifest": packages,
        "conflicts": conflicts or [],
    }


def test_merge_specs_keeps_the_strictest_bounds() -> None:
    assert emitter.merge_specs([">=2.0.0", ">=2.0"]) == ">=2.0.0"
    assert emitter.merge_specs(["<2.0", "<=1.9"]) == "<=1.9"
    assert emitter.merge_specs([">=1.0", "<2.0"]) == ">=1.0,<2.0"


def test_merge_specs_exact_pin_wins_over_a_range() -> None:
    assert emitter.merge_specs([">=1.0,<2.0", "==1.5.0"]) == "==1.5.0"


def test_merge_specs_keeps_an_opaque_form_instead_of_dropping_it() -> None:
    # Une forme non comprise est conservee : une absence de mesure n'est pas
    # une autorisation de la jetter.
    assert emitter.merge_specs([">=1.0", "~=2.1"]) == ">=1.0,~=2.1"


def test_resolve_package_uses_the_manifest_resolution() -> None:
    entry = {"package": "accelerate", "specs": [">=0.25.0"], "version": ""}
    conflict = {
        "package": "accelerate",
        "resolution": {"policy": "intersection", "version": ">=1.0.0"},
    }
    spec, origin = emitter.resolve_package(entry, conflict)
    assert spec == ">=1.0.0"
    assert origin == "manifeste:resolution"


def test_resolve_package_marks_an_unsatisfiable_package_as_dropped() -> None:
    entry = {"package": "torch", "specs": [], "version": ""}
    conflict = {
        "package": "torch",
        "resolution": {"policy": "aucune version commune", "version": ""},
    }
    spec, origin = emitter.resolve_package(entry, conflict)
    assert spec == ""
    assert origin == "manifeste:ecarte"


def test_plan_drops_an_excluded_package_with_its_motif_and_source() -> None:
    manifest = _manifest(
        [
            {"package": "numpy", "specs": [">=1.24,<2.0"], "version": ""},
            {"package": "pyphi", "specs": ["==1.2.0"], "version": "1.2.0"},
        ]
    )
    policy = {
        "target": {"interpreter": "python3", "version": "3.11"},
        "exclude": [
            {
                "package": "pyphi",
                "motif": "requires-python <3.10",
                "source": "docs/reference/kernels-runtime.md",
            }
        ],
    }
    plan = emitter.build_plan(manifest, policy)
    assert [item["package"] for item in plan["installs"]] == ["numpy"]
    assert plan["dropped"] == [
        {
            "package": "pyphi",
            "motif": "requires-python <3.10",
            "source": "docs/reference/kernels-runtime.md",
        }
    ]


def test_plan_separates_the_packages_installed_by_pip() -> None:
    manifest = _manifest(
        [
            {"package": "numpy", "specs": [">=1.24,<2.0"], "version": ""},
            {"package": "python-constraint", "specs": [">=1.4.0"], "version": ""},
        ]
    )
    policy = {
        "target": {"interpreter": "python3", "version": "3.11"},
        "pip_installed": [
            {"package": "python-constraint", "motif": "sdist non PEP 625", "source": "mesure"}
        ],
    }
    plan = emitter.build_plan(manifest, policy)
    installers = {item["package"]: item["installer"] for item in plan["installs"]}
    assert installers == {"numpy": "uv", "python-constraint": "pip"}
    uv_input = emitter.render_uv_input(plan)
    requirement_lines = [
        line for line in uv_input.splitlines() if line and not line.startswith("#")
    ]
    assert "numpy>=1.24,<2.0" in requirement_lines
    assert not any("python-constraint" in line for line in requirement_lines)


def test_render_requirements_keeps_the_manifest_as_the_only_source() -> None:
    manifest = _manifest(
        [
            {"package": "numpy", "specs": [">=1.24,<2.0"], "version": ""},
            {"package": "requests", "specs": [">=2.31"], "version": ""},
        ]
    )
    policy = {"target": {"interpreter": "python3", "version": "3.11"}}
    plan = emitter.build_plan(manifest, policy)
    rendered = emitter.render_requirements(plan, "manifeste-dependances.json")
    assert "numpy>=1.24,<2.0" in rendered
    assert "requests>=2.31" in rendered
    assert "manifeste-dependances.json" in rendered


def test_every_exclusion_carries_a_motif_and_a_source() -> None:
    manifest = _manifest(
        [
            {"package": "torch", "specs": [], "version": ""},
            {"package": "numpy", "specs": [">=1.24,<2.0"], "version": ""},
        ],
        conflicts=[
            {
                "package": "torch",
                "resolution": {"policy": "aucune version commune", "version": ""},
            }
        ],
    )
    policy = {"target": {"interpreter": "python3", "version": "3.11"}}
    plan = emitter.build_plan(manifest, policy)
    assert plan["dropped"], "un paquet ecarte doit etre trace"
    for item in plan["dropped"]:
        assert item["motif"], f"exclusion sans motif : {item['package']}"
        assert item["source"], f"exclusion sans source : {item['package']}"


def test_check_lock_detects_a_stale_lock(tmp_path: Path) -> None:
    manifest_path = tmp_path / "manifeste-dependances.json"
    manifest_path.write_text(json.dumps(_manifest([])), encoding="utf-8")
    lock_path = tmp_path / "requirements-learning.lock.txt"
    lock_path.write_text("# aucune empreinte\n", encoding="utf-8")
    assert emitter.check_lock(lock_path, manifest_path) == 1
    lock_path.write_text(
        f"# manifeste sha256 : {emitter._sha256(manifest_path)}\n", encoding="utf-8"
    )
    assert emitter.check_lock(lock_path, manifest_path) == 0


def test_written_artifact_is_identical_on_every_platform(tmp_path: Path) -> None:
    """L'artefact versionne ne doit pas dependre de la machine qui l'ecrit.

    `Path.write_text` sans `newline` traduit en CRLF sous Windows : le
    fichier versionne, et l'empreinte sha256 que le verrou en porte, alors
    que le contenu etait le meme. L'organe ecrit donc en LF explicite --
    comme le fait l'organe du manifeste (`dependency_manifest_cli.py`).
    """
    manifest_path = tmp_path / "manifeste-dependances.json"
    manifest_path.write_text(
        json.dumps(
            _manifest([{"package": "numpy", "specs": [">=1.24"], "version": ""}])
        ),
        encoding="utf-8",
    )
    policy_path = tmp_path / "learning_image_policy.json"
    policy_path.write_text(
        json.dumps({"target": {"interpreter": "python3", "version": "3.12"}}),
        encoding="utf-8",
    )
    out_path = tmp_path / "requirements-learning.txt"
    assert (
        emitter.main(
            [
                "--manifest",
                str(manifest_path),
                "--policy",
                str(policy_path),
                "--out",
                str(out_path),
                "--write",
            ]
        )
        == 0
    )
    raw = out_path.read_bytes()
    assert b"\r\n" not in raw
    assert raw.endswith(b"\n")
    assert b"numpy>=1.24" in raw

