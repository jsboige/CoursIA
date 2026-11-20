"""Tests du manifeste des dependances par famille de noyau (issue #27544).

Les tests unitaires n'ont besoin ni du depot ni du reseau : ils fabriquent leurs
propres fichiers dans ``tmp_path``. Deux tests d'integration relisent l'arbre
reel, pour les deux criteres d'acceptance qui parlent du depot lui-meme :
aucune serie de carnets absente de la table, et fichiers versionnes a jour.
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

import kernel_dependency_manifest as kdm

REPO_ROOT = Path(__file__).resolve().parents[2]


# ---------------------------------------------------------------------------
# Familles de noyau
# ---------------------------------------------------------------------------


@pytest.mark.parametrize(
    ("name", "expected"),
    [
        ("python3", "python"),
        (".net-csharp", "csharp"),
        ("lean4-wsl", "lean"),
        ("lean4-wsl-perc", "lean"),
        ("leandojo-v2", "lean"),
        ("python3-lean", "python"),
        ("pyphi-iit", "python"),
        ("smartcontracts", "python"),
        ("rust", "rust"),
        ("noyau-inconnu", "other"),
    ],
)
def test_classify_family_from_kernelspec_name(name: str, expected: str) -> None:
    assert kdm.classify_family(name) == expected


def test_classify_family_falls_back_to_language() -> None:
    assert kdm.classify_family(None, "Python") == "python"
    assert kdm.classify_family(None, "C#") == "csharp"
    assert kdm.classify_family(None, "Lean 4") == "lean"
    assert kdm.classify_family(None, None) == "other"


# ---------------------------------------------------------------------------
# Noms de paquets
# ---------------------------------------------------------------------------


@pytest.mark.parametrize(
    ("raw", "expected"),
    [
        ("numpy", "numpy"),
        ("Foo_Bar.Baz", "foo-bar-baz"),
        ("scikit_learn", "scikit-learn"),
        ("  Z3-Solver  ", "z3-solver"),
    ],
)
def test_normalise_name(raw: str, expected: str) -> None:
    assert kdm.normalise_name(raw) == expected


# ---------------------------------------------------------------------------
# Lecture des fichiers de dependances
# ---------------------------------------------------------------------------


def test_parse_requirements_ignores_options_and_follows_include(tmp_path: Path) -> None:
    (tmp_path / "base.txt").write_text("numpy>=1.24\n", encoding="utf-8")
    requirement = tmp_path / "requirements.txt"
    requirement.write_text(
        "# commentaire\n"
        "\n"
        "--index-url https://example.invalid/simple\n"
        "-r base.txt\n"
        "torch==2.14.0  # epingle pour la reproductibilite\n"
        "requests\n"
        "z3-solver>=4.13 ; python_version>'3.9'\n"
        "git+https://example.invalid/repo.git#egg=interdit\n",
        encoding="utf-8",
    )

    specs = {spec.name: spec for spec in kdm.parse_dependency_file(requirement, "requirements.txt")}

    assert (specs["numpy"].operator, specs["numpy"].version) == (">=", "1.24")
    assert (specs["torch"].operator, specs["torch"].version) == ("==", "2.14.0")
    assert specs["requests"].operator == ""
    assert (specs["z3-solver"].operator, specs["z3-solver"].version) == (">=", "4.13")
    assert "interdit" not in specs


def test_parse_environment_yaml_handles_conda_items_and_pip_block(tmp_path: Path) -> None:
    environment = tmp_path / "environment.yml"
    environment.write_text(
        "name: demo\n"
        "channels:\n"
        "  - conda-forge\n"
        "dependencies:\n"
        "  - numpy=1.24\n"
        "  - pip\n"
        "  - pip:\n"
        "    - torch==2.1.0\n"
        "    - pandas>=2.0\n"
        "  - matplotlib\n",
        encoding="utf-8",
    )

    specs = {spec.name: spec for spec in kdm.parse_dependency_file(environment, "environment.yml")}

    assert (specs["numpy"].operator, specs["numpy"].version) == ("==", "1.24")
    assert (specs["torch"].operator, specs["torch"].version) == ("==", "2.1.0")
    assert (specs["pandas"].operator, specs["pandas"].version) == (">=", "2.0")
    assert specs["matplotlib"].operator == ""


def test_parse_dependency_file_tolerates_missing_file(tmp_path: Path) -> None:
    assert kdm.parse_dependency_file(tmp_path / "absent.txt", "absent.txt") == []


# ---------------------------------------------------------------------------
# Contraintes de version
# ---------------------------------------------------------------------------


@pytest.mark.parametrize(
    ("version", "operator", "constraint", "expected"),
    [
        ("2.12.5", "~=", "2.0", True),
        ("2.12.5", "~=", "2.12", True),
        ("3.0.0", "~=", "2.0", False),
        ("2.14.0", "==", "2.14.0", True),
        ("2.14.0", "==", "2.15.0", False),
        ("2.14.0", ">=", "2.13", True),
        ("2.13", ">=", "2.13", True),
        ("2.13", ">", "2.13", False),
        ("1.0", "<", "2.0", True),
        ("2.0", "<=", "2.0", True),
    ],
)
def test_satisfies(version: str, operator: str, constraint: str, expected: bool) -> None:
    assert kdm.satisfies(version, operator, constraint) is expected


def test_satisfies_is_indecidable_without_numbers() -> None:
    assert kdm.satisfies("", ">=", "1.0") is None
    assert kdm.satisfies("1.0", ">=", "latest") is None


def _spec(name: str, operator: str, version: str, source: str) -> kdm.PackageSpec:
    return kdm.PackageSpec(name=name, operator=operator, version=version, source=source)


def test_resolve_package_keeps_the_highest_lower_bound() -> None:
    occurrences = [
        _spec("pandas", ">=", "1.24", "a/requirements.txt"),
        _spec("pandas", ">=", "2.0", "b/requirements.txt"),
        _spec("pandas", ">=", "2.0.0", "c/requirements.txt"),
    ]
    pin, conflicts = kdm.resolve_package("pandas", occurrences)
    assert pin == ">=2.0.0"
    assert conflicts == []


def test_resolve_package_keeps_a_single_exact_pin() -> None:
    occurrences = [
        _spec("torch", "==", "2.14.0", "a/requirements.txt"),
        _spec("torch", ">=", "2.13", "b/requirements.txt"),
    ]
    pin, conflicts = kdm.resolve_package("torch", occurrences)
    assert pin == "==2.14.0"
    assert conflicts == []


def test_resolve_package_reports_a_pin_contradicted_by_a_bound() -> None:
    occurrences = [
        _spec("torch", "==", "2.1.0", "a/requirements.txt"),
        _spec("torch", ">=", "2.13", "b/requirements.txt"),
    ]
    _, conflicts = kdm.resolve_package("torch", occurrences)
    assert [conflict["kind"] for conflict in conflicts] == ["pin-contredit-une-borne"]
    assert "2.13" in conflicts[0]["resolution"]


def test_resolve_package_reports_disjoint_bounds() -> None:
    occurrences = [
        _spec("numpy", ">=", "2.0", "a/requirements.txt"),
        _spec("numpy", "<", "2.0", "b/requirements.txt"),
    ]
    _, conflicts = kdm.resolve_package("numpy", occurrences)
    assert [conflict["kind"] for conflict in conflicts] == ["bornes-disjointes"]


def test_resolve_package_reports_diverging_exact_pins() -> None:
    occurrences = [
        _spec("z3-solver", "==", "4.12.0", "a/requirements.txt"),
        _spec("z3-solver", "==", "4.13.0", "b/requirements.txt"),
    ]
    pin, conflicts = kdm.resolve_package("z3-solver", occurrences)
    assert pin == "==4.13.0"
    assert conflicts[0]["kind"] == "pins-exacts-divergents"


# ---------------------------------------------------------------------------
# Groupes et portee des fichiers
# ---------------------------------------------------------------------------


@pytest.mark.parametrize(
    ("path", "expected"),
    [
        (
            "MyIA.AI.Notebooks/GenAI/Texte/14-Prompt.ipynb",
            ("GenAI", "Texte"),
        ),
        ("MyIA.AI.Notebooks/GenAI/requirements.txt", ("GenAI", "(racine)")),
        ("MyIA.AI.Notebooks/GradeBook.ipynb", ("MyIA.AI.Notebooks", "(racine)")),
        ("scripts/sudoku/requirements.txt", ("scripts", "sudoku")),
        ("README.md", ("(racine)", "(racine)")),
    ],
)
def test_group_key(path: str, expected: tuple[str, str]) -> None:
    assert kdm.group_key(path) == expected


def test_group_key_does_not_fragment_deep_directories() -> None:
    deep = "MyIA.AI.Notebooks/GenAI/Audio/02-Advanced/02-10-Effets.ipynb"
    shallow = "MyIA.AI.Notebooks/GenAI/Audio/01-Foundation/01-1-Intro.ipynb"
    assert kdm.group_key(deep) == kdm.group_key(shallow) == ("GenAI", "Audio")


def test_attach_dependency_file_matches_a_sibling_qualifier() -> None:
    directories = {
        "MyIA.AI.Notebooks/GenAI",
        "MyIA.AI.Notebooks/GenAI/Audio",
        "MyIA.AI.Notebooks/GenAI/Video",
        "MyIA.AI.Notebooks/GenAI/Texte",
    }
    assert kdm.attach_dependency_file(
        "MyIA.AI.Notebooks/GenAI/requirements-audio.txt", directories
    ) == ("GenAI", "Audio")
    assert kdm.attach_dependency_file(
        "MyIA.AI.Notebooks/GenAI/requirements-video.txt", directories
    ) == ("GenAI", "Video")


def test_attach_dependency_file_falls_back_to_the_containing_directory() -> None:
    directories = {
        "MyIA.AI.Notebooks/GenAI",
        "MyIA.AI.Notebooks/GenAI/Texte",
        "MyIA.AI.Notebooks/SymbolicAI/SmartContracts",
    }
    assert kdm.attach_dependency_file(
        "MyIA.AI.Notebooks/GenAI/Texte/requirements-structured-outputs.txt", directories
    ) == ("GenAI", "Texte")
    assert kdm.attach_dependency_file(
        "MyIA.AI.Notebooks/SymbolicAI/SmartContracts/requirements-optional.txt", directories
    ) == ("SymbolicAI", "SmartContracts")


def test_is_series_base_only_accepts_a_bare_name_at_a_series_root() -> None:
    assert kdm.is_series_base("MyIA.AI.Notebooks/GenAI/requirements.txt")
    assert not kdm.is_series_base("MyIA.AI.Notebooks/GenAI/requirements-audio.txt")
    assert not kdm.is_series_base("MyIA.AI.Notebooks/GenAI/Texte/requirements.txt")


# ---------------------------------------------------------------------------
# Lecture des kernelspec
# ---------------------------------------------------------------------------


def _write_notebook(path: Path, payload: dict) -> None:
    path.write_text(json.dumps(payload), encoding="utf-8")


def test_read_kernelspec_reads_the_metadata_block(tmp_path: Path) -> None:
    notebook = tmp_path / "demo.ipynb"
    _write_notebook(
        notebook,
        {
            "cells": [],
            "metadata": {"kernelspec": {"name": "python3", "language": "python"}},
            "nbformat": 4,
            "nbformat_minor": 5,
        },
    )
    assert kdm.read_kernelspec(notebook) == ("python3", "python")


def test_read_kernelspec_finds_metadata_beyond_the_first_window(tmp_path: Path) -> None:
    notebook = tmp_path / "volumineux.ipynb"
    padding = "x" * (300 * 1024)
    notebook.write_text(
        '{"cells": [], "metadata": {"kernelspec": {"name": ".net-csharp", "language": "C#"}},'
        f' "padding": "{padding}", "nbformat": 4, "nbformat_minor": 5}}',
        encoding="utf-8",
    )
    assert kdm.read_kernelspec(notebook) == (".net-csharp", "C#")


def test_read_kernelspec_returns_none_without_metadata(tmp_path: Path) -> None:
    notebook = tmp_path / "nu.ipynb"
    _write_notebook(notebook, {"cells": [], "metadata": {}, "nbformat": 4, "nbformat_minor": 5})
    assert kdm.read_kernelspec(notebook) == (None, None)


# ---------------------------------------------------------------------------
# Verdicts
# ---------------------------------------------------------------------------

VERDICTS = {"inclus", "exclu", "service optionnel"}
EXCLUSION_MOTIFS = {"gpu", "taille", "licence", "conflit de versions"}


def _entry(**kwargs) -> kdm.GroupEntry:
    entry = kdm.GroupEntry(serie="Serie", sous_serie="Sous")
    for key, value in kwargs.items():
        setattr(entry, key, value)
    return entry


def test_verdict_excludes_a_gpu_majority_group(tmp_path: Path) -> None:
    entry = _entry(
        notebooks=[
            kdm.NotebookInfo(path="a.ipynb", requires_gpu=True),
            kdm.NotebookInfo(path="b.ipynb", requires_gpu=True),
            kdm.NotebookInfo(path="c.ipynb", requires_gpu=False),
        ]
    )
    assert kdm.decide_verdict(entry, 2000, tmp_path) == ("exclu", "gpu")


def test_verdict_keeps_a_group_with_a_single_gpu_notebook(tmp_path: Path) -> None:
    entry = _entry(
        notebooks=[
            kdm.NotebookInfo(path=f"{index}.ipynb", requires_gpu=index == 0)
            for index in range(10)
        ]
    )
    assert kdm.decide_verdict(entry, 2000, tmp_path) == ("inclus", "")


def test_verdict_excludes_a_restricted_licence(tmp_path: Path) -> None:
    entry = _entry(packages=[_spec("gurobipy", ">=", "10.0", "requirements.txt")])
    assert kdm.decide_verdict(entry, 2000, tmp_path) == ("exclu", "licence")


def test_verdict_excludes_a_group_whose_own_files_blow_the_budget(tmp_path: Path) -> None:
    requirement = tmp_path / "requirements.txt"
    requirement.write_text("torch\ntensorflow\n", encoding="utf-8")
    entry = _entry(dependency_files=["requirements.txt"])
    assert kdm.decide_verdict(entry, 1000, tmp_path) == ("exclu", "taille")
    assert kdm.decide_verdict(entry, 5000, tmp_path) == ("inclus", "")


def test_verdict_marks_a_cloud_group_as_an_optional_service(tmp_path: Path) -> None:
    entry = _entry(notebooks=[kdm.NotebookInfo(path="a.ipynb", requires_cloud=True)])
    assert kdm.decide_verdict(entry, 2000, tmp_path) == ("service optionnel", "service")


# ---------------------------------------------------------------------------
# Integration sur l'arbre reel
# ---------------------------------------------------------------------------


@pytest.fixture(scope="module")
def payload() -> dict:
    return kdm.build_payload(REPO_ROOT, kdm.DEFAULT_IMAGE_BUDGET_MB)


def test_every_notebook_group_appears_in_the_table(payload: dict) -> None:
    files = kdm.git_ls_files(REPO_ROOT)
    expected = {kdm.group_key(path) for path in files if path.endswith(".ipynb")}
    got = {(group["serie"], group["sous_serie"]) for group in payload["groups"]}
    assert expected <= got


def test_every_group_carries_a_verdict_and_every_exclusion_a_motif(payload: dict) -> None:
    for group in payload["groups"]:
        assert group["verdict"] in VERDICTS, group
        if group["verdict"] == "exclu":
            assert group["motif"] in EXCLUSION_MOTIFS, group
        else:
            assert group["motif"] in ("", "service"), group


def test_manifest_covers_every_included_group_package(payload: dict) -> None:
    declared = {
        spec.name
        for entry in kdm.build_groups(REPO_ROOT)[0]
        for spec in entry.packages
    }
    assert declared
    assert set(payload["manifest"]) <= declared
    for name, data in payload["manifest"].items():
        assert data["pin"], name
        assert data["declared_by"], name


def test_committed_manifest_is_up_to_date() -> None:
    assert kdm.main(["--repo-root", str(REPO_ROOT), "--check", "--quiet"]) == 0