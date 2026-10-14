#!/usr/bin/env python3
"""Tests du helper de prechargement NuGet `scripts/ci/dotnet_preload_packages.py`.

Le helper existe parce que le 2e `#r "nuget:"` d'une session dotnet-interactive
peut lever `PackageRestoreResult..ctor ArgumentException` (#17361, non
deterministe), ce qui tue la cellule sans contournement runtime. La parade est
de ne plus appeler `#r "nuget:"` du tout et de referencer des assembly locales.

Ce que ces tests couvrent -- la resolution de cache et la forme des sorties, qui
sont la partie ou une erreur silencieuse coute une re-execution de notebook :
  - `parse_spec` : `Nom`, `Nom==1.2.3`, `Nom@1.2.3`, spec vide/mal formee ;
  - `_version_key` : tri numerique (`2.10.0` > `2.9.0`) et prerelease < release ;
  - `resolve_version` : version exacte, plus haute, absente, casse du dossier ;
  - `pick_assemblies` : TFM prefere, repli alphabetique, package sans `lib` ;
  - `main` : copie a plat, manifest, ligne `#r` relative, rc=1 sur echec.

`dotnet` n'est JAMAIS invoque : le `restorer` est injecte (aucun reseau, aucun
SDK requis en CI).
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "ci"))

import dotnet_preload_packages as dpp  # noqa: E402


def _make_package(root: Path, package: str, version: str, tfms: dict[str, list[str]]) -> Path:
    """Fabrique un package dans un cache NuGet factice et rend son dossier."""
    version_dir = root / package.lower() / version.lower()
    for tfm, dlls in tfms.items():
        lib = version_dir / "lib" / tfm
        lib.mkdir(parents=True, exist_ok=True)
        for dll in dlls:
            (lib / dll).write_text("fake assembly", encoding="utf-8")
    return version_dir


def _never_called(package: str, version: str | None) -> tuple[bool, str]:
    raise AssertionError(f"le restorer ne devait pas etre appele ({package} {version})")


# --- parse_spec -------------------------------------------------------------


@pytest.mark.parametrize(
    ("spec", "expected"),
    [
        ("QuikGraph", ("QuikGraph", None)),
        ("QuikGraph==2.5.0", ("QuikGraph", "2.5.0")),
        ("QuikGraph@2.5.0", ("QuikGraph", "2.5.0")),
        ("  CsvHelper==33.0.1  ", ("CsvHelper", "33.0.1")),
        ("IKVM.Runtime==8.15.0", ("IKVM.Runtime", "8.15.0")),
        ("A.B-C_D==1.0.0-rc1", ("A.B-C_D", "1.0.0-rc1")),
    ],
)
def test_parse_spec_valid(spec, expected):
    assert dpp.parse_spec(spec) == expected


@pytest.mark.parametrize("spec", ["", "   ", "==1.0.0", "Nom==", "Nom+meta==1.0.0", "a b"])
def test_parse_spec_invalid(spec):
    with pytest.raises(ValueError):
        dpp.parse_spec(spec)


# --- _version_key -----------------------------------------------------------


def test_version_key_is_numeric_not_lexicographic():
    assert dpp._version_key("2.10.0") > dpp._version_key("2.9.0")


def test_version_key_prerelease_sorts_below_release():
    assert dpp._version_key("1.0.0-rc1") < dpp._version_key("1.0.0")


def test_version_key_pads_missing_components():
    assert dpp._version_key("2.0") == dpp._version_key("2.0.0.0")


# --- resolve_version --------------------------------------------------------


def test_resolve_version_exact(tmp_path):
    _make_package(tmp_path, "QuikGraph", "2.5.0", {"netstandard2.0": ["QuikGraph.dll"]})
    resolved = dpp.resolve_version(tmp_path, "QuikGraph", "2.5.0")
    assert resolved is not None and resolved.name == "2.5.0"


def test_resolve_version_exact_missing_does_not_fall_back(tmp_path):
    """Un pin non satisfait doit se VOIR, pas deriver silencieusement."""
    _make_package(tmp_path, "QuikGraph", "2.5.0", {"netstandard2.0": ["QuikGraph.dll"]})
    assert dpp.resolve_version(tmp_path, "QuikGraph", "9.9.9") is None


def test_resolve_version_picks_highest(tmp_path):
    for version in ("2.5.0", "2.9.0", "2.10.0"):
        _make_package(tmp_path, "QuikGraph", version, {"netstandard2.0": ["QuikGraph.dll"]})
    resolved = dpp.resolve_version(tmp_path, "QuikGraph", None)
    assert resolved is not None and resolved.name == "2.10.0"


def test_resolve_version_is_case_insensitive_on_disk(tmp_path):
    _make_package(tmp_path, "QuikGraph", "2.5.0", {"netstandard2.0": ["QuikGraph.dll"]})
    assert dpp.resolve_version(tmp_path, "QUIKGRAPH", "2.5.0") is not None


def test_resolve_version_absent_package(tmp_path):
    assert dpp.resolve_version(tmp_path, "QuikGraph", None) is None


# --- pick_assemblies --------------------------------------------------------


def test_pick_assemblies_prefers_net9(tmp_path):
    version_dir = _make_package(
        tmp_path,
        "Pkg",
        "1.0.0",
        {"netstandard2.0": ["Pkg.dll"], "net9.0": ["Pkg.dll"]},
    )
    picked = dpp.pick_assemblies(version_dir)
    assert [path.parent.name for path in picked] == ["net9.0"]


def test_pick_assemblies_falls_back_to_first_tfm(tmp_path):
    version_dir = _make_package(tmp_path, "Pkg", "1.0.0", {"weird-tfm": ["Pkg.dll"]})
    picked = dpp.pick_assemblies(version_dir)
    assert [path.name for path in picked] == ["Pkg.dll"]


def test_pick_assemblies_without_lib_dir(tmp_path):
    version_dir = tmp_path / "pkg" / "1.0.0"
    version_dir.mkdir(parents=True)
    assert dpp.pick_assemblies(version_dir) == []


# --- _reference_line --------------------------------------------------------


def test_reference_line_relative_uses_measured_form():
    """Forme mesuree c.790 : `#r "./_deps/X.dll"` (litteral, parse-time)."""
    assert dpp._reference_line(Path("_deps"), "QuikGraph.dll") == '#r "./_deps/QuikGraph.dll"'


def test_reference_line_absolute_is_kept_as_is(tmp_path):
    """Un chemin absolu ne peut pas etre relatif au notebook : il est rendu tel quel."""
    assert dpp._reference_line(tmp_path, "Pkg.dll") == f'#r "{tmp_path.as_posix()}/Pkg.dll"'


# --- main : chemin nominal --------------------------------------------------


def test_main_copies_flat_and_emits_manifest(tmp_path, monkeypatch):
    cache = tmp_path / "cache"
    _make_package(
        cache,
        "QuikGraph",
        "2.5.0",
        {"netstandard2.0": ["QuikGraph.dll", "QuikGraph.Contracts.dll"]},
    )
    monkeypatch.setenv("NUGET_PACKAGES", str(cache))
    # Dest RELATIF (la forme d'usage : le notebook et `_deps/` sont voisins).
    monkeypatch.chdir(tmp_path)
    dest = Path("_deps")

    rc = dpp.main(["--dest", str(dest), "QuikGraph==2.5.0"], restorer=_never_called)

    assert rc == 0
    # Copie A PLAT : c'est la forme verifiee `#r "./_deps/X.dll"`.
    assert sorted(path.name for path in dest.glob("*.dll")) == [
        "QuikGraph.Contracts.dll",
        "QuikGraph.dll",
    ]

    manifest = json.loads((dest / ".NET-packages.json").read_text(encoding="utf-8"))
    assert manifest["schema"] == dpp.SCHEMA
    assert manifest["issue"] == 17361
    entry = manifest["packages"][0]
    assert entry["package"] == "QuikGraph"
    assert entry["version"] == "2.5.0"
    assert "error" not in entry
    assert entry["reference"] == [
        '#r "./_deps/QuikGraph.Contracts.dll"',
        '#r "./_deps/QuikGraph.dll"',
    ]


def test_main_pins_exact_version_over_higher_cached(tmp_path, monkeypatch):
    cache = tmp_path / "cache"
    _make_package(cache, "QuikGraph", "2.5.0", {"netstandard2.0": ["QuikGraph.dll"]})
    _make_package(cache, "QuikGraph", "2.6.0", {"netstandard2.0": ["QuikGraph.dll"]})
    monkeypatch.setenv("NUGET_PACKAGES", str(cache))
    dest = tmp_path / "_deps"

    assert dpp.main(["--dest", str(dest), "QuikGraph==2.5.0"], restorer=_never_called) == 0
    manifest = json.loads((dest / ".NET-packages.json").read_text(encoding="utf-8"))
    assert manifest["packages"][0]["version"] == "2.5.0"


def test_main_json_writes_manifest_and_stdout(tmp_path, monkeypatch, capsys):
    cache = tmp_path / "cache"
    _make_package(cache, "QuikGraph", "2.5.0", {"netstandard2.0": ["QuikGraph.dll"]})
    monkeypatch.setenv("NUGET_PACKAGES", str(cache))
    dest = tmp_path / "_deps"

    assert dpp.main(["--dest", str(dest), "--json", "QuikGraph"], restorer=_never_called) == 0
    assert json.loads(capsys.readouterr().out)["packages"][0]["version"] == "2.5.0"


# --- main : chemin de restauration ------------------------------------------


def test_main_restores_then_resolves(tmp_path, monkeypatch):
    """Package absent du cache -> le restorer est appele, puis la resolution reussit."""
    cache = tmp_path / "cache"
    monkeypatch.setenv("NUGET_PACKAGES", str(cache))
    dest = tmp_path / "_deps"
    calls: list[tuple[str, str | None]] = []

    def restorer(package: str, version: str | None) -> tuple[bool, str]:
        calls.append((package, version))
        _make_package(cache, package, version or "0.0.1", {"net9.0": [f"{package}.dll"]})
        return True, f"dotnet restore rc=0 ({package} {version})"

    rc = dpp.main(["--dest", str(dest), "IKVM==8.15.0"], restorer=restorer)

    assert rc == 0
    assert calls == [("IKVM", "8.15.0")]
    manifest = json.loads((dest / ".NET-packages.json").read_text(encoding="utf-8"))
    assert manifest["packages"][0]["restore"].startswith("dotnet restore rc=0")
    assert (dest / "IKVM.dll").is_file()


def test_main_reports_failure_and_returns_1(tmp_path, monkeypatch):
    monkeypatch.setenv("NUGET_PACKAGES", str(tmp_path / "vide"))
    dest = tmp_path / "_deps"

    def failing(package: str, version: str | None) -> tuple[bool, str]:
        return False, "dotnet introuvable dans le PATH"

    rc = dpp.main(["--dest", str(dest), "QuikGraph==2.5.0"], restorer=failing)

    assert rc == 1
    manifest = json.loads((dest / ".NET-packages.json").read_text(encoding="utf-8"))
    assert manifest["packages"][0]["error"] == "dotnet introuvable dans le PATH"


def test_main_restore_without_version_refuses_early(tmp_path, monkeypatch):
    """Sans version epinglee, `dotnet restore` est refuse AVANT d'etre tente."""
    monkeypatch.setenv("NUGET_PACKAGES", str(tmp_path / "vide"))
    dest = tmp_path / "_deps"

    def failing(package: str, version: str | None) -> tuple[bool, str]:
        return False, f"{package} absent du cache et aucune version epinglee : " \
                      "`dotnet restore` exige `Nom==x.y.z`"

    rc = dpp.main(["--dest", str(dest), "QuikGraph"], restorer=failing)

    assert rc == 1
    manifest = json.loads((dest / ".NET-packages.json").read_text(encoding="utf-8"))
    assert "aucune version epinglee" in manifest["packages"][0]["error"]


# --- main : entrees malformees ----------------------------------------------


def test_main_bad_spec_is_reported_not_raised(tmp_path, monkeypatch):
    monkeypatch.setenv("NUGET_PACKAGES", str(tmp_path / "vide"))
    dest = tmp_path / "_deps"

    rc = dpp.main(["--dest", str(dest), "Nom avec espaces"], restorer=_never_called)

    assert rc == 1
    manifest = json.loads((dest / ".NET-packages.json").read_text(encoding="utf-8"))
    assert "specification invalide" in manifest["packages"][0]["error"]


def test_main_mixed_batch_keeps_good_entries(tmp_path, monkeypatch):
    """Un echec ne doit pas emporter les packages resolus du meme lot."""
    cache = tmp_path / "cache"
    _make_package(cache, "QuikGraph", "2.5.0", {"netstandard2.0": ["QuikGraph.dll"]})
    monkeypatch.setenv("NUGET_PACKAGES", str(cache))
    dest = tmp_path / "_deps"

    def failing(package: str, version: str | None) -> tuple[bool, str]:
        return False, f"{package} absent du cache"

    rc = dpp.main(["--dest", str(dest), "QuikGraph", "CsvHelper"], restorer=failing)

    assert rc == 1
    manifest = json.loads((dest / ".NET-packages.json").read_text(encoding="utf-8"))
    by_package = {entry.get("package"): entry for entry in manifest["packages"]}
    assert "error" not in by_package["QuikGraph"]
    assert "error" in by_package["CsvHelper"]
    assert (dest / "QuikGraph.dll").is_file()


def test_manifest_ends_with_single_newline(tmp_path, monkeypatch):
    """Pas de CRLF : les manifests sont lus par des outils, pas par un shell Windows."""
    cache = tmp_path / "cache"
    _make_package(cache, "QuikGraph", "2.5.0", {"netstandard2.0": ["QuikGraph.dll"]})
    monkeypatch.setenv("NUGET_PACKAGES", str(cache))
    dest = tmp_path / "_deps"

    assert dpp.main(["--dest", str(dest), "QuikGraph"], restorer=_never_called) == 0
    raw = (dest / ".NET-packages.json").read_bytes()
    assert b"\r\n" not in raw
    assert raw.endswith(b"\n")


# --- restore_via_dotnet (subprocess simule) ---------------------------------


class _FakeProc:
    def __init__(self, returncode: int, stdout: str = "", stderr: str = "") -> None:
        self.returncode = returncode
        self.stdout = stdout
        self.stderr = stderr


def test_restore_refuses_without_pinned_version(monkeypatch):
    """Sans version, on n'appelle meme pas `dotnet` : le refus est explicite."""
    monkeypatch.setattr(dpp.shutil, "which", lambda _: "/usr/bin/dotnet")
    monkeypatch.setattr(
        dpp.subprocess, "run", lambda *a, **k: pytest.fail("dotnet ne devait pas etre lance")
    )
    ok, message = dpp.restore_via_dotnet("QuikGraph", None)
    assert ok is False and "aucune version epinglee" in message


def test_restore_reports_stdout_errors(monkeypatch):
    """`dotnet restore -v quiet` ecrit ses erreurs sur STDOUT : ne pas les perdre."""
    monkeypatch.setattr(dpp.shutil, "which", lambda _: "/usr/bin/dotnet")
    monkeypatch.setattr(
        dpp.subprocess,
        "run",
        lambda *a, **k: _FakeProc(1, stdout="error NU1101: Unable to find package\n"),
    )
    ok, message = dpp.restore_via_dotnet("Inexistant", "1.0.0")
    assert ok is False
    assert "NU1101" in message
    assert "(aucune sortie)" not in message


def test_restore_missing_dotnet_is_ordinary_failure(monkeypatch):
    monkeypatch.setattr(dpp.shutil, "which", lambda _: None)
    ok, message = dpp.restore_via_dotnet("QuikGraph", "2.5.0")
    assert ok is False and "introuvable dans le PATH" in message


def test_restore_timeout_is_ordinary_failure(monkeypatch):
    monkeypatch.setattr(dpp.shutil, "which", lambda _: "/usr/bin/dotnet")

    def boom(*args, **kwargs):
        raise dpp.subprocess.TimeoutExpired(cmd="dotnet", timeout=1)

    monkeypatch.setattr(dpp.subprocess, "run", boom)
    ok, message = dpp.restore_via_dotnet("QuikGraph", "2.5.0", timeout=1)
    assert ok is False and "timeout" in message


def test_restore_success_message(monkeypatch):
    monkeypatch.setattr(dpp.shutil, "which", lambda _: "/usr/bin/dotnet")
    monkeypatch.setattr(dpp.subprocess, "run", lambda *a, **k: _FakeProc(0))
    ok, message = dpp.restore_via_dotnet("QuikGraph", "2.5.0")
    assert ok is True and "rc=0" in message


# --- nuget_root -------------------------------------------------------------


def test_nuget_root_honours_env(tmp_path, monkeypatch):
    monkeypatch.setenv("NUGET_PACKAGES", str(tmp_path / "perso"))
    assert dpp.nuget_root() == tmp_path / "perso"


def test_nuget_root_defaults_to_home(monkeypatch):
    monkeypatch.delenv("NUGET_PACKAGES", raising=False)
    assert dpp.nuget_root().name == "packages"
