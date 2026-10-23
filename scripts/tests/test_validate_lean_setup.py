#!/usr/bin/env python3
r"""Tests du validateur d'environnement Lean 4 (#21614).

Pinent les quatre defauts mesures sur `myia-po-2028` (Windows 11,
`powershell.exe` 5.1), chacun avec un controle POSITIF et un controle
NEGATIF :

1. Encodage console cp1252 -- le validateur imprimait `✓` (U+2713) sur une
   console cp1252 : `UnicodeEncodeError` a la premiere ligne de resultat, le
   verdict n'etait jamais rendu. Controle positif : l'appel des fonctions
   d'affichage sur une sortie cp1252 ne leve pas et rend un texte lisible ;
   controle negatif : le texte ASCII traverse inchange.

2. Cote valide -- sur un poste installe en WSL, la chaine elan/lean/lake
   n'existe que dans la distro ; la compter comme "composants manquants"
   rendait un verdict incoherent avec ce que le setup installe. Controle
   positif : la chaine Windows complete -> 3 composants ; controle negatif :
   chaine Windows absente + poste WSL -> 0 composant manquant et un verdict
   explicite ; sans marqueur WSL -> 3 manquants (verdict honnete).

3. `kernel.json` cherche du mauvais cote -- en mode `--wsl` (le script
   tourne DANS WSL), `%APPDATA%` n'est pas exporte : l'enregistrement
   Windows etait invisible et le check annonçait "aucun kernel.json trouve"
   pour un kernel enregistre. Controle positif : depuis WSL, le chemin
   Windows `/mnt/c/Users/<u>/AppData/Roaming/jupyter/kernels/<n>/kernel.json`
   est trouve ; controle negatif : un chemin de profil inexistant ne rend
   aucun candidat.

4. `python-dotenv` -- le nom de distribution n'est pas le nom de module :
   la transformation automatique `-` -> `_` produisait `python_dotenv`, un
   module inexistant, et le check concluait "Non installe" pour un paquet
   present. Controle positif : un module `dotenv` installe est vu installe ;
   controle negatif : le module calcule n'est jamais `python_dotenv`.

5. Le setup cree le venv que le validateur controle -- `setup_wsl_lean4.sh`
   cree `~/.lean4-venv`, alors que le validateur (et le kernel
   `python3-wsl`) regardent `~/.python3-wsl-venv` : la chaine n'installait
   jamais le venv valide. Controle positif : le flux complet appelle
   l'etape venv ; controle negatif : l'etape venv pointe bien sur
   `setup_wsl_python.sh`.

Run : python -m pytest scripts/tests/test_validate_lean_setup.py
"""

import importlib.util
import io
import json
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[2]
VALIDATOR_PATH = (REPO_ROOT / "MyIA.AI.Notebooks" / "SymbolicAI" / "Lean"
                   / "scripts" / "validate_lean_setup.py")
SETUP_PATH = REPO_ROOT / "scripts" / "lean" / "setup_lean4_all.py"
KERNEL_CHECK_PATH = REPO_ROOT / "scripts" / "lean" / "lean_kernel_check.py"


def _load(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


@pytest.fixture(scope="module")
def validator():
    return _load(VALIDATOR_PATH, "validate_lean_setup_under_test")


@pytest.fixture(scope="module")
def kernel_check():
    return _load(KERNEL_CHECK_PATH, "lean_kernel_check_under_test")


@pytest.fixture(scope="module")
def setup_module():
    return _load(SETUP_PATH, "setup_lean4_all_under_test")


class _Cp1252Stream(io.TextIOWrapper):
    """Sortie texte dont l'encodage est cp1252 (console Windows par defaut)."""

    def __init__(self):
        self._buffer = io.BytesIO()
        super().__init__(self._buffer, encoding="cp1252", newline="")


# --- Defaut 1 : encodage console -----------------------------------------


def test_print_helpers_survive_a_cp1252_console(validator, capsys):
    """Controle POSITIF : aucun UnicodeEncodeError sur une sortie cp1252."""
    stream = _Cp1252Stream()
    original = sys.stdout
    sys.stdout = stream
    try:
        validator.print_ok("Lean 4: version 4.35.0")
        validator.print_error("Lake: Non trouve")
        validator.print_warning("Composants OK: 3/13")
        validator.print_section("RESULTAT")
        stream.flush()
        payload = stream._buffer.getvalue()
    finally:
        sys.stdout = original

    text = payload.decode("cp1252")
    assert "Lean 4: version 4.35.0" in text
    assert "RESULTAT" in text
    # Le verdict reste lisible : aucun octet de remplacement UTF-8 (les
    # glyphes Unicode ont ete remplaces, pas laisses tels quels).
    assert "�" not in text


def test_ascii_text_passes_through_unchanged(validator):
    """Controle NEGATIF : le texte ASCII n'est pas degrade."""
    assert validator._safe("Lean 4: OK") == "Lean 4: OK"

    stream = _Cp1252Stream()
    original = sys.stdout
    sys.stdout = stream
    try:
        assert validator._safe("Lean 4: OK") == "Lean 4: OK"
        # Un caractere hors cp1252 (U+2713) ne doit pas survivre tel quel.
        assert validator._safe("✓") != "✓"
    finally:
        sys.stdout = original


# --- Defaut 2 : le cote valide -------------------------------------------


def test_lean_toolchain_counts_the_windows_chain_when_present(validator, monkeypatch):
    """Controle POSITIF : chaine Windows complete -> 3 composants."""
    monkeypatch.setattr(validator.shutil, "which", lambda cmd: f"/usr/bin/{cmd}")
    monkeypatch.setattr(validator, "_kernel_drives_wsl", lambda *a, **k: False)
    checks = validator.check_lean_toolchain()
    assert len(checks) == 3
    assert all(checks)


def test_lean_toolchain_excludes_the_windows_chain_on_a_wsl_seat(validator, monkeypatch):
    """Controle NEGATIF : poste WSL sans chaine Windows -> aucun manquant."""
    monkeypatch.setattr(validator.shutil, "which", lambda cmd: None)
    monkeypatch.setattr(validator, "_kernel_drives_wsl", lambda *a, **k: True)
    checks = validator.check_lean_toolchain()
    assert checks == []


def test_lean_toolchain_reports_missing_when_not_a_wsl_seat(validator, monkeypatch):
    """Hors WSL, une chaine Windows absente reste un verdict negatif."""
    monkeypatch.setattr(validator.shutil, "which", lambda cmd: None)
    monkeypatch.setattr(validator, "_kernel_drives_wsl", lambda *a, **k: False)
    checks = validator.check_lean_toolchain()
    assert len(checks) == 3
    assert not any(checks)


# --- Defaut 3 : le kernel.json du bon cote -------------------------------


def test_windows_kernel_json_is_found_from_inside_wsl(kernel_check, tmp_path):
    """Controle POSITIF : le chemin Windows est resolu depuis WSL."""
    users = tmp_path / "Users"
    profile = users / "tester"
    kj = profile / "AppData" / "Roaming" / "jupyter" / "kernels" / "lean4-wsl" / "kernel.json"
    kj.parent.mkdir(parents=True)
    kj.write_text(json.dumps({"argv": ["wsl.exe", "-d", "Ubuntu", "python3",
                                       "/home/tester/.lean4-kernel-wrapper.py"]}),
                  encoding="utf-8")

    candidates = kernel_check.windows_kernel_json_candidates(
        "lean4-wsl", windows_users_root=str(users))
    assert kj in candidates


def test_no_candidate_for_an_absent_profile(kernel_check, tmp_path, monkeypatch):
    """Controle NEGATIF : un profil inexistant ne rend aucun candidat."""
    monkeypatch.delenv("APPDATA", raising=False)
    candidates = kernel_check.windows_kernel_json_candidates(
        "lean4-wsl", windows_users_root=str(tmp_path / "Users"))
    assert candidates == []


def test_kernel_drives_wsl_reads_the_registered_argv(kernel_check, tmp_path):
    """Le marqueur WSL est lu dans l'argv du kernel.json enregistre."""
    kj = tmp_path / "kernel.json"
    kj.write_text(json.dumps({"argv": ["wsl.exe", "-d", "Ubuntu",
                                        "/home/tester/.lean4-kernel-wrapper.py"]}),
                  encoding="utf-8")
    assert kernel_check.kernel_drives_wsl("lean4-wsl", kernel_json_path=kj) is True

    native = tmp_path / "native.json"
    native.write_text(json.dumps({"argv": ["python", "-m", "lean_kernel"]}),
                      encoding="utf-8")
    assert kernel_check.kernel_drives_wsl("lean4-wsl", kernel_json_path=native) is False


# --- Defaut 4 : le nom de module du paquet --------------------------------


def test_python_dotenv_is_checked_under_its_module_name(validator, tmp_path, monkeypatch):
    """Controle POSITIF : un paquet `python-dotenv` installe est vu installe."""
    (tmp_path / "dotenv.py").write_text("__version__ = '1.2.4'\n", encoding="utf-8")
    monkeypatch.syspath_prepend(str(tmp_path))
    monkeypatch.delitem(sys.modules, "dotenv", raising=False)
    assert validator.check_python_package("python-dotenv") is True


def test_no_distribution_maps_to_a_dashed_module_name(validator):
    """Controle NEGATIF : `python_dotenv` n'est jamais le module teste."""
    assert validator.PKG_IMPORTS["python-dotenv"] == "dotenv"
    assert "python_dotenv" not in validator.PKG_IMPORTS.values()
    for distribution, module in validator.PKG_IMPORTS.items():
        if "-" in distribution:
            assert module != distribution.replace("-", "_")


# --- Defaut 5 : le setup cree le venv valide ------------------------------


def test_setup_full_flow_runs_the_wsl_python_venv_step(setup_module, monkeypatch):
    """Controle POSITIF : le flux complet installe le venv valide."""
    calls = []

    def _fake_step(name, ok=True):
        def _inner(*args, **kwargs):
            calls.append(name)
            return ok
        return _inner

    monkeypatch.setattr(setup_module, "step_wsl_install", _fake_step("wsl_install"))
    monkeypatch.setattr(setup_module, "step_wsl_python_venv", _fake_step("wsl_venv"))
    monkeypatch.setattr(setup_module, "step_register_kernel", _fake_step("register"))
    monkeypatch.setattr(setup_module, "step_validate", _fake_step("validate"))
    monkeypatch.setattr(setup_module, "check_wrapper_registration", _fake_step("wrapper"))
    monkeypatch.setattr(setup_module.sys, "argv", ["setup_lean4_all.py"])

    with pytest.raises(SystemExit):
        setup_module.main()

    assert calls == ["wsl_install", "wsl_venv", "register", "validate", "wrapper"]


def test_wsl_venv_step_targets_setup_wsl_python(setup_module, monkeypatch):
    """Controle NEGATIF : l'etape venv pointe sur setup_wsl_python.sh."""
    recorded = {}

    class _Result:
        returncode = 0

    def _fake_run(cmd, **kwargs):
        recorded["cmd"] = cmd
        return _Result()

    monkeypatch.setattr(setup_module.subprocess, "run", _fake_run)
    assert setup_module.step_wsl_python_venv() is True
    assert any("setup_wsl_python.sh" in str(part) for part in recorded["cmd"])
