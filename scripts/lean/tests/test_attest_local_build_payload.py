"""Tests du payload de build remis a l'organe canonique (#26699, #15666).

Le payload `lake build <cibles>` est construit **au point de la remise** a
`scripts/lean/lean_exec.py`, et nulle part ailleurs : une liste de commande
posee hors de la main de l'organe est une voie directe, que le garde
`scripts/lean/check_lake_direct_invocation.py` refuse (forme 2 : jeton
`lake` dans un literal de liste).

Ce fichier verifie le CONTRAT de la remise :
- le payload cible est `lake build <cibles>` ;
- le payload du lac entier est `lake build` (mode `all`) ;
- l'argv construit par l'organe contient bien ce payload, apres le `--` ;
- ce fichier ne lance aucun processus : l'execution est neutralisee.

Aucun lake, aucun reseau, aucune machine.
"""

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import attest_local_build  # noqa: E402
from attest_local_build import _lean_exec_argv, run_lake_build  # noqa: E402


class _FakeProc:
    """Resultat d'execution neutre : l'organe n'a rien lance."""

    returncode = 0
    stdout = "{}"
    stderr = ""


def _capture_payload(monkeypatch) -> list:
    """Capture le payload remis a l'organe, sans lancer quoi que ce soit."""
    captured: dict = {}

    def fake_argv(payload, **kwargs):
        captured["payload"] = list(payload)
        return ["fake-organe"]

    monkeypatch.setattr(attest_local_build, "_lean_exec_argv", fake_argv)
    monkeypatch.setattr(attest_local_build, "_run", lambda *a, **k: _FakeProc())
    return captured


def test_le_payload_cible_est_remis_a_l_organe(monkeypatch, tmp_path):
    captured = _capture_payload(monkeypatch)
    run_lake_build(tmp_path, timeout=1.0, targets=["Demo.Alpha", "Demo.Delta"])
    assert captured["payload"] == ["lake", "build", "Demo.Alpha", "Demo.Delta"]


def test_le_payload_du_lac_entier_ne_porte_aucune_cible(monkeypatch, tmp_path):
    captured = _capture_payload(monkeypatch)
    run_lake_build(tmp_path, timeout=1.0, targets=[])
    assert captured["payload"] == ["lake", "build"]


def test_une_cible_absente_porte_le_meme_payload(monkeypatch, tmp_path):
    """`targets=None` (mode `all`) et `targets=[]` sont le meme lac entier."""
    captured = _capture_payload(monkeypatch)
    run_lake_build(tmp_path, timeout=1.0, targets=None)
    assert captured["payload"] == ["lake", "build"]


def test_l_argv_de_l_organe_porte_le_payload_apres_le_separateur(tmp_path):
    """L'organe recoit la commande dans son payload, apres le `--`."""
    argv = _lean_exec_argv(
        ["lake", "build", "Demo.Alpha"],
        lake_dir=tmp_path,
        timeout=60.0,
        stdout_file=tmp_path / "stdout.txt",
        stderr_file=tmp_path / "stderr.txt",
    )
    # Le separateur `--` precede le payload : rien n'est execute avant lui.
    separateur = argv.index("--")
    assert argv[separateur + 1:] == ["lake", "build", "Demo.Alpha"]


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(pytest.main([__file__, "-v"]))
