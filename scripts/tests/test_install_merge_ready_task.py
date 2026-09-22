"""Tests hermetiques de l'installateur merge_ready (Q40) -- aucun schtasks reel.

La discipline UAC du depot exige que le dry-run imprime la commande schtasks
exacte SANS l'executer : le test verifie les deux moities (la commande est
imprimee, aucun sous-processus n'est lance).
"""

import importlib.util
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
INSTALLER_PATH = HERE.parent / "coordination" / "install_merge_ready_task.py"
_spec = importlib.util.spec_from_file_location(
    "install_merge_ready_task_under_test", INSTALLER_PATH
)
imod = importlib.util.module_from_spec(_spec)
sys.modules["install_merge_ready_task_under_test"] = imod
_spec.loader.exec_module(imod)


def test_build_schtasks_toutes_les_20_minutes(tmp_path):
    cmd = imod.build_schtasks_install(imod.task_command(tmp_path), 20)
    assert cmd[0:3] == ["schtasks", "/Create", "/F"]
    assert cmd[cmd.index("/TN") + 1] == imod.TASK_NAME
    assert cmd[cmd.index("/SC") + 1] == "MINUTE"
    assert cmd[cmd.index("/MO") + 1] == "20"
    # la tache appelle le wrapper --run de cet installateur (qui journalise
    # puis lance l'organe en --apply), pas l'organe nu
    tr = cmd[cmd.index("/TR") + 1]
    assert "install_merge_ready_task.py" in tr and "--run" in tr


def test_dry_run_imprime_la_commande_sans_l_executer(tmp_path, capsys, monkeypatch):
    def boom(cmd, **kw):
        raise AssertionError(
            "aucun sous-processus ne doit etre lance en --dry-run : "
            + str(cmd)
        )

    monkeypatch.setattr(imod, "_run", boom)
    monkeypatch.setattr(imod.subprocess, "run", boom)
    rc = imod.main(["--dry-run", "--repo", str(tmp_path)])
    out = capsys.readouterr().out
    assert rc == 0
    assert "schtasks" in out
    assert "/Create" in out
    assert "/SC" in out and "MINUTE" in out
    assert "/MO" in out and " 20" in out
    assert "--run" in out
    assert "DRY-RUN" in out


def test_install_refuse_organe_absent(tmp_path, capsys, monkeypatch):
    def boom(cmd, **kw):
        raise AssertionError("un depot vide ne doit jamais atteindre schtasks")

    monkeypatch.setattr(imod, "_run", boom)
    repo = tmp_path / "vide"  # sans scripts/coordination/merge_ready.py
    rc = imod.main(["--install", "--repo", str(repo)])
    assert rc == 2
    assert "REFUSE" in capsys.readouterr().err
