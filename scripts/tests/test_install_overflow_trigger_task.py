from __future__ import annotations

import sys
from pathlib import Path

CI_DIR = Path(__file__).resolve().parents[1] / "ci"
sys.path.insert(0, str(CI_DIR))

import install_overflow_trigger_task as inst  # noqa: E402


def test_le_dry_run_imprime_la_commande_schtasks_exacte_sans_ecrire(monkeypatch, capsys, tmp_path):
    """Discipline UAC : la sortie du dry-run precede toute inscription
    schtasks. Il n'ecrit donc RIEN -- pas meme les lanceurs."""
    monkeypatch.setenv("LOCALAPPDATA", str(tmp_path))
    inst.BASE_DIR = tmp_path / "CoursIA" / "overflow_trigger"
    inst.LOG_DIR = inst.BASE_DIR / "logs"
    inst.CMD_PATH = inst.BASE_DIR / "dispatch_overflow.cmd"
    inst.VBS_PATH = inst.BASE_DIR / "run_hidden.vbs"
    rc = inst.main(["--dry-run"])
    out = capsys.readouterr().out
    assert rc == 0
    assert "schtasks /Create /F" in out
    assert str(inst.TASK_NAME) in out
    assert "/SC MINUTE" in out
    assert "/MO 15" in out
    assert not inst.CMD_PATH.exists()
    assert not inst.VBS_PATH.exists()
    assert not inst.BASE_DIR.exists()


def test_le_lanceur_ditribue_le_jeton_au_moment_du_tir_sans_l_ecrire(monkeypatch):
    """Aucun jeton dans un fichier : le lanceur lit le trousseau du siege au
    moment ou la tache tourne."""
    monkeypatch.setenv("LOCALAPPDATA", "C:/Users/xx/AppData/Local")
    content = inst.cmd_content("jsboige/CoursIA", "ci-overflow-controller.yml",
                                "jsboige", 15)
    assert "gh auth token --user %GH_USER%" in content
    assert 'set "GH_USER=jsboige"' in content
    assert "gh workflow run %GH_WORKFLOW%" in content
    assert 'set "GH_WORKFLOW=ci-overflow-controller.yml"' in content
    assert "-f min_interval=%GH_MIN_INTERVAL%" in content
    assert 'set "GH_MIN_INTERVAL=15"' in content
    assert "ghp_" not in content
    assert "github_pat_" not in content


def test_le_lanceur_vbs_ferme_la_fenetre_et_remonte_le_code_de_sortie():
    vbs = inst.vbs_content(Path(r"C:/Users/xx/AppData/Local/x/dispatch_overflow.cmd"))
    assert "WScript.Shell" in vbs
    assert ", 0, True)" in vbs
    assert "dispatch_overflow.cmd" in vbs


def test_install_refuse_de_cabler_un_workflow_inexistant(monkeypatch, capsys, tmp_path):
    """Un declencheur cable vers un workflow absent echouerait en silence
    toutes les N minutes : l'installation refuse."""
    monkeypatch.setenv("LOCALAPPDATA", str(tmp_path))
    monkeypatch.setattr(inst, "workflow_exists", lambda repo, wf: (False, "introuvable"))
    monkeypatch.setattr(inst, "_run", lambda cmd, **kw: (_ for _ in ()).throw(
        AssertionError("aucune inscription schtasks quand le workflow est absent")))
    rc = inst.main(["--install"])
    assert rc == 2
    assert "introuvable" in capsys.readouterr().err


def test_la_commande_schtasks_cible_la_tache_nommee():
    command = inst.build_schtasks_install(inst.task_action(), 15, "00:07")
    assert command[0] == "schtasks"
    assert "/TN" in command and inst.TASK_NAME in command
    assert "/ST" in command and "00:07" in command
    # L'action enregistree est le lanceur VBS, pas python.exe en direct.
    assert command[-1].endswith("run_hidden.vbs")


def test_le_declencheur_ne_passe_pas_un_input_que_le_depot_ne_declare_pas():
    """Un input inconnu fait echouer chaque tir : le declencheur ne passe
    que ce que le workflow declare reellement sur le depot."""
    without = inst.cmd_content("jsboige/CoursIA", "ci-overflow-controller.yml",
                               "jsboige", 15, pass_min_interval=False)
    assert "-f min_interval" not in without
    assert "gh workflow run %GH_WORKFLOW% --repo %GH_REPO%" in without
    with_input = inst.cmd_content("jsboige/CoursIA", "ci-overflow-controller.yml",
                                  "jsboige", 15, pass_min_interval=True)
    assert "-f min_interval=%GH_MIN_INTERVAL%" in with_input


def test_les_inputs_sont_lus_dans_le_workflow_du_depot(monkeypatch):
    import base64
    import json

    workflow = (
        "on:\n"
        "  workflow_dispatch:\n"
        "    inputs:\n"
        "      min_interval:\n"
        "        default: '0'\n"
    )
    payload = json.dumps({"content": base64.b64encode(workflow.encode()).decode()})

    class _Proc:
        returncode = 0
        stdout = payload
        stderr = ""

    monkeypatch.setattr(inst, "_run", lambda cmd, **kw: _Proc())
    inputs, reason = inst.workflow_inputs("jsboige/CoursIA", "ci-overflow-controller.yml")
    assert inputs == {"min_interval"}
    assert reason == ""
