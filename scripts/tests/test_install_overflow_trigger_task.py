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
    assert f"/MO {inst.DEFAULT_INTERVAL_MINUTES}" in out
    assert not inst.CMD_PATH.exists()
    assert not inst.VBS_PATH.exists()
    assert not inst.BASE_DIR.exists()


def test_la_cadence_par_defaut_respecte_le_plafond_d_appels_de_gh():
    """La cadence n'est pas une preference, elle est bornee par le cout.

    Mesure du 2026-10-27 : **313 appels `gh` par passage**. Le jeton du
    depot (`github.token`) plafonne a **1 000 appels/h pour le repo**,
    partage avec les autres jobs ; le cron horaire du depot en consomme
    deja 313/h. La minuterie locale ne peut donc pas faire plus d'UN
    passage par heure sans passer au-dessus du plafond (le declencheur
    affamerait l'organe qu'il pilote -- reserve Hermes du 28/10).

    La garde (`min_interval`) reste STRICTEMENT inferieure a la cadence :
    l'ecart se lit sur le dernier passage, run confondu, et le cron du
    depot mesure a :31 -- soit 36 min avant le tic local de :07. Une garde
    egale a la cadence ecarterait ce tic-la.
    """
    assert inst.DEFAULT_INTERVAL_MINUTES >= 60
    assert inst.DEFAULT_MIN_INTERVAL_MINUTES < inst.DEFAULT_INTERVAL_MINUTES


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


# --- #25510 (E2) : l'instrument du declencheur doit voir l'EFFET, et l'ecart
# entre l'artefact installe et son generateur doit etre detectable. ---


def test_le_lanceur_verifie_l_effet_du_declenchement():
    """Le lanceur doit voir l'EFFET, pas son propre code de sortie.

    Mesure du 2026-11-12 (19:07Z, ai-01) : la tache planifiee a rendu
    rc 0, son journal n'a trace que « declenchement », et AUCUN run n'a
    ete cree (0 workflow_dispatch sur le depot apres 18:30Z, les 11
    passages horaires precedents ayant tous produit un run). L'instrument
    qui ne regarde que son code de sortie croit avoir declenche : la
    MINUTERIE peut mourir sans que rien ne le dise.
    """
    content = inst.cmd_content(
        "jsboige/CoursIA", "ci-overflow-controller.yml", "jsboige", 30,
    )
    assert "RUN_BEFORE" in content and "RUN_AFTER" in content
    assert "gh run list --workflow %GH_WORKFLOW%" in content
    assert "EFFET NON CONSTATE" in content
    assert "exit /b 3" in content
    # Le code de sortie du declenchement reste propage tel quel : un refus
    # de l'API n'est pas un « effet non constate ».
    assert "if errorlevel 1 (" in content


def test_le_statut_signale_le_drift_entre_le_lanceur_installe_et_le_genere(
    monkeypatch, tmp_path
):
    """Un lanceur installe derriere son generateur s'ecarte sans bruit.

    Mesure du 2026-11-12 (ai-01) : le lanceur installe ne passait pas
    `min_interval` -- que le generateur ecrit depuis -- et chacune de ses
    20 lignes portait un CR supplementaire ; rien ne le signalait.
    """
    monkeypatch.setattr(inst, "CMD_PATH", tmp_path / "dispatch_overflow.cmd")
    monkeypatch.setattr(inst, "VBS_PATH", tmp_path / "run_hidden.vbs")
    monkeypatch.setattr(
        inst, "workflow_inputs", lambda repo, wf: ({"min_interval"}, ""),
    )
    inst.CMD_PATH.write_text("@echo off\r\nexit /b 0\r\n", encoding="ascii")
    inst.VBS_PATH.write_text("' vbs\r\n", encoding="ascii")
    drifts = inst.launcher_drift(
        "jsboige/CoursIA", "ci-overflow-controller.yml", "jsboige", 30,
    )
    assert drifts, "le drift du lanceur installe n'est pas vu"
    assert any("DIVERGE" in d for d in drifts)


def test_le_statut_ne_signale_pas_de_drift_quand_le_lanceur_est_conforme(
    monkeypatch, tmp_path
):
    monkeypatch.setattr(inst, "CMD_PATH", tmp_path / "dispatch_overflow.cmd")
    monkeypatch.setattr(inst, "VBS_PATH", tmp_path / "run_hidden.vbs")
    monkeypatch.setattr(
        inst, "workflow_inputs", lambda repo, wf: ({"min_interval"}, ""),
    )
    inst.CMD_PATH.write_text(
        inst.cmd_content(
            "jsboige/CoursIA", "ci-overflow-controller.yml", "jsboige", 30,
        ),
        encoding="ascii", newline="",
    )
    inst.VBS_PATH.write_text(
        inst.vbs_content(inst.CMD_PATH), encoding="ascii", newline="",
    )
    assert inst.launcher_drift(
        "jsboige/CoursIA", "ci-overflow-controller.yml", "jsboige", 30,
    ) == []


def test_le_lanceur_ecrit_sans_cr_supplementaire(monkeypatch, tmp_path):
    """Le fichier ecrit doit etre byte-identique au contenu genere.

    `write_text` sans `newline=""` traduit chaque "\\n" en os.linesep et
    ecrit "\\r\\r\\n" : le contenu porte deja ses "\\r\\n" explicites, donc
    chaque ligne prenait un CR de plus (mesure sur l'artefact installe le
    2026-11-12 : 20 lignes sur 20). cmd.exe toleit le resultat, mais
    l'artefact n'etait plus comparable a ce que le generateur declare.
    """
    class _Proc:
        returncode = 0
        stdout = ""
        stderr = ""

    monkeypatch.setattr(inst, "BASE_DIR", tmp_path)
    monkeypatch.setattr(inst, "LOG_DIR", tmp_path / "logs")
    monkeypatch.setattr(inst, "CMD_PATH", tmp_path / "dispatch_overflow.cmd")
    monkeypatch.setattr(inst, "VBS_PATH", tmp_path / "run_hidden.vbs")
    monkeypatch.setattr(inst, "workflow_exists", lambda repo, wf: (True, ""))
    monkeypatch.setattr(
        inst, "workflow_inputs", lambda repo, wf: ({"min_interval"}, ""),
    )
    monkeypatch.setattr(inst, "_run", lambda cmd, **kw: _Proc())
    rc = inst.main(["--install"])
    assert rc == 0
    raw = inst.CMD_PATH.read_bytes()
    assert b"\r\r\n" not in raw
    assert raw.decode("ascii") == inst.cmd_content(
        "jsboige/CoursIA", "ci-overflow-controller.yml", "jsboige", 30,
    )
