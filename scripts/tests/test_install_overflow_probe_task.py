from __future__ import annotations

import sys
from pathlib import Path

CI_DIR = Path(__file__).resolve().parents[1] / "ci"
sys.path.insert(0, str(CI_DIR))

import install_overflow_probe_task as inst  # noqa: E402


def _patch_paths(monkeypatch, tmp_path):
    monkeypatch.setenv("LOCALAPPDATA", str(tmp_path))
    monkeypatch.setattr(inst, "BASE_DIR", tmp_path / "CoursIA" / "overflow_probe")
    monkeypatch.setattr(inst, "LOG_DIR", inst.BASE_DIR / "logs")
    monkeypatch.setattr(inst, "CMD_PATH", inst.BASE_DIR / "dispatch_probe.cmd")
    monkeypatch.setattr(inst, "VBS_PATH", inst.BASE_DIR / "run_hidden.vbs")


def test_le_dry_run_imprime_la_commande_schtasks_exacte_sans_ecrire(monkeypatch, capsys, tmp_path):
    """Discipline UAC : la sortie du dry-run precede toute inscription
    schtasks. Il n'ecrit donc RIEN -- pas meme les lanceurs."""
    _patch_paths(monkeypatch, tmp_path)
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


def test_la_cadence_par_defaut_tient_le_contrat_de_latence_de_l_issue():
    """#26939 : deux passages sonde a moins de 15 min d'ecart. Le cron de
    depot ('4-59/12') fait 12 min d'ecart max ; la minuterie locale DOIT
    tenir le meme contrat, sinon elle ne remplace pas le cron non livre.
    Et elle reste sous la cadence disputee : le budget au repos est
    5 passages/h x 2 appels = 10 appels/h, negligeable devant le plafond
    de 1 000 appels/h."""
    assert inst.DEFAULT_INTERVAL_MINUTES < 15
    assert inst.DEFAULT_INTERVAL_MINUTES >= 10


def test_la_phase_de_depart_ne_collisionne_avec_aucun_tic_existant():
    """:04 (sonde locale) ne touche ni :07 (declencheur local du controleur),
    ni :31 (cron du controleur), ni :00/:30 (jitter de la flotte)."""
    assert inst.DEFAULT_START.endswith("04")
    assert inst.DEFAULT_START.startswith("00:")


def test_le_lanceur_ditribue_le_jeton_au_moment_du_tir_sans_l_ecrire(monkeypatch):
    """Aucun jeton dans un fichier : le lanceur lit le trousseau du siege au
    moment ou la tache tourne."""
    monkeypatch.setenv("LOCALAPPDATA", "C:/Users/xx/AppData/Local")
    content = inst.cmd_content(Path("D:/dev/CoursIA"), "python", "jsboige/CoursIA", "jsboige")
    assert "gh auth token --user %GH_USER%" in content
    assert 'set "GH_USER=jsboige"' in content
    # La sonde est jouee DEPUIS le checkout du siege, en sortie JSON journalisee.
    assert "ci_overflow_probe.py" in content
    assert "--json" in content
    # Aucun jeton ecrit.
    assert "ghp_" not in content
    assert "github_pat_" not in content


def test_le_lanceur_pose_le_jeton_dans_l_environ_pas_sur_la_ligne_de_commande(monkeypatch):
    """L'organe lit GH_TOKEN (option --token-env par defaut) : le lanceur le
    pose par environment herite, jamais en argument de ligne de commande
    (il y serait visible de la table des processus)."""
    monkeypatch.setenv("LOCALAPPDATA", "C:/Users/xx/AppData/Local")
    content = inst.cmd_content(Path("D:/dev/CoursIA"), "python", "jsboige/CoursIA", "jsboige")
    assert "--token-env" not in content
    assert "GH_TOKEN=%GH_TOKEN%" not in content  # l'env herite suffit


def test_le_lanceur_vbs_ferme_la_fenetre_et_remonte_le_code_de_sortie():
    vbs = inst.vbs_content(Path(r"C:/Users/xx/AppData/Local/x/dispatch_probe.cmd"))
    assert "WScript.Shell" in vbs
    assert ", 0, True)" in vbs
    assert "dispatch_probe.cmd" in vbs


def test_install_refuse_un_checkout_inutilisable(monkeypatch, capsys, tmp_path):
    """Une minuterie cablee vers un organe absent echouerait en silence
    toutes les 12 minutes : l'installation refuse."""
    _patch_paths(monkeypatch, tmp_path)
    monkeypatch.setattr(inst, "probe_usable", lambda checkout: (False, "organe absent"))
    monkeypatch.setattr(inst, "_run", lambda cmd, **kw: (_ for _ in ()).throw(
        AssertionError("aucune inscription schtasks quand l'organe est absent")))
    rc = inst.main(["--install"])
    assert rc == 2
    assert "organe absent" in capsys.readouterr().err


def test_probe_usable_exige_les_deux_organes(tmp_path):
    """La sonde importe le module du controleur au moment de l'execution :
    un checkout sans `ci_overflow_controller.py` echouerait aussi."""
    ok, reason = inst.probe_usable(tmp_path)
    assert not ok and "ci_overflow_probe.py" in reason
    (tmp_path / "scripts" / "ci").mkdir(parents=True)
    (tmp_path / "scripts" / "ci" / "ci_overflow_probe.py").write_text("# probe")
    ok, reason = inst.probe_usable(tmp_path)
    assert not ok and "ci_overflow_controller.py" in reason
    (tmp_path / "scripts" / "ci" / "ci_overflow_controller.py").write_text("# ctl")
    ok, reason = inst.probe_usable(tmp_path)
    assert ok and reason == ""


def test_la_commande_schtasks_cible_la_tache_nommee():
    command = inst.build_schtasks_install(inst.task_action(), 12, "00:04")
    assert command[0] == "schtasks"
    assert "/TN" in command and inst.TASK_NAME in command
    assert "/ST" in command and "00:04" in command
    # L'action enregistree est le lanceur VBS, pas python.exe en direct.
    assert command[-1].endswith("run_hidden.vbs")


def test_le_statut_signale_le_drift_entre_le_lanceur_installe_et_le_genere(
    monkeypatch, capsys, tmp_path
):
    """Un lanceur installe qui derive du generateur doit etre nomme -- le
    defaut mesure le 2026-11-12 sur le declencheur du controleur."""
    _patch_paths(monkeypatch, tmp_path)
    inst.BASE_DIR.mkdir(parents=True)
    stale = inst.cmd_content(Path("D:/old"), "python", "jsboige/CoursIA", "jsboige")
    inst.CMD_PATH.write_text(stale, encoding="ascii", newline="")
    monkeypatch.setattr(inst, "_run", lambda cmd, **kw: type(
        "P", (), {"returncode": 0, "stdout": "tache presente", "stderr": ""})())
    rc = inst.main(["--status", "--checkout", str(tmp_path)])
    out = capsys.readouterr().out
    assert rc == 3
    assert "DIVERGE" in out
    assert "remedy : python scripts/ci/install_overflow_probe_task.py --install" in out


def test_le_statut_ne_signale_pas_de_drift_quand_le_lanceur_est_conforme(
    monkeypatch, capsys, tmp_path
):
    _patch_paths(monkeypatch, tmp_path)
    inst.BASE_DIR.mkdir(parents=True)
    inst.CMD_PATH.write_text(
        inst.cmd_content(str(tmp_path), "python", "jsboige/CoursIA", "jsboige"),
        encoding="ascii",
        newline="",
    )
    inst.VBS_PATH.write_text(inst.vbs_content(inst.CMD_PATH), encoding="ascii", newline="")
    monkeypatch.setattr(inst, "_run", lambda cmd, **kw: type(
        "P", (), {"returncode": 0, "stdout": "tache presente", "stderr": ""})())
    rc = inst.main(["--status", "--checkout", str(tmp_path)])
    assert rc == 0
    assert "conformes au generateur" in capsys.readouterr().out


def test_le_lanceur_ecrit_sans_cr_supplementaire(monkeypatch, tmp_path):
    """Defaut mesure le 2026-11-12 : sans `newline=""`, chaque "\\n" devient
    os.linesep et le fichier porte "\\r\\r\\n" -- toleré par cmd.exe, mais
    plus byte-identique a ce que le generateur declare."""
    _patch_paths(monkeypatch, tmp_path)
    inst.BASE_DIR.mkdir(parents=True)
    monkeypatch.setattr(inst, "probe_usable", lambda checkout: (True, ""))
    import subprocess as sp

    monkeypatch.setattr(
        sp, "run",
        lambda cmd, **kw: type("P", (), {"returncode": 0, "stdout": "", "stderr": ""})(),
    )
    rc = inst.main(["--install", "--checkout", str(tmp_path)])
    assert rc == 0
    raw = inst.CMD_PATH.read_bytes()
    assert b"\r\r\n" not in raw
    assert raw.count(b"\r\n") == raw.count(b"\n")


def test_le_dry_run_l_emporte_sur_install(monkeypatch, capsys, tmp_path):
    """Defaut mesure le 2026-11-12 sur le declencheur du controleur : un
    drapeau dry-run mort qui installait quand meme. Ici, l'ordre des tests
    garantit que --dry-run --install n'installe pas."""
    _patch_paths(monkeypatch, tmp_path)
    monkeypatch.setattr(inst, "probe_usable", lambda checkout: (True, ""))
    rc = inst.main(["--dry-run", "--install", "--checkout", str(tmp_path)])
    assert rc == 0
    assert not inst.CMD_PATH.exists()
    assert not inst.VBS_PATH.exists()
    assert "DRY-RUN" in capsys.readouterr().out
