"""Tests hermetiques de l'installateur merge_ready (Q40) -- aucun schtasks reel.

La discipline UAC du depot exige que le dry-run imprime la commande schtasks
exacte SANS l'executer : le test verifie les deux moities (la commande est
imprimee, aucun sous-processus n'est lance). Depuis le lanceur masque
(audit de flotte 2026-09-24), le dry-run couvre AUSSI le contenu du .vbs,
sans jamais l'ecrire.
"""

import importlib.util
import subprocess
import sys
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
INSTALLER_PATH = HERE.parent / "coordination" / "install_merge_ready_task.py"
_spec = importlib.util.spec_from_file_location(
    "install_merge_ready_task_under_test", INSTALLER_PATH
)
imod = importlib.util.module_from_spec(_spec)
sys.modules["install_merge_ready_task_under_test"] = imod
_spec.loader.exec_module(imod)


def _redirect_cablage(monkeypatch, tmp_path):
    """Pointe LOG_DIR/VBS_PATH sous tmp_path : aucun test d'ecriture ne
    touche le vrai %LOCALAPPDATA% de la machine."""
    base = tmp_path / "cablage"
    monkeypatch.setattr(imod, "LOG_DIR", base / "logs")
    monkeypatch.setattr(imod, "VBS_PATH", base / "run_hidden.vbs")
    return base


def test_build_schtasks_toutes_les_20_minutes():
    # Adapte (audit de flotte 2026-09-24) : ce test affirmait que le /TR
    # executait python.exe (install_merge_ready_task.py --run) ; l'action
    # est desormais wscript + lanceur VBS, la commande python vit dans le
    # .vbs (voir test_vbs_...).
    cmd = imod.build_schtasks_install(imod.task_action(), 20)
    assert cmd[0:3] == ["schtasks", "/Create", "/F"]
    assert cmd[cmd.index("/TN") + 1] == imod.TASK_NAME
    assert cmd[cmd.index("/SC") + 1] == "MINUTE"
    assert cmd[cmd.index("/MO") + 1] == "20"
    tr = cmd[cmd.index("/TR") + 1]
    assert "wscript.exe" in tr
    assert "//B" in tr and "//Nologo" in tr
    assert "run_hidden.vbs" in tr


def test_tr_quote_chaque_element_pas_la_ligne_entiere():
    # Regression mesuree le 2026-09-24 : /TR "python.exe script.py --run ..."
    # enregistrait la ligne ENTIERE comme nom d'executable ; la tache echouait
    # a chaque tour avec 0x80070002 sans rien journaliser.
    cmd = [r"C:\Program Files\Py\python.exe", r"D:\repo\x.py", "--run"]
    line = imod.build_schtasks_install(cmd, 20)
    tr = line[line.index("/TR") + 1]
    assert tr == r'"C:\Program Files\Py\python.exe" D:\repo\x.py --run'
    assert tr != '"' + " ".join(cmd) + '"'


def test_vbs_masque_la_commande_et_remonte_le_code_de_sortie(tmp_path):
    # Un repo AVEC espace force list2cmdline a quoter : les guillemets
    # doivent etre doubles dans le literal VBScript.
    repo = tmp_path / "repo avec espace"
    content = imod.vbs_content(repo)
    cmdline = subprocess.list2cmdline(imod.task_command(repo))
    escaped = cmdline.replace('"', '""')
    assert f'"{escaped}"' in content
    assert ", 0, True)" in content
    assert "WScript.Quit" in content
    content.encode("ascii")  # wscript lit les .vbs en ANSI


def test_vbs_refuse_une_commande_non_ascii(tmp_path):
    # Un .vbs ANSI portant un accent casserait la ligne de commande
    # silencieusement : refus fort plutot que lanceur casse.
    accent = chr(233)  # 'e' accentue
    with pytest.raises(ValueError, match="ASCII"):
        imod.vbs_content(tmp_path / ("depot" + accent))


def test_dry_run_imprime_la_commande_sans_l_executer(tmp_path, capsys, monkeypatch):
    def boom(cmd, **kw):
        raise AssertionError(
            "aucun sous-processus ne doit etre lance en --dry-run : "
            + str(cmd)
        )

    monkeypatch.setattr(imod, "_run", boom)
    monkeypatch.setattr(imod.subprocess, "run", boom)
    base = _redirect_cablage(monkeypatch, tmp_path)
    rc = imod.main(["--dry-run", "--repo", str(tmp_path / "repo")])
    out = capsys.readouterr().out
    assert rc == 0
    assert "schtasks" in out
    assert "/Create" in out
    assert "/SC" in out and "MINUTE" in out
    assert "/MO" in out and " 20" in out
    assert "DRY-RUN" in out
    # le /TR cible wscript (pas python.exe), et le contenu VBS est imprime
    assert "wscript.exe" in out and "//B" in out and "//Nologo" in out
    assert "run_hidden.vbs" in out
    assert ", 0, True)" in out and "WScript.Quit" in out
    assert "install_merge_ready_task.py" in out and "--run" in out
    # RIEN n'est ecrit : ni le lanceur, ni meme son repertoire
    assert not (base / "run_hidden.vbs").exists()
    assert not base.exists()


def test_install_refuse_organe_absent(tmp_path, capsys, monkeypatch):
    def boom(cmd, **kw):
        raise AssertionError("un depot vide ne doit jamais atteindre schtasks")

    monkeypatch.setattr(imod, "_run", boom)
    _redirect_cablage(monkeypatch, tmp_path)
    repo = tmp_path / "vide"  # sans scripts/coordination/merge_ready.py
    rc = imod.main(["--install", "--repo", str(repo)])
    assert rc == 2
    assert "REFUSE" in capsys.readouterr().err
    assert not imod.VBS_PATH.exists()


class _Res:
    def __init__(self, rc=0, out="", err=""):
        self.returncode, self.stdout, self.stderr = rc, out, err


def _scripted(answers):
    calls = []

    def fake(cmd, **kw):
        calls.append(cmd)
        for key, res in answers:
            if key in cmd:
                return res
        return _Res()

    return fake, calls


def test_install_ecrit_le_vbs_puis_enregistre(tmp_path, capsys, monkeypatch):
    repo = tmp_path / "repo"
    organ = repo / "scripts" / "coordination" / "merge_ready.py"
    organ.parent.mkdir(parents=True)
    organ.write_text("# stub d'organe\n", encoding="ascii")
    base = _redirect_cablage(monkeypatch, tmp_path)
    seen = {}

    def fake(cmd, **kw):
        if "schtasks" in cmd:
            seen["tr"] = cmd[cmd.index("/TR") + 1]
            # le lanceur doit exister AVANT l'inscription : la tache ne
            # doit jamais pointer vers un fichier absent
            seen["vbs_premier"] = imod.VBS_PATH.exists()
        return _Res()

    monkeypatch.setattr(imod, "_run", fake)
    rc = imod.main(["--install", "--repo", str(repo)])
    assert rc == 0
    vbs = base / "run_hidden.vbs"
    assert vbs.is_file()
    content = vbs.read_text(encoding="ascii")
    assert "install_merge_ready_task.py" in content and "--run" in content
    assert ", 0, True)" in content and "WScript.Quit" in content
    assert seen["vbs_premier"] is True
    assert "wscript.exe" in seen["tr"]
    assert "//B" in seen["tr"] and "run_hidden.vbs" in seen["tr"]
    assert "python" not in seen["tr"].lower()


def test_uninstall_supprime_tache_et_lanceur(tmp_path, capsys, monkeypatch):
    base = _redirect_cablage(monkeypatch, tmp_path)
    base.mkdir(parents=True)
    imod.VBS_PATH.write_text("' stub\n", encoding="ascii")
    fake, calls = _scripted([])
    monkeypatch.setattr(imod, "_run", fake)
    rc = imod.main(["--uninstall"])
    assert rc == 0
    assert any("/Delete" in c for c in calls)
    assert not imod.VBS_PATH.exists()
    assert "lanceur supprime" in capsys.readouterr().out


def test_uninstall_echoue_garde_le_lanceur(tmp_path, monkeypatch):
    # si schtasks /Delete echoue, la tache vit encore : son lanceur aussi.
    base = _redirect_cablage(monkeypatch, tmp_path)
    base.mkdir(parents=True)
    imod.VBS_PATH.write_text("' stub\n", encoding="ascii")
    fake, _ = _scripted([("/Delete", _Res(rc=1, err="acces refuse"))])
    monkeypatch.setattr(imod, "_run", fake)
    rc = imod.main(["--uninstall"])
    assert rc == 2
    assert imod.VBS_PATH.exists()


def test_sync_repo_refuse_hors_main(tmp_path, monkeypatch):
    fake, calls = _scripted([("rev-parse", _Res(out="feat/x"))])
    monkeypatch.setattr(imod, "_run", fake)
    ok, msg = imod.sync_repo(tmp_path)
    assert not ok and "pas sur main" in msg
    assert not any("fetch" in c or "merge" in c for c in calls)


def test_sync_repo_siege_detache_avance_sur_origin_main(tmp_path, monkeypatch):
    # Le worktree dedie d'ai-01 ne peut pas porter `main` (tenue par le
    # checkout principal) : il est detache, et c'est son etat nominal.
    fake, calls = _scripted([("rev-parse", _Res(out="HEAD"))])
    monkeypatch.setattr(imod, "_run", fake)
    ok, _ = imod.sync_repo(tmp_path)
    assert ok
    assert any("fetch" in c for c in calls)
    assert any("--is-ancestor" in c for c in calls)
    assert any("checkout" in c and "--detach" in c for c in calls)
    assert not any("--ff-only" in c for c in calls)


def test_sync_repo_siege_detache_refuse_commits_locaux(tmp_path, monkeypatch):
    # HEAD detache hors d'origin/main : des commits locaux seraient abandonnes.
    fake, calls = _scripted(
        [("rev-parse", _Res(out="HEAD")), ("--is-ancestor", _Res(rc=1))]
    )
    monkeypatch.setattr(imod, "_run", fake)
    ok, msg = imod.sync_repo(tmp_path)
    assert not ok and "is-ancestor" in msg
    assert not any("checkout" in c for c in calls)


def test_sync_repo_refuse_depot_modifie(tmp_path, monkeypatch):
    fake, calls = _scripted(
        [("rev-parse", _Res(out="main")), ("status", _Res(out=" M scripts/x.py"))]
    )
    monkeypatch.setattr(imod, "_run", fake)
    ok, msg = imod.sync_repo(tmp_path)
    assert not ok and "modifications" in msg
    assert not any("merge" in c for c in calls)


def test_sync_repo_fast_forward_sur_main(tmp_path, monkeypatch):
    fake, calls = _scripted([("rev-parse", _Res(out="main"))])
    monkeypatch.setattr(imod, "_run", fake)
    ok, _ = imod.sync_repo(tmp_path)
    assert ok
    assert any("fetch" in c for c in calls)
    assert any("--ff-only" in c for c in calls)


def test_tache_lance_l_installateur_du_depot_cible(tmp_path):
    # La tache doit executer le wrapper du depot synchronise, pas celui du
    # checkout d'ou l'installation a ete lancee.
    cmd = imod.task_command(tmp_path)
    assert cmd[1] == str(tmp_path / "scripts" / "coordination" / "install_merge_ready_task.py")
