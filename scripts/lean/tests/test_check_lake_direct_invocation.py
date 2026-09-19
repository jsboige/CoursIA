"""Tests du garde CI anti-invocation-directe lake (#15666, T4).

Chaque NEGATIVE encode une lecon de calibration mesuree sur le corpus reel
au moment de la naissance du garde : les cinq premieres versions attrapaient
des docstrings, des sondes ``which``, des tests d'appartenance et de la
prose d'erreur -- chacune de ces classes a sa negatif de regression ici.
"""

from __future__ import annotations

import sys
import textwrap
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(REPO_ROOT / "scripts" / "lean"))

import check_lake_direct_invocation as guard  # noqa: E402


def scan_source(src: str, tmp_path: Path) -> list[tuple[int, str, str]]:
    f = tmp_path / "sample.py"
    f.write_text(textwrap.dedent(src), encoding="utf-8")
    return guard.scan_file(f)


@pytest.fixture()
def tmp(tmp_path: Path) -> Path:
    return tmp_path


# --- formes positives ------------------------------------------------------

def test_shape1_list_inline(tmp: Path) -> None:
    out = scan_source("""
        import subprocess
        subprocess.run(["lake", "build"], cwd=p)
    """, tmp)
    assert out and out[0][1] == "lake build"


def test_shape1_string_os_system(tmp: Path) -> None:
    out = scan_source("""
        import os
        os.system("lake build Foo.lean")
    """, tmp)
    assert out


def test_shape1_fstring_prefix(tmp: Path) -> None:
    out = scan_source("""
        import subprocess
        subprocess.run(f"lake build {target}", shell=True)
    """, tmp)
    assert out


def test_shape1_wsl_interposed(tmp: Path) -> None:
    out = scan_source("""
        import subprocess
        subprocess.run(["wsl", "bash", "-lc", "lake env lean x.lean"])
    """, tmp)
    assert out


def test_shape2_command_list_token(tmp: Path) -> None:
    out = scan_source("""
        def resolve(extra):
            return ["lake", *extra], env
    """, tmp)
    assert out and out[0][1] == "jeton lake"


def test_shape2_path_join(tmp: Path) -> None:
    out = scan_source("""
        from pathlib import Path
        lake_exe = Path.home() / ".elan" / "bin" / "lake.exe"
    """, tmp)
    assert out


def test_shape3_command_fragment(tmp: Path) -> None:
    out = scan_source("""
        cmd = f"set -o pipefail; cd {p} && lake build {args} 2>&1 | tail"
    """, tmp)
    assert out and out[0][1] == "fragment f-string"


# --- negatives : chaque classe de FP mesuree sur le corpus ----------------

def test_negative_which_probe(tmp: Path) -> None:
    assert not scan_source("""
        import shutil
        lake = shutil.which("lake")
    """, tmp)


def test_negative_membership_list(tmp: Path) -> None:
    assert not scan_source("""
        if cmd in ["elan", "lean", "lake", "repl"]:
            pass
    """, tmp)


def test_negative_for_iter_probe(tmp: Path) -> None:
    assert not scan_source("""
        import shutil
        for tool in ["lake", "lean"]:
            if shutil.which(tool):
                print(tool)
    """, tmp)


def test_negative_prose_fstring_without_shell_signal(tmp: Path) -> None:
    # Message d'erreur reel de po2026_recover_build.py -- prose, pas commande.
    assert not scan_source("""
        print(f"lake build failed (exit {rc}, elapsed {t})")
    """, tmp)


def test_negative_docstring_mention(tmp: Path) -> None:
    assert not scan_source('''
        """Run ``lake build`` and check sorry count.

        The lake build output feeds the audit.
        """
        def f():
            return 0
    ''', tmp)


def test_lake_version_inline_list_is_flagged(tmp: Path) -> None:
    # Semantique CONSERVATRICE assumee : une liste dont le jeton de tete est
    # ``lake`` est une voie de lancement a sous-commande potentiellement
    # dynamique (la forme exacte de l'incident : ``["lake", *extra_args]``).
    # Une sonde de version inline doit passer par ``which`` (cf negative
    # ci-dessus) ou se documenter dans l'allowlist.
    out = scan_source("""
        import subprocess
        subprocess.run(["lake", "--version"])
    """, tmp)
    assert out and out[0][1] == "jeton lake"


def test_negative_plain_prose_constant(tmp: Path) -> None:
    # Rapport reel de count_code_sorry.py : prose dans une constante simple.
    assert not scan_source("""
        lines.append("These pass lake build + axiom checks but state nothing.")
    """, tmp)


def test_negative_ordinary_subprocess(tmp: Path) -> None:
    assert not scan_source("""
        import subprocess
        subprocess.run(["git", "status"], cwd=p)
    """, tmp)


# --- classification chemins ------------------------------------------------

def test_is_test_path() -> None:
    assert guard._is_test_path("scripts/lean/tests/test_lean_exec.py")
    assert guard._is_test_path("scripts/lean/test_check_grothendieck_readme.py")
    assert not guard._is_test_path("scripts/lean/lean_exec.py")
    assert not guard._is_test_path("MyIA.AI.Notebooks/x/verifiers/lean_rlvr_verifier.py")


# --- verdict end-to-end (main) ---------------------------------------------

def _run_main(tmp: Path, src: str, allowlist: dict, monkeypatch) -> int:
    f = tmp / "orchestrator.py"
    f.write_text(textwrap.dedent(src), encoding="utf-8")
    import json
    al = tmp / "allowlist.json"
    al.write_text(json.dumps(allowlist), encoding="utf-8")
    monkeypatch.setattr(guard, "ALLOWLIST_PATH", al)
    return guard.main([str(f), "--check"])


def test_main_fails_on_new_direct_invocation(tmp: Path, monkeypatch) -> None:
    rc = _run_main(tmp, """
        import subprocess
        subprocess.run(["lake", "build"])
    """, {}, monkeypatch)
    assert rc == 1


def test_main_passes_when_allowlisted(tmp: Path, monkeypatch) -> None:
    rc = _run_main(tmp, """
        import subprocess
        subprocess.run(["lake", "build"])
    """, {str((tmp / "orchestrator.py").as_posix()): "dette documentee"},
        monkeypatch)
    assert rc == 0


def test_main_reports_stale_entry(tmp: Path, monkeypatch, capsys) -> None:
    rc = _run_main(tmp, """
        import subprocess
        subprocess.run(["git", "status"])
    """, {"chemin/migre.py": "deja migre"}, monkeypatch)
    assert rc == 0
    assert "STALE" in capsys.readouterr().out


def test_real_repo_all_violations_allowlisted() -> None:
    """Controle positif sur l'etat reel : le verdict du garde sur main.

    Une nouvelle invocation directe commitee hors allowlist fait echouer CE
    test avant meme de rougir une PR -- le filet se teste lui-meme.
    """
    rc = guard.main(["--all", "--check"])
    assert rc == 0, "violation hors allowlist sur l'arbre courant"
