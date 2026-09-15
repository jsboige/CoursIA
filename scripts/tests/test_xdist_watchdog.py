"""Tests du chien de garde anti-blocage xdist (#16288).

Proprietes sous test, dans l'ordre de ce qu'elles protegent :

1. **Pass-through pur en regime normal** -- le garde recopie la sortie et
   propage le code du fils tel quel. Un garde qui transformerait le verdict
   d'une jambe saine serait pire que le blocage qu'il pretend soigner.
2. **Un vivant n'est pas tue** -- un enfant qui emet regulierement (fils de
   points pytest) traverse une limite d'inactivite sans dommage. C'est le
   garde-fou contre le faux positif, le risque reel d'un detecteur de
   silence.
3. **Un bloque est tue et NOMME** -- la signature mesuree (progression
   ``[99%]`` puis silence, ``node down: gwN``) doit produire un verdict qui
   cite le worker mort et la fenetre de silence, pas seulement un kill.
   C'est le critere d'acceptation de l'issue : le gate nomme aujourd'hui le
   mur, et c'est ce qui fait lire un blocage comme un depassement.
4. **Arme des le demarrage** -- un enfant muet depuis sa naissance (hang de
   collection) est aussi tue : l'armement ne depend pas d'une premiere ligne.

Les enfants sont des ``python -c`` mono-processus : aucun xdist requis
(l'issue note le defaut propre a la classe de runner ; le garde doit etre
testable sans reproduire la mort d'un vrai worker).
"""

from __future__ import annotations

import subprocess
import sys
import textwrap
from pathlib import Path

CI_DIR = Path(__file__).resolve().parents[1] / "ci"
sys.path.insert(0, str(CI_DIR))

import xdist_watchdog as wd  # noqa: E402


def _child(code: str) -> list[str]:
    return [sys.executable, "-c", textwrap.dedent(code)]


def _run_watchdog(argv: list[str], idle_limit: float):
    lines: list[str] = []
    verdicts: list[str] = []

    def echo(line: str) -> None:
        lines.append(line.rstrip("\n"))

    def emit(message: str) -> None:
        verdicts.append(message)

    code = wd.run(argv, idle_limit, echo=echo, emit=emit)
    return code, "\n".join(lines), "\n".join(verdicts)


def test_passthrough_succes_recopie_et_propage():
    code, out, verdict = _run_watchdog(
        _child("""
            for i in range(3):
                print("ligne", i)
            raise SystemExit(0)
        """),
        idle_limit=10.0,
    )
    assert code == 0
    assert "ligne 0" in out and "ligne 2" in out
    assert verdict == ""


def test_passthrough_echec_propage_le_code():
    code, _, verdict = _run_watchdog(
        _child("raise SystemExit(7)"), idle_limit=10.0
    )
    assert code == 7
    assert verdict == ""


def test_vivant_regulier_non_tue():
    # Emet toutes les 0,3 s pendant ~2,4 s avec une limite a 1,0 s :
    # si le garde mesurait n'importe quoi d'autre que le silence de
    # sortie, il tuerait ici.
    code, out, verdict = _run_watchdog(
        _child("""
            import time
            for i in range(8):
                print("progress", i, flush=True)
                time.sleep(0.3)
            raise SystemExit(0)
        """),
        idle_limit=1.0,
    )
    assert code == 0
    assert "XDIST-WATCHDOG" not in out
    assert verdict == ""


def test_bloque_apres_progression_tue_et_nomme_le_worker():
    # La signature exacte de l'issue : [99%], node down gw3, puis silence.
    code, out, verdict = _run_watchdog(
        _child("""
            print("....s....s.. [ 99%]", flush=True)
            print("[gw3] node down: Not properly terminated", flush=True)
            import time
            time.sleep(300)
        """),
        idle_limit=1.0,
    )
    assert code == wd.EXIT_BLOCKED
    assert "BLOQUE" in verdict
    assert "gw3" in verdict
    assert "99%" in verdict
    assert "limite 1 s" in verdict
    assert "XDIST-WATCHDOG" not in out  # le verdict ne pollue pas la sortie pilote


def test_bloque_muet_des_la_naissance_tue_aussi():
    # Hang de collection : aucune ligne jamais emise. Le garde doit etre
    # arme des le demarrage, pas apres une premiere ligne.
    code, out, verdict = _run_watchdog(
        _child("import time; time.sleep(300)"),
        idle_limit=1.0,
    )
    assert code == wd.EXIT_BLOCKED
    assert "BLOQUE" in verdict
    # Verdict honnete : aucun marqueur gwN vu.
    assert "aucun marqueur" in verdict
    assert "aucune ligne de progression vue" in verdict


def test_replacing_crashed_worker_nomme_aussi():
    # Variante du run 34955819329 : remplacement effectif de gw3, mort de
    # gw4 47 s plus tard -- le marqueur "replacing crashed worker" doit
    # lui aussi nommer le worker dans le verdict.
    code, out, verdict = _run_watchdog(
        _child("""
            print("..... [ 97%]", flush=True)
            print("replacing crashed worker gw4", flush=True)
            import time
            time.sleep(300)
        """),
        idle_limit=1.0,
    )
    assert code == wd.EXIT_BLOCKED
    assert "gw4" in verdict


def test_deux_workers_morts_tous_nommes():
    code, out, verdict = _run_watchdog(
        _child("""
            print("[gw3] node down: Not properly terminated", flush=True)
            print("[gw4] node down: Not properly terminated", flush=True)
            print(".. [ 99%]", flush=True)
            import time
            time.sleep(300)
        """),
        idle_limit=1.0,
    )
    assert code == wd.EXIT_BLOCKED
    assert "gw3" in verdict and "gw4" in verdict


def test_main_mappe_exit_bloque_vers_1(capsys):
    # En CLI, le code 3 (interne, distinct pour le triage) se mappe en 1 :
    # la CI ne doit pas distinguer "bloque" d'un echec par le code seul,
    # mais par le verdict -- les ##[error] annotent le job.
    rc = wd.main(["--idle-limit", "0.5", "--",
                  sys.executable, "-c", "import time; time.sleep(300)"])
    captured = capsys.readouterr()
    assert rc == 1
    assert "XDIST-WATCHDOG" in captured.out


def test_regex_marqueurs():
    assert wd.NODE_DOWN_RE.search("[gw3] node down: Not properly terminated")
    assert not wd.NODE_DOWN_RE.search(".... [ 42%]")
    assert wd.REPLACING_RE.search(
        "gw3 replacing crashed worker gw3").group(1) == "gw3"
    assert wd.PROGRESS_RE.search("....ss... [ 99%]")
    assert not wd.PROGRESS_RE.search("[gw3] node down")


def test_kill_tree_posix_fallback_mono_processus():
    # Sur Windows (et en fallback POSIX), le kill vise au minimum le fils
    # direct : le wrapper ne doit pas survivre a son propre kill.
    proc = subprocess.Popen(
        [sys.executable, "-c", "import time; time.sleep(300)"],
        stdout=subprocess.PIPE,
    )
    try:
        wd._kill_tree(proc)
        proc.wait(timeout=15)
        assert proc.poll() is not None
    finally:
        if proc.poll() is None:
            proc.kill()
