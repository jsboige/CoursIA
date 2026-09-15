"""Chien de garde anti-blocage pour ``Scripts Tests (CPU)`` (#16288).

Defaut mesure (issue #16288, cinq runs, horodatages UTC du log) : quand un
worker xdist meurt (``[gwN] node down: Not properly terminated``), la jambe
ne repart jamais. La derniere ligne de progression tombe 3,3 a 5,5 min apres
le demarrage du job -- dans le CORPS de la distribution, souvent ``[99%]``
-- puis **14 a 17 min de silence total** jusqu'a l'annulation au plafond.
Le master n'attend pas du travail : il attend des workers morts. Aucun test
n'est en cours, donc ``pytest-timeout`` (borne par TEST) ne peut pas tirer,
et le plafond du job ne fait que donner un nom de mur a un blocage.

Ce module est la piste 3 de l'issue -- le chien de garde sur l'ABSENCE de
sortie, le seul qui colle a la signature :

  - il laisse passer la sortie du processus tel quel (aucune transformation
    en regime normal, le verdict CI ne change pas d'un bit) ;
  - il horodate chaque ligne en interne et memorise la derniere ligne de
    progression pytest (motif ``[ NN%]``) ;
  - il collecte en vol les marqueurs de mort xdist (``node down`` /
    ``replacing crashed worker``) avec le nom du worker ;
  - si la sortie se tait plus de ``--idle-limit`` secondes : il tue le
    groupe de processus et echoue avec un verdict qui NOMME LE WORKER MORT
    et la fenetre de silence -- pas seulement le mur. C'est le critere
    d'acceptance de l'issue : un run bloque doit echouer vite, en disant
    pourquoi.

Pistes rejetees, pour memoire (detail dans #16288) :

  - ``pytest-timeout`` + ``--timeout`` : borne un TEST qui bloque ; ici
    aucun test n'est en cours, le master attend des workers morts.
  - ``timeout-minutes`` d'etape : borne le blocage mais le verdict nomme
    toujours le mur ; de plus le plafond 20->30 appartient a #16087.
  - ``--max-worker-restart`` : politique de redemarrage, pas un detecteur
    de silence ; le run #34955819329 montre un remplacement EFFECTIF
    (``replacing crashed worker gw3``) suivi de la mort de gw4 47 s plus
    tard -- la jambe est restee bloquee malgre le remplacement.

Le choix de ``--idle-limit 480`` (defaut) est arithmetique : un run bloque
echoue a (derniere progression ~3,3-5,5 min) + 480 s, soit **11,5 a 13,5 min
< 17,4 min** (plus long succes legitime mesure par #16087) ; et un faux
positif exigerait **8 min de silence global** alors que 4 workers emettent
des points en continu sous ``-q`` -- la seule fenetre legitime comparable
serait un unique test final de 8 min muet sur les 4 workers a la fois, absent
des mesures. Le seuil reste un parametre : la CI peut le resserrer.

Limites honnetes :

  - ne diagnostique PAS pourquoi les workers meurent (OOM runner, module,
    interaction loadscope) -- l'issue le laisse ouvert et ce garde ne le
    tranche pas ;
  - le kill de groupe est POSIX (session dediee + ``os.killpg``). Sous
    Windows le kill ne vise que le processus fils direct -- suffisant pour
    les tests (enfants mono-processus), non deploye en CI (jambe ubuntu).

Usage :

  python scripts/ci/xdist_watchdog.py --idle-limit 480 -- pytest <paths> \\
      -n 4 --dist loadscope --tb=short -q
"""

from __future__ import annotations

import argparse
import os
import re
import signal
import subprocess
import sys
import threading
import time

# Marqueurs de mort xdist, tels qu'ils apparaissent dans le log du job
# (run 34955819329 : "gw3 ... node down: Not properly terminated" puis
# "replacing crashed worker gw3" ; l'un ou l'autre nomme un worker mort).
NODE_DOWN_RE = re.compile(r"\[(gw\d+)\][^\n]*node down", re.IGNORECASE)
REPLACING_RE = re.compile(r"replacing crashed worker (gw\d+)", re.IGNORECASE)

# Derniere progression pytest sous -q : "[ 57%]" en fin de ligne de points.
PROGRESS_RE = re.compile(r"\[\s?\d+%\]")

VERDICT_PREFIX = "XDIST-WATCHDOG"

EXIT_BLOCKED = 3  # distinct des exits pytest usuels pour le triage post-mortem


class _StreamState:
    """Etat partage entre le fil de lecture et la boucle de surveillance."""

    def __init__(self) -> None:
        self.lock = threading.Lock()
        self.last_output = time.monotonic()
        self.last_progress_line: str | None = None
        self.dead_workers: list[str] = []
        self.line_count = 0

    def record(self, line: str) -> None:
        now = time.monotonic()
        with self.lock:
            self.last_output = now
            self.line_count += 1
            if PROGRESS_RE.search(line):
                self.last_progress_line = line.strip()
            m = NODE_DOWN_RE.search(line)
            if m and m.group(1) not in self.dead_workers:
                self.dead_workers.append(m.group(1))
            m = REPLACING_RE.search(line)
            if m and m.group(1) not in self.dead_workers:
                self.dead_workers.append(m.group(1))

    def idle_for(self) -> float:
        with self.lock:
            return time.monotonic() - self.last_output


def _pump(stream, state: _StreamState, echo) -> None:
    """Lit les lignes d'un pipe du fils, les horodate et les recopie."""
    # Sentinelle en BYTES : le pipe est binaire (Popen sans text=True),
    # et b"" == "" est faux -- un sentinelle str ferait boucler le fil
    # a l'infini apres l'EOF, inondant l'echo de lignes vides.
    for raw in iter(stream.readline, b""):
        line = raw.decode("utf-8", errors="replace") if isinstance(raw, bytes) else raw
        state.record(line)
        echo(line)
    try:
        stream.close()
    except OSError:
        pass


def _kill_tree(proc: subprocess.Popen) -> None:
    """Tue le fils et, sur POSIX, tout son groupe (master + workers xdist)."""
    if os.name == "posix":
        try:
            os.killpg(proc.pid, signal.SIGKILL)
            return
        except (ProcessLookupError, PermissionError, OSError):
            pass
    proc.kill()


def _emit(message: str) -> None:
    """Verdict sur stdout ET stderr : le log CI garde l'un des deux quoi qu'il arrive."""
    sys.stdout.write(message + "\n")
    sys.stdout.flush()
    sys.stderr.write(message + "\n")
    sys.stderr.flush()


def run(argv: list[str], idle_limit: float, echo=None, emit=None) -> int:
    """Execute ``argv`` sous surveillance ; renvoie le code de sortie a propager.

    En regime normal : pass-through pur (sortie recopiee, code du fils
    renvoye tel quel). En blocage : kill + verdict qui nomme le worker mort,
    renvoie ``EXIT_BLOCKED``. ``echo`` recopie la sortie du fils, ``emit``
    publie le verdict (stdout+stderr par defaut, pour le log CI).
    """
    if echo is None:
        def echo(line: str) -> None:
            sys.stdout.write(line if line.endswith("\n") else line + "\n")
            sys.stdout.flush()

    if emit is None:
        emit = _emit

    state = _StreamState()
    kwargs: dict = {}
    if os.name == "posix":
        kwargs["start_new_session"] = True
    proc = subprocess.Popen(
        argv,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        bufsize=-1,
        **kwargs,
    )
    started = time.monotonic()

    reader = threading.Thread(
        target=_pump, args=(proc.stdout, state, echo), daemon=True
    )
    reader.start()

    try:
        while True:
            if proc.poll() is not None:
                break
            idle = state.idle_for()
            if idle > idle_limit:
                _verdict_blocked(state, idle, idle_limit, started, emit)
                _kill_tree(proc)
                proc.wait(timeout=30)
                return EXIT_BLOCKED
            time.sleep(0.5)
    finally:
        # Le fils est mort ou tue : le lecteur atteint l'EOF, on ne bloque pas
        # la sortie du wrapper sur un pipe theoriquement ouvert.
        reader.join(timeout=10)

    return proc.returncode if proc.returncode is not None else EXIT_BLOCKED


def _verdict_blocked(state: _StreamState, idle: float, idle_limit: float,
                      started: float, emit=_emit) -> None:
    wall = time.monotonic() - started
    progress = state.last_progress_line or "(aucune ligne de progression vue)"
    workers = ", ".join(state.dead_workers) if state.dead_workers else \
        "aucun marqueur gwN (node down / replacing crashed worker) vu -- " \
        "blocage hors de la classe mesuree dans #16288, fenetre de silence " \
        "a investiguer telle quelle"
    emit(f"##[error]{VERDICT_PREFIX}: BLOQUE -- silence de sortie depuis "
         f"{idle:.0f} s (limite {idle_limit:.0f} s), mur du job non atteint")
    emit(f"##[error]{VERDICT_PREFIX}: derniere progression pytest : "
         f"\"{progress}\" ; {state.line_count} lignes emises au total ; "
         f"wall du wrapper {wall:.0f} s")
    emit(f"##[error]{VERDICT_PREFIX}: workers morts : {workers}")
    emit(f"##[error]{VERDICT_PREFIX}: le master etait vivant mais n'attendait "
         f"pas du travail -- signature #16288 ; kill du groupe de processus")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Execute une commande et la tue si sa sortie se tait "
                    "(workers xdist morts, cf #16288).")
    parser.add_argument("--idle-limit", type=float, default=480.0,
                        help="secondes de silence de sortie tolerees avant "
                             "kill + verdict (defaut 480)")
    parser.add_argument("command", nargs=argparse.REMAINDER,
                        help="commande a surveiller, apres '--'")
    args = parser.parse_args(argv)

    cmd = args.command
    if cmd and cmd[0] == "--":
        cmd = cmd[1:]
    if not cmd:
        parser.error("aucune commande a surveiller")

    code = run(cmd, args.idle_limit)
    if code == EXIT_BLOCKED:
        return 1
    return code


if __name__ == "__main__":
    sys.exit(main())
