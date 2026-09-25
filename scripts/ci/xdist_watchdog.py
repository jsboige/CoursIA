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

Mode 2 -- le garde lui-meme tuait un run sain (run 35276661841, PR #16240,
attempt 2, 2026-09-17 23:27Z) : en fin de parcours sous ``-q``, pytest
ecrit ses points de test SANS saut de ligne tant que la ligne de ~72
caracteres n'est pas pleine. Le fil de lecture, base sur ``readline``,
restait bloque sur le fragment sans ``\\n`` pendant que des octets vivants
traversaient le tube : verdict « silence 480 s ... ``[99%]`` ... workers
morts : gw2 », kill d'un run a 99 % sans echec -- et le flush d'EOF du
kill a laisse la preuve sur le log : une ligne partielle de 43 resultats
emis PENDANT la fenetre dite muette (23:19:06 -> 23:27:07). Le master
n'etait pas bloque, il finissait la queue (tests de queue lents, puis
re-execution du lot du worker remplace). Correctif : la fraicheur se
mesure desormais par OCTET lu (``os.read`` par chunks, lignes
reconstituees en interne), pas par ligne complete. Un run qui emet ne
peut plus etre tue ; un blocage reel (zero octet, signature originelle)
l'est toujours.

Une tolerance au pourcentage de fin de parcours (« [95%+] => grace ») a
ete ecarte a dessin : le blocage originel #16288 s'est AUSSI produit a
``[99%]`` -- le pourcentage ne discrimine rien, seul le flux d'octets le
fait.

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

# Prefixe qui fait du verdict une ANNOTATION du check-run, pas seulement une
# ligne de log. C'est la seule surface par laquelle un lecteur -- humain ou
# organe -- peut distinguer une mort de session d'un rouge de contenu : quand
# le garde tue, l'etape `Run tests` conclut `failure` avec l'annotation
# generique "Process completed with exit code 1.", et
# `classify_job_deaths.py` retourne `REAL_STEP_FAILURE` des qu'une etape a
# conclu `failure`, AVANT de lire la moindre annotation.
#
# Mesure 2026-09-21 (job 106258931264, workflow "Scripts Tests (CPU)") : la
# legibilite TIENT -- le check-run porte 8 annotations `XDIST-WATCHDOG`,
# verbatim "XDIST-WATCHDOG: workers morts : gw1". L'organe de triage lit ce
# job comme une mort de parc (signature `Fatal Python error: Aborted` au log,
# aucun `short test summary`), donc par le log -- mais l'annotation est ce que
# voit quiconque n'a que le check-run sous les yeux.
#
# Pourquoi `##[error]` et non `::error::` : le runner GitHub accepte les deux.
# `##[error]` est la forme heritee (Azure DevOps), et elle annote bel et bien
# -- verifie sur le job ci-dessus, ou elle a produit les 8 annotations. Le
# formuler ici pour eviter la "correction" qui consiste a basculer sur
# `::error::` en croyant reparer un dialecte inerte : la mesure dit que les
# deux fonctionnent, donc la bascule serait un changement sans effet.
# En revanche une TROISIEME forme (par ex. `[error]` ou `#error`) n'annoterait
# rien : c'est ce que `test_le_prefixe_est_un_dialecte_du_runner_github` borne.
ANNOTATION_PREFIX = "##[error]"

EXIT_BLOCKED = 3  # distinct des exits pytest usuels pour le triage post-mortem


class _StreamState:
    """Etat partage entre le fil de lecture et la boucle de surveillance."""

    def __init__(self) -> None:
        self.lock = threading.Lock()
        self.last_output = time.monotonic()
        self.last_progress_line: str | None = None
        self.dead_workers: list[str] = []
        self.line_count = 0
        # Forensique mode 2 : des octets sans aucune ligne complete (points
        # de fin de parcours sans \n) sont le signe d'un run VIVANT -- le
        # verdict doit pouvoir les citer apres coup.
        self.byte_count = 0

    def record_bytes(self, nbytes: int) -> None:
        """Fraicheur par OCTET, pas par ligne complete (mode 2).

        Sous ``-q``, les points de test n'emportent pas de ``\\n`` avant
        que la ligne de ~72 caracteres soit pleine : un fil base sur
        ``readline`` ne verrait rien pendant que le run finit sa queue
        (run 35276661841 : 43 resultats emis pendant une fenetre que le
        garde croyait muette). La boucle de surveillance appelle donc
        ceci sur CHAQUE chunk lu du tube.
        """
        if nbytes <= 0:
            return
        with self.lock:
            self.last_output = time.monotonic()
            self.byte_count += nbytes

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


# Taille d'un chunk de lecture du tube. Un seul os.read = un seul appel
# systeme : il retourne des le PREMIER octet disponible (jamais apres un
# remplissage complet ni un \n) -- c'est la propriete qui repare le mode 2.
PIPE_CHUNK_BYTES = 65536


def _pump(stream, state: _StreamState, echo) -> None:
    """Recopie la sortie du fils en mesurant l'activite par OCTET.

    On lit le tube par chunks bruts (``os.read`` sur le fd) et on
    reconstitue les lignes en interne : la fraicheur (``record_bytes``)
    est mise a jour pour CHAQUE chunk, le decoupage en lignes ne sert
    qu'au bookkeeping (progression, workers morts) et a l'echo.

    Pourquoi pas ``readline`` : en fin de parcours ``-q``, pytest ecrit
    ses points SANS saut de ligne -- un readline resterait bloque sur le
    fragment pendant que le run finit sa queue, et le garde tuerait un
    vivant (mode 2, run 35276661841). Un fragment final sans ``\\n``
    n'est recopie qu'a l'EOF (ou au kill), exactement comme la ligne
    partielle de 43 resultats revelee par le flush d'EOF du run cite.
    """
    fd = stream.fileno()
    pending = b""
    while True:
        try:
            chunk = os.read(fd, PIPE_CHUNK_BYTES)
        except OSError:
            break  # tube ferme sous nos pieds : equivaut a l'EOF
        if not chunk:
            break
        state.record_bytes(len(chunk))
        pending += chunk
        while b"\n" in pending:
            raw, pending = pending.split(b"\n", 1)
            line = raw.decode("utf-8", errors="replace") + "\n"
            state.record(line)
            echo(line)
    if pending:
        line = pending.decode("utf-8", errors="replace")
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
    emit(f"{ANNOTATION_PREFIX}{VERDICT_PREFIX}: BLOQUE -- silence de sortie depuis "
         f"{idle:.0f} s (limite {idle_limit:.0f} s), mur du job non atteint")
    emit(f"{ANNOTATION_PREFIX}{VERDICT_PREFIX}: derniere progression pytest : "
         f"\"{progress}\" ; {state.line_count} lignes ({state.byte_count} "
         f"octets) emises au total ; wall du wrapper {wall:.0f} s")
    emit(f"{ANNOTATION_PREFIX}{VERDICT_PREFIX}: workers morts : {workers}")
    emit(f"{ANNOTATION_PREFIX}{VERDICT_PREFIX}: zero octet emis pendant la fenetre "
         f"(ni ligne ni fragment) -- le master etait vivant mais "
         f"n'attendait pas du travail, signature #16288 ; kill du groupe "
         f"de processus")


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
