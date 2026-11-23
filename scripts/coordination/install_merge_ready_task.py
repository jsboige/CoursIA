#!/usr/bin/env python3
r"""Installateur de la tache planifiee merge_ready (Q40, mandat 2026-09-22).

L'organe (scripts/coordination/merge_ready.py) existe mais aucun cycle ne
le rappelle : une prescription en prose ne s'execute pas seule (meme
constat que #14473 pour prune_merged_worktrees). Le cablage est LOCAL :
une tache planifiee Windows toutes les 20 minutes qui lance
``merge_ready.py --apply`` sous l'identite coordinateur (myia-ai-01).

Fenetre masquee (audit de flotte 2026-09-24) : python.exe est un programme
console et le --run spawn des enfants console (git, gh), donc chaque tour
faisait flasher une fenetre noire sur le bureau interactif. L'action de la
tache est desormais wscript.exe sur un lanceur VBS qui execute la commande
en fenetre 0 (masquee) et attend la fin : la console cachee est heritee par
tous les enfants console ; pythonw.exe ne conviendrait pas -- sans console
attachee, chaque enfant ouvrirait sa PROPRE fenetre visible.

Modes :
    --dry-run [--repo PATH] [--interval N]   imprime la commande schtasks
                                              EXACTE et le contenu du
                                              lanceur VBS, sans rien
                                              ecrire ni executer
                                              (discipline UAC : la sortie
                                              du dry-run precede toute
                                              inscription schtasks)
    --install    [--repo PATH] [--interval N] ecrit le lanceur VBS puis
                                              cree la tache (idempotent)
    --status                                      etat de la tache
    --uninstall                                   supprime la tache ET le
                                                  lanceur VBS
    --run                     execute l'organe en --apply (invoque PAR la
                              tache, via le lanceur VBS) : journal
                              horodate, jamais de TTY

Garde : --install REFUSE de cabler --apply si l'organe cible est absent
(installer un cron vers un fichier qui n'existe pas deployerait un echec
silencieux toutes les 20 minutes).

Journal de la tache : %LOCALAPPDATA%\CoursIA\merge_ready\logs\
merge_ready_YYYYMMDD.log ; journal de l'organe :
%LOCALAPPDATA%\CoursIA\merge_ready\journal.jsonl ; lanceur masque :
%LOCALAPPDATA%\CoursIA\merge_ready\run_hidden.vbs.

Pendant un tour, le journal de la tache **avance** : l'enfant est lance
sans buffer (`-u`) et le lanceur ecrit un battement de coeur toutes les
60 s (issue #28005) -- le controle d'hygiene lit l'AGE de ce journal, et un
journal muet pendant une passe de 4 h passait pour muet alors que la passe
vivait.
"""
from __future__ import annotations

import argparse
import datetime as _dt
import importlib.util
import json
import os
import subprocess
import sys
import threading
import time
from pathlib import Path

TASK_NAME = r"CoursIA\merge_ready"
THIS_FILE = Path(__file__).resolve()
LOG_DIR = (
    Path(os.environ.get("LOCALAPPDATA", str(Path.home() / "AppData" / "Local")))
    / "CoursIA"
    / "merge_ready"
    / "logs"
)
# Lanceur masque (audit de flotte 2026-09-24) : wscript y execute la
# commande de la tache en fenetre 0, console heritee par les enfants.
VBS_PATH = LOG_DIR.parent / "run_hidden.vbs"
# Chemin ABSOLU : l'action de la tache ne doit pas dependre du PATH au reveil.
WSH_PATH = (
    Path(os.environ.get("SystemRoot", r"C:\Windows")) / "System32" / "wscript.exe"
)
# Siege coordinateur (ai-01) : un worktree DEDIE a `origin/main`, pas le
# checkout principal. D:\CoursIA est le siege interactif, souvent sur une
# branche de travail : l'organe y executerait le gate et B.0 de CETTE branche,
# pas ceux de `main`. Le worktree dedie ne peut PAS porter la branche `main`
# (git la refuse a un second worktree tant que le checkout principal la
# tient) : il est en HEAD DETACHE, ramene sur origin/main avant chaque tour
# (voir sync_repo). Les autres machines passent --repo explicitement.
DEFAULT_REPO = Path(r"D:\CoursIA-wt-merge-ready")
INTERVAL_MINUTES = 20

#: Cadence du BATTEMENT DE COEUR ecrit dans le journal texte de la tache
#: pendant que l'enfant tourne (issue #28005).
#:
#: Le controle d'hygiene lit l'AGE du journal (`session_hygiene.py` :
#: `last_log.stat().st_mtime`) : un journal qui n'ecrit rien pendant une passe
#: de 4 h passe pour muet alors que la passe vit (mesure du 22/11 :
#: « journal muet depuis 256 min » pendant que `py-spy` montrait la passe
#: dans `mergeable_state_and_head` -> `sleep`).
#:
#: 60 s est assez court pour que l'age du journal reste sous le seuil
#: d'alerte (3 x l'intervalle nominal de 20 min) et assez long pour ne pas
#: ecrire 60 lignes par passe.
HEARTBEAT_S = 60.0

# --- miroir du journal ------------------------------------------------------------
#
# Pourquoi ce miroir existe (mesure du 2026-11-23)
# -------------------------------------------------
# L'organe ecrit son stdout A LA FIN de sa boucle : `merge_ready.py` fait
# `for verdict in results: print(_describe(verdict))` -- une impression par
# PR, mais apres la boucle. Mesure : le run du 23/11 a evalue 191 PRs entre
# 00:36Z et 06:38Z, et le journal de la tache
# (`logs\merge_ready_20261123.log`) en pesait 76 octets a 08:00Z -- les deux
# seules lignes du lanceur (« run start », « depot synchronise »). Les 191
# verdicts etaient pourtant deja dans `journal.jsonl`, une ligne par PR,
# ecrite au fil de l'evaluation.
#
# Autrement dit : le journal de l'organe est en temps reel, le journal de la
# tache ne l'est pas. Un run de six heures ne laisse aucune trace lisible de
# son travail tant qu'il n'est pas fini -- et un run qui n'est jamais fini
# (le budget de duree n'existait pas dans la copie executee) ne laisse rien.
#
# Le miroir lit le journal pendant le run et ecrit UNE LIGNE PAR PR dans le
# journal de la tache, avec la duree de l'evaluation. Il ne touche ni
# l'organe ni son code : il lit ce que l'organe ecrit deja.
#
# Le battement de coeur et le miroir ne se remplacent pas : le battement dit
# que la passe VIT (il ecrit meme quand aucune PR ne se termine), le miroir
# dit ce que la passe FAIT (un verdict par PR, avec sa duree). Un organe de
# fidelite veut les deux.

#: Nom du journal de l'organe, dans le dossier de la tache.
JOURNAL_FILENAME = "journal.jsonl"
#: Delai entre deux scrutations du journal pendant le run (s).
JOURNAL_POLL_S = 5.0
#: Ecart au-dela duquel deux lignes consecutives n'appartiennent plus au
#: meme passage (meme convention que l'organe de duree, `DEFAULT_MAX_GAP_S`).
DEFAULT_MAX_GAP_S = 900.0


def _run(cmd: list[str], **kw) -> subprocess.CompletedProcess:
    return subprocess.run(
        cmd, capture_output=True, text=True, encoding="utf-8",
        errors="replace", **kw
    )


def organ_path(repo: Path) -> Path:
    return repo / "scripts" / "coordination" / "merge_ready.py"


def check_organ_present(repo: Path) -> tuple[bool, str]:
    """L'organe cible doit exister avant tout cablage --apply."""
    target = organ_path(repo)
    if not target.is_file():
        return False, f"introuvable : {target}"
    return True, f"organe present : {target}"


def task_command(repo: Path) -> list[str]:
    """Commande reellement executee a chaque tour : ce script --run, qui
    journalise et appelle l'organe en --apply. C'est cette ligne que le
    lanceur VBS execute (vbs_content) ; l'action ENREGISTREE dans le
    planificateur est wscript (task_action)."""
    return [
        sys.executable,
        str(repo / "scripts" / "coordination" / "install_merge_ready_task.py"),
        "--run", "--repo", str(repo),
    ]


def vbs_content(repo: Path) -> str:
    """Contenu du lanceur run_hidden.vbs : la commande task_command(repo)
    executee par WScript.Shell.Run en fenetre 0 (masquee), avec attente de
    fin (True) et remontee du code de sortie (WScript.Quit) -- duree et
    verdict de la tache restent lisibles dans le planificateur.

    Le fichier est ecrit en ASCII : wscript lit les .vbs en ANSI, tout
    caractere non-ASCII casserait la ligne de commande silencieusement --
    on refuse fort (ValueError) plutot que d'ecrire un lanceur casse.
    """
    cmdline = subprocess.list2cmdline(task_command(repo))
    try:
        cmdline.encode("ascii")
    except UnicodeEncodeError as exc:
        raise ValueError(
            "ligne de commande non-ASCII (wscript lit les .vbs en ANSI, "
            f"le lanceur serait casse) : {cmdline!r} -- {exc}"
        ) from exc
    # litteral VBScript : chaque guillemet de la ligne de commande est double
    escaped = cmdline.replace('"', '""')
    return (
        "' Lanceur genere par install_merge_ready_task.py -- ecrase a chaque\n"
        "' --install, ne pas editer a la main.\n"
        "' Fenetre 0 (masquee, heritee par les enfants console de --run) et\n"
        "' attente de fin : le code de sortie remonte a la tache planifiee.\n"
        "Dim WshShell\n"
        "Set WshShell = CreateObject(\"WScript.Shell\")\n"
        f"WScript.Quit WshShell.Run(\"{escaped}\", 0, True)\n"
    )


def task_action() -> list[str]:
    """Action enregistree dans le planificateur : wscript execute le lanceur
    VBS sans fenetre. //B (mode batch) supprime les dialogues d'erreur de
    l'hote, //Nologo la banniere ; le prefixe // distingue les options de
    wscript d'un chemin commenceant par /."""
    return [str(WSH_PATH), "//B", "//Nologo", str(VBS_PATH)]


def build_schtasks_install(cmd: list[str], interval_minutes: int) -> list[str]:
    """Ligne schtasks /Create : toutes les N minutes, contexte utilisateur
    courant (gh auth vit au niveau utilisateur). ``cmd`` est l'ACTION de la
    tache : le lanceur wscript (task_action), PAS python.exe en direct."""
    # Quoter chaque element, jamais la ligne entiere : un /TR "python.exe script.py
    # --run" enregistre la ligne comme NOM d'executable, et la tache echoue
    # a chaque tour avec 0x80070002 (fichier introuvable) sans rien journaliser.
    tr = subprocess.list2cmdline(cmd)
    return [
        "schtasks", "/Create", "/F",
        "/TN", TASK_NAME,
        "/SC", "MINUTE",
        "/MO", str(interval_minutes),
        "/TR", tr,
    ]


def log_path_for(day: _dt.date | None = None) -> Path:
    day = day or _dt.date.today()
    return LOG_DIR / f"merge_ready_{day:%Y%m%d}.log"


def task_exists() -> bool:
    return _run(["schtasks", "/Query", "/TN", TASK_NAME]).returncode == 0


def cmd_dry_run(repo: Path, interval: int) -> int:
    """Imprime la commande EXACTE que --install enregistrerait et le
    contenu EXACT du lanceur VBS qu'il ecrirait. N'execute RIEN et
    n'ecrit RIEN : c'est la sortie que la discipline UAC exige de voir
    avant toute inscription schtasks."""
    try:
        vbs = vbs_content(repo)
    except ValueError as exc:
        print(f"REFUSE : {exc}", file=sys.stderr)
        return 2
    command = build_schtasks_install(task_action(), interval)
    print("DRY-RUN -- commande schtasks que --install enregistrerait :")
    print(" ".join(command))
    print(f"DRY-RUN -- contenu de {VBS_PATH} que --install ecrirait :")
    print(vbs, end="")
    print(f"journal de la tache : {log_path_for()}")
    return 0


def cmd_install(repo: Path, interval: int) -> int:
    ok, msg = check_organ_present(repo)
    if not ok:
        print(f"REFUSE : {msg}", file=sys.stderr)
        return 2
    print(f"garde OK : {msg}")
    try:
        vbs = vbs_content(repo)
    except ValueError as exc:
        print(f"REFUSE : {exc}", file=sys.stderr)
        return 2
    # le lanceur AVANT l'inscription : une tache enregistree ne doit jamais
    # pointer vers un fichier absent
    VBS_PATH.parent.mkdir(parents=True, exist_ok=True)
    VBS_PATH.write_text(vbs, encoding="ascii")
    proc = _run(build_schtasks_install(task_action(), interval))
    if proc.returncode != 0:
        print(
            f"schtasks /Create echoue (rc={proc.returncode}) : "
            f"{proc.stdout.strip()} {proc.stderr.strip()}",
            file=sys.stderr,
        )
        return 2
    print(f"tache installee : {TASK_NAME} toutes les {interval} minutes")
    print(f"lanceur   : {VBS_PATH}")
    print(f"commande  : {' '.join(task_command(repo))}")
    print(f"journal   : {log_path_for()}")
    print(
        "verification : schtasks /Query /TN " + TASK_NAME + " /V /FO LIST"
    )
    return 0


def cmd_status() -> int:
    if not task_exists():
        print(f"tache ABSENTE : {TASK_NAME}")
        return 1
    proc = _run(["schtasks", "/Query", "/TN", TASK_NAME, "/V", "/FO", "LIST"])
    print(proc.stdout)
    return 0


def cmd_uninstall() -> int:
    proc = _run(["schtasks", "/Delete", "/TN", TASK_NAME, "/F"])
    if proc.returncode != 0:
        print(
            f"suppression echouee : {proc.stdout.strip()} {proc.stderr.strip()}",
            file=sys.stderr,
        )
        return 2
    print(f"tache supprimee : {TASK_NAME}")
    # la tache etait l'unique consommateur du lanceur : on le retire
    VBS_PATH.unlink(missing_ok=True)
    print(f"lanceur supprime : {VBS_PATH}")
    return 0


def sync_repo(repo: Path) -> tuple[bool, str]:
    """Ramene le depot de l'organe sur origin/main, ou refuse le tour.

    Deux sieges acceptes : la branche `main`, ou un HEAD DETACHE (le worktree
    dedie d'ai-01, qui ne peut pas porter `main` tant que le checkout
    principal la tient). Refuse (sans rien toucher) toute autre branche, un
    depot qui porte des modifications suivies, et un HEAD detache qui n'est
    pas un ancetre d'origin/main (des commits locaux seraient abandonnes) :
    un tour ne doit jamais executer un gate ou un B.0 de branche, ni ecraser
    un travail local. Sinon fetch + avance rapide.
    """
    branch = _run(["git", "-C", str(repo), "rev-parse", "--abbrev-ref", "HEAD"])
    if branch.returncode != 0:
        return False, f"git rev-parse rc={branch.returncode} : {branch.stderr.strip()[:200]}"
    seat = branch.stdout.strip()
    if seat not in ("main", "HEAD"):
        return False, f"le depot {repo} est sur '{seat}', pas sur main ni detache"
    dirty = _run(["git", "-C", str(repo), "status", "--porcelain", "--untracked-files=no"])
    if dirty.returncode != 0 or dirty.stdout.strip():
        return False, f"le depot {repo} porte des modifications suivies : tour refuse"
    fetch = ["git", "-C", str(repo), "fetch", "-q", "origin", "main"]
    if seat == "main":
        steps = (fetch, ["git", "-C", str(repo), "merge", "--ff-only", "-q", "origin/main"])
    else:
        steps = (
            fetch,
            ["git", "-C", str(repo), "merge-base", "--is-ancestor", "HEAD", "origin/main"],
            ["git", "-C", str(repo), "checkout", "-q", "--detach", "origin/main"],
        )
    for cmd in steps:
        res = _run(cmd)
        if res.returncode != 0:
            return False, f"{' '.join(cmd[3:])} rc={res.returncode} : {res.stderr.strip()[:200]}"
    return True, "origin/main"


def journal_path() -> Path:
    """Chemin du journal de l'organe.

    Derive de ``LOG_DIR.parent`` -- le dossier de la tache -- et non
    recalcule : c'est le meme emplacement que
    ``merge_ready.default_journal_path`` (et que la recopie qu'en fait
    ``merge_ready_pass_timing.py``). La copie ne derive pas en silence --
    un test verrouille l'egalite des trois. Passer par ``LOG_DIR`` rend
    aussi le lanceur hermetique : un test qui redirige ``LOG_DIR`` ne lit
    jamais le journal de la machine.
    """
    return LOG_DIR.parent / JOURNAL_FILENAME


def timing_module():
    """L'organe de duree (`merge_ready_pass_timing.py`), charge par chemin.

    Il vit dans le meme repertoire que ce lanceur. Il n'est pas importe au
    chargement : il ne sert qu'au miroir, et son absence ne doit pas
    empecher la tache de tourner (le miroir tombe alors en mode « sans
    duree », il continue d'ecrire les verdicts).

    Charge par chemin et non par `import` : le lanceur est execute comme un
    script depuis un dossier de travail arbitraire (System32 au reveil), ou
    le repertoire du script n'est pas dans `sys.path`.
    """
    path = Path(__file__).resolve().parent / "merge_ready_pass_timing.py"
    if not path.is_file():
        return None
    try:
        spec = importlib.util.spec_from_file_location(
            "merge_ready_pass_timing_mirror", path
        )
        if spec is None or spec.loader is None:
            return None
        module = importlib.util.module_from_spec(spec)
        # Le module doit etre dans `sys.modules` AVANT son execution : les
        # `@dataclass` de l'organe y lisent leur propre module, et
        # l AttributeError (module absent) les ferait echouer.
        sys.modules[spec.name] = module
        spec.loader.exec_module(module)
    except Exception:  # noqa: BLE001 -- l'absence de l'organe n'est pas fatale
        sys.modules.pop("merge_ready_pass_timing_mirror", None)
        return None
    return module


def _duree_texte(state: dict, ts, max_gap: float) -> str:
    """La duree de l'evaluation decrite par la ligne courante.

    Meme convention que l'organe de duree : l'ecart entre deux lignes
    consecutives du journal est le cout d'evaluation de la PR de la ligne
    SUIVANTE (la ligne est ecrite apres l'evaluation). La premiere ligne
    d'un passage n'a pas de predecesseur : son cout n'est pas mesurable et
    n'est pas invente. Un ecart superieur au `--max-gap` coupe le passage
    (meme convention) : la duree n'est donc pas annoncee non plus.
    """
    prev_ts = state.get("prev_ts")
    if ts is None or prev_ts is None:
        return "duree n.d. (premiere ligne du passage)"
    delta = (ts - prev_ts).total_seconds()
    if delta < 0:
        return "duree n.d. (horodatage en retrait)"
    if delta > max_gap:
        return (
            f"duree n.d. (ecart {delta:.0f} s > {max_gap:.0f} s : "
            "passage coupe comme par l'organe de duree)"
        )
    return f"duree {delta:.1f} s"


def _drain_journal(
    journal: Path, log_fh, state: dict, parse_ts, max_gap: float, lock=None
) -> None:
    """Ecrit dans le journal de la tache les lignes de journal nouvelles.

    `state` porte l'offset lu, le reliquat de ligne incomplete et
    l'horodatage precedent (pour la duree). Une ligne partielle (le
    journal ecrit en append, une ligne peut etre lue a moitie) n'est pas
    rendue : elle est mise en attente et rendue au tour suivant, une fois
    complete.
    """
    offset = state["offset"]
    try:
        size = journal.stat().st_size
    except OSError:
        return
    if size <= offset:
        return
    with journal.open("rb") as fh:
        fh.seek(offset)
        chunk = fh.read(size - offset)
    state["offset"] = offset + len(chunk)
    state["pending"] += chunk
    while b"\n" in state["pending"]:
        raw, state["pending"] = state["pending"].split(b"\n", 1)
        text = raw.decode("utf-8", "replace").strip()
        if not text:
            continue
        try:
            data = json.loads(text)
        except ValueError:
            continue
        if not isinstance(data, dict):
            continue
        pr = data.get("pr")
        verdict = str(data.get("verdict") or "?")
        reason = str(data.get("reason") or "")
        ts = parse_ts(data.get("ts")) if parse_ts is not None else None
        label = f"PR #{pr}" if pr is not None else "PR ?"
        motif = f" -- {reason}" if reason else ""
        if lock is not None:
            with lock:
                log_fh.write(
                    f"journal : {label} {verdict}{motif} "
                    f"({_duree_texte(state, ts, max_gap)})\n"
                )
                # Flush a chaque PR : c'est le point de la demande (« log
                # ligne par ligne, avec flush a chaque PR »). Sans flush, le
                # tampon de 8 Ko du lanceur retiendrait les lignes jusqu'a la
                # fin du run -- c'est exactement le symptome que le miroir
                # supprime.
                log_fh.flush()
        else:
            log_fh.write(
                f"journal : {label} {verdict}{motif} "
                f"({_duree_texte(state, ts, max_gap)})\n"
            )
            log_fh.flush()
        state["mirrored"] += 1
        if ts is not None:
            state["prev_ts"] = ts


def mirror_journal(
    journal: Path,
    log_fh,
    start_offset: int,
    stop_event: threading.Event,
    poll_s: float = JOURNAL_POLL_S,
    lock=None,
) -> int:
    """Suit le journal de l'organe pendant le run et l'ecrit ligne par ligne.

    Renvoie le nombre de lignes mises en miroir. Ne leve jamais : une
    panne du miroir ne doit pas arreter la tache (le journal de l'organe
    reste la source de verite). `lock` (optionnel) serialise les ecritures
    avec le battement de coeur du lanceur.
    """
    timing = timing_module()
    parse_ts = getattr(timing, "parse_ts", None) if timing is not None else None
    max_gap = float(getattr(timing, "DEFAULT_MAX_GAP_S", DEFAULT_MAX_GAP_S))
    state = {"offset": start_offset, "pending": b"", "prev_ts": None, "mirrored": 0}
    try:
        while True:
            _drain_journal(journal, log_fh, state, parse_ts, max_gap, lock)
            if stop_event.wait(poll_s):
                break
        # Dernier tour : le journal a pu grossir pendant la derniere
        # scrutation (la fin du run ecrit ses lignes d'un coup).
        _drain_journal(journal, log_fh, state, parse_ts, max_gap, lock)
    except Exception:  # noqa: BLE001 -- le miroir ne doit jamais casser le run
        return int(state.get("mirrored") or 0)
    return int(state.get("mirrored") or 0)


def append_pass_timing(repo: Path, journal: Path, log_fh) -> str:
    """Ajoute au journal de la tache le rapport de duree de l'organe.

    L'organe de duree existe deja (`merge_ready_pass_timing.py`, #26799) :
    il mesure la duree d'un passage, groupee par classe, a partir du
    journal de l'organe. Il n'etait appele par PERSONNE -- sa sortie
    vivait dans le stdout d'un run manuel. L'appeler ici rend la mesure
    lisible dans le journal de la tache, sans rien reimplementer : c'est
    l'organe qui parle, avec ses propres regles.
    """
    organ = repo / "scripts" / "coordination" / "merge_ready_pass_timing.py"
    if not organ.is_file():
        log_fh.write(f"organe de duree absent : {organ}\n")
        log_fh.flush()
        return "absent"
    res = subprocess.run(
        [sys.executable, str(organ), "--journal", str(journal)],
        capture_output=True,
        check=False,
        text=True,
        encoding="utf-8",
        errors="replace",
        cwd=str(repo),
    )
    log_fh.write(getattr(res, "stdout", "") or "")
    stderr = getattr(res, "stderr", "") or ""
    if stderr:
        log_fh.write(stderr)
    log_fh.flush()
    return f"rc={getattr(res, 'returncode', 0)}"


def cmd_run(repo: Path) -> int:
    """Invoque par la tache planifiee (via le lanceur VBS masque) : journal
    horodate, pas de TTY.

    L'organe part en dry-run par defaut a l'ecran, mais le cablage est le
    geste : la tache lance --apply (c'est le mandat Q40 -- sans --apply le
    cablage ne ferait rien).
    """
    LOG_DIR.mkdir(parents=True, exist_ok=True)
    log = log_path_for()
    stamp = _dt.datetime.now().strftime("%Y-%m-%dT%H:%M:%S")
    with log.open("a", encoding="utf-8") as fh:
        fh.write(f"\n=== {stamp} run start ===\n")
        ok, msg = sync_repo(repo)
        if not ok:
            fh.write(f"=== tour REFUSE : {msg} ===\n")
            return 2
        fh.write(f"depot synchronise sur {msg}\n")
        fh.flush()
        # Le journal de l'organe est lu PENDANT le run : une ligne par PR,
        # avec la duree de l'evaluation, dans le journal de la tache.
        # L'organe n'imprime ses verdicts qu'apres sa boucle (mesure du
        # 23/11 : 191 PRs evaluees, 76 octets dans le log de la tache) --
        # sans ce miroir, un run long ne laisse aucune trace lisible.
        journal = journal_path()
        start_offset = journal.stat().st_size if journal.exists() else 0
        stop_event = threading.Event()
        # Le miroir (thread) et le battement de coeur (thread principal)
        # ecrivent dans le meme journal : un verrou, sinon les lignes se
        # melangent au milieu.
        journal_lock = threading.Lock()
        mirror = threading.Thread(
            target=mirror_journal,
            args=(journal, fh, start_offset, stop_event),
            kwargs={"lock": journal_lock},
            daemon=True,
            name="merge-ready-journal-mirror",
        )
        mirror.start()
        # cwd=repo : la tache planifiee demarre hors depot (System32), et les
        # organes que merge_ready lance appellent `git` sans `-C`. Sans ce
        # cwd, check_slot_reservation.py sortait en rc=2 a chaque tour et
        # chaque PR touchant un notebook etait sautee en
        # `slot-collision-unreadable` (mesure du 20/10 : #20434, #21008,
        # #21470, ~20 sauts par heure).
        #
        # `-u` : la sortie standard d'un process Python redirigee vers un
        # FICHIER est bufferisee par blocs -- rien n'atteint le journal avant
        # la sortie de l'enfant. Mesure du 22/11 (issue #28005) : sans `-u`,
        # le journal faisait 0 octet au bout de 0,35 s et 27 octets a la fin ;
        # avec `-u`, 18 octets a 0,35 s. Le journal du 22/11 est reste muet
        # 256 min pendant que la passe vivait.
        proc = subprocess.Popen(
            [sys.executable, "-u", str(organ_path(repo)), "--apply"],
            stdout=fh,
            stderr=subprocess.STDOUT,
            cwd=str(repo),
        )
        # Battement de coeur : tant que l'enfant tourne, le journal avance.
        # La ligne dit ce qui est MESURE (la passe est vivante) et rien de
        # plus -- le compte par PR reste dans `journal.jsonl`, que
        # `merge_ready_pass_timing.py` lit.
        started = time.monotonic()
        while True:
            try:
                proc.wait(timeout=HEARTBEAT_S)
                break
            except subprocess.TimeoutExpired:
                elapsed = int(time.monotonic() - started)
                with journal_lock:
                    fh.write(f"=== passe en cours (elapsed {elapsed} s) ===\n")
                    fh.flush()
        # Le miroir s'arrete AVANT les ecritures du lanceur : un seul
        # redacteur a la fois sur le journal de la tache.
        stop_event.set()
        mirror.join(timeout=60)
        fh.write("\n--- duree des passages (organe merge_ready_pass_timing.py) ---\n")
        fh.flush()
        try:
            append_pass_timing(repo, journal, fh)
        except Exception as exc:  # noqa: BLE001 -- le rapport est un bonus
            fh.write(f"rapport de duree indisponible : {exc}\n")
            fh.flush()
        fh.write(
            f"=== {_dt.datetime.now().strftime('%Y-%m-%dT%H:%M:%S')} "
            f"run end rc={proc.returncode} ===\n"
        )
    # exit code non zero si l'organe a echoue -- visible dans le journal
    return proc.returncode


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--install", action="store_true")
    parser.add_argument(
        "--dry-run",
        dest="dry_run",
        action="store_true",
        help="imprime la commande schtasks exacte sans l'executer",
    )
    parser.add_argument("--status", action="store_true")
    parser.add_argument("--uninstall", action="store_true")
    parser.add_argument(
        "--run",
        action="store_true",
        help="mode interne (invoque par la tache planifiee)",
    )
    parser.add_argument(
        "--repo",
        type=Path,
        default=DEFAULT_REPO,
        help=f"checkout principal du depot (defaut {DEFAULT_REPO})",
    )
    parser.add_argument(
        "--interval",
        type=int,
        default=INTERVAL_MINUTES,
        metavar="N",
        help=f"cadence en minutes (defaut {INTERVAL_MINUTES})",
    )
    args = parser.parse_args(argv)
    if args.interval <= 0:
        parser.error("--interval doit etre > 0")

    repo = args.repo.resolve()
    # --dry-run d'abord : un --install --dry-run combine fait le geste sur.
    if args.dry_run:
        return cmd_dry_run(repo, args.interval)
    if args.install:
        return cmd_install(repo, args.interval)
    if args.status:
        return cmd_status()
    if args.uninstall:
        return cmd_uninstall()
    if args.run:
        return cmd_run(repo)
    parser.print_help()
    return 1


if __name__ == "__main__":
    sys.exit(main())
