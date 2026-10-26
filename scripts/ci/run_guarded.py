#!/usr/bin/env python3
"""Lance une commande longue sous deux plafonds durs : RAM du processus, RAM libre machine.

Incident fondateur -- 2026-10-05, po-2023 : un run de mesure de 6 h (banc
sigma/K sur Qwen3.5-27B, #18112) a retenu 38,6 Go et porte la machine a 99,3 %
(0,43 Go libres, commit 181,7/210,7 Go), en trajectoire identique au BSOD de la
veille. Le processus etait de surcroit **orphelin** -- session parente morte,
plus personne pour surveiller sa fin -- et **aucun garde ne l'a arrete** : la
non-recidive a tenu a la chance (il s'est fini seul a 12:56), pas a un
mecanisme.

Ce lanceur remplace la chance par deux mecanismes independants :

1. **plafonds durs** -- si le RSS cumule du processus et de ses descendants
   depasse ``--limit-gib``, ou si la RAM physique disponible de la machine
   passe sous ``--reserve-gib``, l'arbre est tue et le lanceur sort en 3
   (plafond processus) ou 4 (plancher machine) ;
2. **anti-orphelin** -- sous Windows, l'enfant est place dans un Job Object
   ``KILL_ON_JOB_CLOSE`` : si CE lanceur meurt (session fermee, kill -9,
   crash), le systeme tue l'enfant. Un run ne survit plus a son observateur.

Le rapport de fin (pic de RSS, minimum de RAM libre, raison de l'arret) part
dans le journal : un run garde se relit avec son enveloppe de ressources.

Usage :
    python scripts/ci/run_guarded.py --limit-gib 24 --reserve-gib 4 \\
        --log runs/27b.log -- python measure_sigma_jailbreak_bridge.py --full ...

Job Object et memoire -- #21661. Apres l'anti-orphelin, le job porte un
**plafond memoire dur** (``JOB_OBJECT_LIMIT_JOB_MEMORY``) : la memoire
commitee du job (lui et ses enfants) ne peut pas depasser la limite ; quand
elle est atteinte, les **allocations echouent** au lieu de swapper sur l'hote.
L'arret effectif du job est assure par le second verrou -- la garde de RSS
(``--limit-gib``) tue l'arbre. Le plafond du job et la garde de RSS se
regissent sur la meme valeur : le noyau refuse d'abord l'allocation, la
garde coupe ensuite si le processus survit a l'echec d'allocation.

Garde d'admission -- #21661. ``--max-commit-charge-pct`` refuse le demarrage
quand la **charge de commit** de la machine (memoire physique + pagefile)
depasse le seuil, et refuse **aussi** quand la mesure est illisible
(fail-CLOSED : une garde aveugle ne laisse pas burning). Meme instrument que
la garde GPU existante (``Win32_PerfFormattedData_PerfOS_Memory``), parce
qu'une sonde differente peut rendre un chiffre propre, plausible et
permissif. Hors Windows, l'instrument n'existe pas (l'equivalent Linux est un
cgroup, pas un compteur) : la garde est alors declaree NON APPLICABLE et ne
refuse pas -- un refus systematique y bloquerait tout lancement.

Exclusion N=1 -- #21661. ``--exclusive-lock <chemin>`` prend un verrou
exclusif sur un fichier ; si un autre lancement le tient deja, le demarrage
est refuse. Le verrou est tenu par ce lanceur, donc par toute la duree de
l'entrainement, et il est relache par le systeme si le lanceur meurt.

Garde GPU optionnelle -- #22456. ``--gpu-entity <machine>#gpu<n>`` active la
sequence codee du regisseur : consultation du gate ``check_pending`` du
ledger ``gpu-reservation``, puis ecriture de l'observation ``held`` AVANT le
lancement de l'enfant (la reservation existe avant le premier appel CUDA),
puis observation ``released`` au teardown (arret garde, interruption, echec
de demarrage ou sortie normale). Sans ``--gpu-entity``, ce lanceur ne fait
AUCUN appel au ledger : un job sans device declare ne peut pas echouer a
cause du ledger. Avec ``--gpu-entity``, toute panne de l'organe (module
absent, appel qui leve, source illisible) refuse le lancement -- on ne lance
pas sur un device dont on ne peut ni lire l'etat ni porter la reservation
(fail-CLOSED). ``--gpu-holder`` et ``--gpu-workload`` sont requis avec
``--gpu-entity`` ; ``--gpu-expected-end`` (UTC ISO-8601, suffixe Z) est
facultatif mais **borne par defaut** (maintenant + 24 h, journalisee) -- un
hold sans borne n'est jamais STALE, donc un lanceur tue brutalement laisserait
le device pris pour toute la flotte ; ``--gpu-issue`` est facultatif.

Codes de sortie : 0 commande terminee sous les deux plafonds · 3 plafond
processus franchi · 4 plancher machine franchi · 5 demarrage refuse (RAM libre
insuffisante, Job Object indisponible sans ``--allow-no-job``, charge de
commit au-dessus du seuil ou illisible, verrou N=1 deja pris, gate GPU
defavorable ou indisponible, reservation GPU non ecrite) · 6 la
commande n'a pas demarre · 7 commande terminee mais l'observation ``released``
du ledger GPU n'a pas pu etre ecrite (la reservation reste vivante) ·
130 interruption clavier · sinon le code de sortie de la commande.
"""
import argparse
import json
import os
import subprocess
import sys
import time
from datetime import datetime, timedelta, timezone
from pathlib import Path

GiB = 2**30

RC_OK = 0
RC_LIMIT = 3
RC_FLOOR = 4
RC_REFUSED = 5
RC_NOSTART = 6
RC_INTERRUPT = 130
RC_LEDGER = 7

# Flags Job Object (winbase.h)
JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE = 0x00002000
JOB_OBJECT_LIMIT_JOB_MEMORY = 0x00000200

# CreateProcessW (winbase.h)
CREATE_SUSPENDED = 0x00000004


def _win_job_kill_on_close(memory_limit_bytes=0):
    """Job Object Windows avec ``KILL_ON_JOB_CLOSE`` (anti-orphelin structurel).

    ``memory_limit_bytes`` > 0 ajoute le plafond dur de memoire commitee du
    job (``JOB_OBJECT_LIMIT_JOB_MEMORY``) : au-dela, les allocations
    **echouent** -- la machine ne swappe pas pour sauver le job.

    Retourne ``(job, kernel32)`` ou ``None`` si indisponible. L'enfant assigne
    a ce job est tue par le systeme des que le handle se ferme -- c'est-a-dire
    des que ce lanceur meurt, quelle qu'en soit la cause (fermeture de session,
    kill -9, crash). Sans ce job, un enfant survit a son observateur : c'est
    exactement le mode de defaillance de l'incident du 2026-10-05.
    """
    if os.name != "nt":
        return None
    import ctypes
    from ctypes import wintypes

    kernel32 = ctypes.WinDLL("kernel32", use_last_error=True)

    class _IoCounters(ctypes.Structure):
        _fields_ = [(n, ctypes.c_ulonglong) for n in (
            "ReadOperationCount", "WriteOperationCount", "OtherOperationCount",
            "ReadTransferCount", "WriteTransferCount", "OtherTransferCount")]

    class _BasicLimit(ctypes.Structure):
        _fields_ = [("PerProcessUserTimeLimit", ctypes.c_longlong),
                    ("PerJobUserTimeLimit", ctypes.c_longlong),
                    ("LimitFlags", wintypes.DWORD),
                    ("MinimumWorkingSetSize", ctypes.c_size_t),
                    ("MaximumWorkingSetSize", ctypes.c_size_t),
                    ("ActiveProcessLimit", wintypes.DWORD),
                    ("Affinity", ctypes.c_size_t),      # ULONG_PTR
                    ("PriorityClass", wintypes.DWORD),
                    ("SchedulingClass", wintypes.DWORD)]

    class _ExtLimit(ctypes.Structure):
        _fields_ = [("BasicLimitInformation", _BasicLimit),
                    ("IoInfo", _IoCounters),
                    ("ProcessMemoryLimit", ctypes.c_size_t),
                    ("JobMemoryLimit", ctypes.c_size_t),
                    ("PeakProcessMemoryUsed", ctypes.c_size_t),
                    ("PeakJobMemoryUsed", ctypes.c_size_t)]

    kernel32.CreateJobObjectW.restype = wintypes.HANDLE
    kernel32.CreateJobObjectW.argtypes = [ctypes.c_void_p, wintypes.LPCWSTR]
    job = kernel32.CreateJobObjectW(None, None)
    if not job:
        return None
    info = _ExtLimit()
    info.BasicLimitInformation.LimitFlags = JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE
    if memory_limit_bytes:
        info.BasicLimitInformation.LimitFlags |= JOB_OBJECT_LIMIT_JOB_MEMORY
        info.JobMemoryLimit = int(memory_limit_bytes)
    if not kernel32.SetInformationJobObject(
            job, 9, ctypes.byref(info), ctypes.sizeof(info)):   # 9=Extended
        return None
    return job, kernel32


def _assign_to_job(handle_pair, proc):
    """Assigne l'enfant au Job Object. False si le systeme refuse."""
    if handle_pair is None:
        return False
    import ctypes
    from ctypes import wintypes

    job, kernel32 = handle_pair
    kernel32.AssignProcessToJobObject.argtypes = [wintypes.HANDLE, wintypes.HANDLE]
    return bool(kernel32.AssignProcessToJobObject(
        job, wintypes.HANDLE(int(proc._handle))))


def _resume_suspended(proc):
    """Reprend un processus demarre en ``CREATE_SUSPENDED``.

    La creation suspendue ferme la fenetre entre le demarrage du fils et son
    assignation au job : sans elle, un fils peut creer ses propres enfants
    **avant** d'etre dans le job, et ces petits-lains n'heriteront pas de la
    limite memoire. La reprise passe par ``NtResumeProcess`` (ntdll) ; en cas
    d'echec, le lanceur tue l'enfant et relance sans suspension -- le plafond
    reste pose, seule la fenetre d'heritage est plus large.
    """
    if os.name != "nt":
        return True
    import ctypes
    from ctypes import wintypes

    try:
        ntdll = ctypes.WinDLL("ntdll")
        ntdll.NtResumeProcess.argtypes = [wintypes.HANDLE]
        ntdll.NtResumeProcess.restype = ctypes.c_long
        status = ntdll.NtResumeProcess(wintypes.HANDLE(int(proc._handle)))
        return status >= 0
    except Exception:                                  # pragma: no cover
        return False


def _commit_charge_pct():
    """Charge de commit de la machine en pourcentage, ou ``None`` si illisible.

    Meme instrument que la garde GPU existante : ``Win32_PerfFormattedData_
    PerfOS_Memory`` (``CommittedBytes`` / ``CommitLimit``). Les compteurs
    ``\\Memory\\...`` sont absents sous certaines locales, et la memoire
    **physique** n'est pas la charge de commit : les deux sondes se
    ressemblent et l'ecart enjambe le seuil. Retourner ``None`` sur echec
    permet a l'appelant de refuser (fail-CLOSED) au lieu de laisser passer.
    """
    if os.name != "nt":
        return None
    cmd = [
        "powershell", "-NoProfile", "-Command",
        "$m=Get-CimInstance Win32_PerfFormattedData_PerfOS_Memory; "
        "if ($m) { [int](100*$m.CommittedBytes/$m.CommitLimit) }",
    ]
    try:
        out = subprocess.run(cmd, capture_output=True, text=True, timeout=60,
                             encoding="utf-8", errors="replace")
    except (OSError, subprocess.SubprocessError):
        return None
    if out.returncode != 0:
        return None
    raw = (out.stdout or "").strip()
    try:
        return int(raw)
    except ValueError:
        return None


def _acquire_exclusive_lock(path):
    """Prend un verrou exclusif sur un fichier. ``None`` si deja pris.

    Le verrou est rendu par le systeme a la mort du processus : un lanceur
    tue ne laisse pas de verrou fantome, et un verrou tenu par un processus
    vivant est un indice fiable. Le handle doit rester ouvert pendant toute
    la duree du job.
    """
    lock_path = Path(path)
    lock_path.parent.mkdir(parents=True, exist_ok=True)
    try:
        fh = open(lock_path, "a+b")
    except OSError:
        return None
    try:
        if os.name == "nt":
            import msvcrt
            fh.seek(0)
            if fh.read(1) == b"":
                fh.write(b"0")
                fh.flush()
            fh.seek(0)
            msvcrt.locking(fh.fileno(), msvcrt.LK_NBLCK, 1)
        else:
            import fcntl
            fcntl.flock(fh.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
    except OSError:
        fh.close()
        return None
    return fh


# --- Garde GPU optionnelle : gate + reservation via le ledger (#22456) ------
#
# Decision de robustesse : le chemin GPU ne s'active QUE sur --gpu-entity.
# Un job CPU (sans device declare) ne touche jamais le ledger et ne peut donc
# pas echouer a cause de lui. Avec --gpu-entity, une panne de l'organe
# (module absent, appel qui leve, sortie illisible) est traitee comme une
# INDISPONIBILITE de la source et REFUSE le lancement : on ne lance pas sur un
# device dont on ne peut ni lire l'etat ni porter la reservation.

#: Nom du ledger GPU dans l'organe debt_ledger.py.
GPU_LEDGER_NAME = "gpu-reservation"
#: Branche qui porte l'etat publie des reservations (la source PRIMAIRE ;
#: le dashboard en est le miroir, le snapshot local un cache).
GPU_LEDGER_BRANCH = "ops/gpu-ledger"
#: Remote git sur lequel la branche du ledger est publiee et lue. C'est un
#: PARAMETRE, pas une decision codee en dur : l'etat vivant des reservations
#: est de l'orchestration (usage interne de flotte), et sa cible peut etre un
#: depot prive -- le registre ne doit pas dependre de ce choix.
GPU_LEDGER_REMOTE_DEFAULT = "origin"

#: Borne par defaut d'un hold quand `--gpu-expected-end` n'est pas fourni.
#: Sans borne, un lanceur tué brutalement (kill -9, reboot, crash de l'hote)
#: laisse un hold VIVANT : aucun chemin de sortie ne s'execute, le verdict
#: STALE ne peut donc jamais etre rendu, et le device reste pris pour toute
#: la flotte -- jusqu'a une liberation manuelle. Une borne rend ce cas
#: detectable par l'organe au lieu de le laisser muet.
GPU_HOLD_DEFAULT_HOURS = 24

#: Verdicts du gate qui autorisent le lancement. Tout autre verdict (HOLD,
#: STALE, UNPOSTED, ou un verdict d'indisponibilite rendu par une version
#: future de l'organe) REFUSE : fail-CLOSED, la liste blanche seule ouvre.
GPU_GATE_GREEN_VERDICTS = frozenset({"OK_TO_RUN", "NO_OBS", "RELEASED"})


def _ledger_organ_path():
    """Chemin de l'organe ``debt_ledger.py``, deduit de ``__file__``.

    Ce script vit dans ``scripts/ci/`` et l'organe dans
    ``scripts/coordination/`` : le chemin est relatif au fichier, jamais un
    chemin absolu code en dur.
    """
    return Path(__file__).resolve().parents[1] / "coordination" / "debt_ledger.py"


def _run_ledger_organ(args, timeout=120):
    """Appelle l'organe ledger via ``sys.executable``. Rend ``(rc, stdout, stderr)``.

    Une panne de l'appel (organe absent du disque, executable impossible,
    timeout) rend ``(None, "", detail)`` : le retour rc=None distingue la
    PANNE de l'organe d'un simple code de sortie non nul de l'organe.
    """
    organ = _ledger_organ_path()
    if not organ.is_file():
        return None, "", f"organe introuvable : {organ}"
    try:
        proc = subprocess.run(
            [sys.executable, str(organ), *args],
            capture_output=True, text=True, timeout=timeout,
            encoding="utf-8", errors="replace")
    except (OSError, subprocess.SubprocessError) as exc:
        return None, "", f"{type(exc).__name__}: {exc}"
    return proc.returncode, proc.stdout or "", proc.stderr or ""


def _utc_now_iso():
    """Heure UTC reelle au format ISO-8601 attendu par le ledger (suffixe Z).

    Jamais une heure locale etiquetee Z : le ledger refuse un stamp naïf et
    un offset non-UTC, et une horloge melange reordonnerait les observations.
    Les microsecondes garantissent que deux appels successifs produisent des
    contenus (donc des observation_id) distincts.
    """
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%S.%fZ")


def _gpu_gate_check(entity, my_lane, remote=GPU_LEDGER_REMOTE_DEFAULT):
    """Consulte ``check_pending`` pour l'entite. Rend ``(verdict, detail)``.

    ``my_lane`` est la lane qui demande le device (``--gpu-holder``). Elle est
    TRANSMISE au gate (``--my-lane``) : c'est elle qui distingue le tenant d'un
    hold, admis dans sa fenetre (OK_TO_RUN), d'une autre lane, refusee (HOLD).
    Sans elle, le gate ne peut prouver aucune propriete -- avant ce correctif,
    il rendait alors OK_TO_RUN sur le hold vivant d'une autre lane, et ce
    lanceur admettait un second job sur un device deja reserve (PR #22755,
    finding Hermes 1).

    verdict ``None`` signifie SOURCE INDISPONIBLE : appel en panne, sortie non
    JSON, ou verdict absent -- dans les trois cas l'appelant refuse.
    """
    if not my_lane:
        # Fail-CLOSED : un appel sans lane ne peut pas etre admis sur un device
        # tenu, et le gate ne doit pas etre consulte sans elle.
        return None, "lane appelante absente : le gate ne peut prouver aucune propriete"
    rc, out, err = _run_ledger_organ([
        "check_pending", "--ledger", GPU_LEDGER_NAME,
        "--entity", entity, "--remote", remote,
        "--my-lane", my_lane, "--json",
    ])
    if rc is None:
        return None, err
    lines = [ln for ln in (out or "").strip().splitlines() if ln.strip()]
    try:
        payload = json.loads(lines[-1]) if lines else None
    except ValueError:
        payload = None
    if not isinstance(payload, dict):
        return None, f"sortie du gate non parsable (rc={rc}) : {(err or out).strip()[:200]!r}"
    verdict = payload.get("verdict")
    if not isinstance(verdict, str) or not verdict:
        return None, f"verdict absent de la sortie du gate (rc={rc})"
    source = str(payload.get("source") or "")
    if verdict in GPU_GATE_GREEN_VERDICTS and verdict != "NO_OBS" and source != "git":
        # Seule une lecture FRAICHE de la branche (source exactement `git`)
        # peut AFFIRMER qu'un device est libre ou a nous. Un cache local, un
        # ref de suivi perime (fetch en echec), ou une sortie qui ne nomme
        # pas sa source peuvent dater d'avant le hold d'autrui : un verdict
        # vert y autoriserait deux machines sur le meme device -- le defaut
        # exact que ce transport doit empecher. Le test portait sur le
        # PREFIXE `git`, que la sortie `git (fetch impossible ...)` passait
        # (PR #22755, finding Hermes 3). `NO_OBS` reste admis : c'est un
        # constat d'absence, pas une affirmation de liberte (et la branche
        # n'a jamais existe dans ce cas).
        return (
            "NON_AUTORITAIRE",
            f"verdict {verdict} rendu depuis une source NON autoritaire "
            f"({source or 'source non nommee'}) -- seule une lecture fraiche "
            "de la branche (source=git) peut autoriser un lancement",
        )
    return verdict, str(payload.get("reason") or "")


def _gpu_append_observation(entity, fields, actor):
    """Ecrit une observation gpu-reservation via l'organe. Rend ``(ok, detail)``.

    L'appel est fait SANS ``--dry-run`` : il ecrit dans le spool reel du
    state-dir (et echoue si le state-dir n'est pas initialise -- c'est le
    fail-CLOSED voulu : une reservation qui n'existe nulle part n'est pas une
    reservation). L'``observation_id`` est calcule par l'organe a partir du
    contenu ; ce lanceur n'en fabrique aucun.
    """
    rc, out, err = _run_ledger_organ([
        "append", "--ledger", GPU_LEDGER_NAME,
        "--entity", entity,
        "--actor", actor,
        "--evidence", "run_guarded",
        "--confidence", "high",
        "--fields-json", json.dumps(fields, ensure_ascii=False),
    ])
    if rc is None:
        return False, err
    if rc != 0:
        return False, f"rc={rc} : {(err or out).strip()[:300]}"
    # Succes : extraire l'observation_id de la ligne [OBS] pour le journal
    # (tolerant : un format futur different ne casse pas le lancement).
    for line in (out or "").splitlines():
        if line.startswith("[OBS] "):
            try:
                payload = json.loads(line[len("[OBS] "):])
                return True, str(payload.get("observation_id") or "")
            except ValueError:
                break
    return True, ""


def _gpu_publish_reservations(machine, remote=GPU_LEDGER_REMOTE_DEFAULT):
    """Publie les reservations locales sur la branche `ops/gpu-ledger`.

    Pourquoi cette etape est INDISPENSABLE : le gate d'admission lit l'etat
    PUBLIE (la branche), et une observation restee dans le spool local rend le
    verdict `UNPOSTED` -- qui BLOQUE le lancement suivant, y compris celui de
    la machine qui vient de reserver. Sans publication, la sequence
    `held -> released` se verrouillerait elle-meme a la deuxieme reservation.

    Rend ``(ok, detail)`` ; l'echec est un refus fail-CLOSED cote admission
    (une reservation invisible de la flotte n'est pas une reservation) et un
    signalement explicite cote teardown.
    """
    rc, out, err = _run_ledger_organ([
        "publish", "--git", "--ledger", GPU_LEDGER_NAME,
        "--machine", machine, "--remote", remote, "--emit",
    ], timeout=300)
    if rc is None:
        return False, err
    if rc != 0:
        return False, f"rc={rc} : {(err or out).strip()[:300]}"
    return True, (out or "").strip()[-200:]


def _gpu_build_fields(state, started_at, expected_end, holder, workload, issue):
    """Construit le dictionnaire des champs gpu-reservation d'une observation.

    Les champs absents sont omis (l'organe trace les champs manquants mais ne
    les refuse pas) ; les champs inconnus, eux, sont refuses -- d'ou la
    construction explicite.
    """
    fields = {"state": state, "started_at": started_at}
    if expected_end:
        fields["expected_end"] = expected_end
    if holder:
        fields["holder"] = holder
    if workload:
        fields["workload"] = workload
    if issue:
        fields["issue"] = issue
    return fields


def _release_gpu_if_held(gpu_res, fh, ended_reason,
                         remote=GPU_LEDGER_REMOTE_DEFAULT):
    """Teardown GPU : ecrit l'observation ``released`` si un ``held`` a ete porte.

    ``started_at`` du released = l'instant du held ; ``expected_end`` =
    l'heure UTC reelle de fin. Rend True si l'ecriture a reussi (ou s'il n'y
    avait rien a faire) ; l'echec est signale dans le journal par un message
    explicite -- un held sans released laisse une reservation vivante sur un
    device libre et bloque les lancements suivants a tort.
    """
    if gpu_res is None:
        return True
    ended_at = _utc_now_iso()
    fields = _gpu_build_fields(
        state="released",
        started_at=gpu_res["held_started_at"],
        expected_end=ended_at,
        holder=gpu_res.get("holder"),
        workload=gpu_res.get("workload"),
        issue=gpu_res.get("issue"),
    )
    ok, detail = _gpu_append_observation(
        gpu_res["entity"], fields, gpu_res.get("holder") or "run_guarded")
    if ok:
        _say(fh, f"gpu-reservation : released ecrit pour {gpu_res['entity']} "
                 f"({ended_reason}) -- hold du {gpu_res['held_started_at']} "
                 f"ferme a {ended_at}"
                 + (f" (observation {detail})" if detail else ""))
        # Le released doit etre PUBLIE comme le held : un hold ferme
        # localement mais invisible de la flotte laisse les autres machines
        # croire le device tenu.
        published, pub_detail = _gpu_publish_reservations(
            gpu_res["entity"].split("#")[0], remote)
        if not published:
            _say(fh, f"ATTENTION gpu-reservation : le released de "
                     f"{gpu_res['entity']} n'a pas pu etre PUBLIE -- "
                     f"{pub_detail} -- la flotte peut encore voir le hold et "
                     f"croire le device tenu. Remediation : "
                     f"python scripts/coordination/debt_ledger.py publish --git "
                     f"--ledger {GPU_LEDGER_NAME} --emit")
            return False
    else:
        _say(fh, f"ATTENTION gpu-reservation : l'observation released N'A PAS PU "
                 f"etre ecrite pour {gpu_res['entity']} ({ended_reason}) -- la "
                 f"reservation reste VIVANTE sur un device libre et bloquera les "
                 f"lancements suivants. Liberer manuellement : debt_ledger.py "
                 f"append --ledger gpu-reservation --entity {gpu_res['entity']} "
                 f"--actor {gpu_res.get('holder') or 'run_guarded'} "
                 f"--evidence manual-release --confidence high "
                 f"--fields-json \"<state=released, started_at="
                 f"{gpu_res['held_started_at']}, expected_end={ended_at}>\". "
                 f"Detail de l'echec : {detail}")
    return ok



def _rss_bytes(pid):
    """RSS cumule du processus et de ses descendants (0 si process parti)."""
    import psutil

    try:
        proc = psutil.Process(pid)
        procs = [proc] + proc.children(recursive=True)
    except psutil.NoSuchProcess:
        return 0
    total = 0
    for p in procs:
        try:
            total += p.memory_info().rss
        except (psutil.NoSuchProcess, psutil.AccessDenied):
            pass
    return total


def _available_bytes():
    import psutil

    return psutil.virtual_memory().available


def _kill_tree(pid):
    """Tue l'arbre du pid : descendants d'abord, puis la racine."""
    import psutil

    try:
        proc = psutil.Process(pid)
    except psutil.NoSuchProcess:
        return
    procs = []
    try:
        procs = proc.children(recursive=True)
    except (psutil.NoSuchProcess, psutil.AccessDenied):
        pass
    for p in procs + [proc]:
        try:
            p.kill()
        except (psutil.NoSuchProcess, psutil.AccessDenied):
            pass


def _say(fh, msg):
    """Ecrit une ligne horodatee sur la console ET dans le journal."""
    line = f"[{time.strftime('%H:%M:%S')}] {msg}"
    print(line, flush=True)
    if fh is not None:
        fh.write(line + "\n")
        fh.flush()


def main(argv=None):
    ap = argparse.ArgumentParser(
        description="Lance une commande sous plafond de RAM et plancher de RAM libre.",
        epilog="Exemple : run_guarded.py --limit-gib 24 --log run.log -- python train.py")
    ap.add_argument("--limit-gib", type=float, required=True,
                    help="plafond de RSS cumule du processus et de ses descendants")
    ap.add_argument("--reserve-gib", type=float, default=4.0,
                    help="RAM physique libre a ne jamais franchir vers le bas (defaut 4)")
    ap.add_argument("--poll", type=float, default=5.0,
                    help="periode de mesure en secondes (defaut 5)")
    ap.add_argument("--report-every", type=float, default=300.0,
                    help="ligne de suivi toutes les N s, 0 = aucune (defaut 300)")
    ap.add_argument("--log", default=None,
                    help="journal de la commande (la garde y ecrit aussi son rapport)")
    ap.add_argument("--cwd", default=None, help="repertoire de travail de la commande")
    ap.add_argument("--allow-no-job", action="store_true",
                    help="accepter de lancer sans Job Object (l'enfant survivrait "
                         "a ce lanceur) -- refus par defaut, cf incident 2026-10-05")
    ap.add_argument("--no-job", action="store_true",
                    help="ne poser AUCUN Job Object : ni anti-orphelin, ni "
                         "plafond memoire du job. Sert de CONTROLE NEGATIF "
                         "(prouver que l'arret vient du job) et de repli assume")
    ap.add_argument("--job-memory-limit-gib", type=float, default=0.0,
                    help="plafond DUR de memoire commitee du job (processus et "
                         "enfants). 0 = desactive. Au-dela, les allocations "
                         "echouent au lieu de swapper (cf #21661)")
    ap.add_argument("--max-commit-charge-pct", type=int, default=0,
                    help="refuse le demarrage si la charge de commit de la "
                         "machine depasse ce pourcentage. 0 = desactive. "
                         "Une mesure ILLISIBLE refuse aussi (fail-CLOSED)")
    ap.add_argument("--exclusive-lock", default=None,
                    help="chemin d'un fichier de verrou exclusif : refuse le "
                         "demarrage si un autre lancement le tient (N = 1)")
    ap.add_argument("--pid-file", default=None,
                    help="fichier ou ecrire le PID du processus lance")
    ap.add_argument("--stderr-file", default=None,
                    help="fichier ou ecrire la sortie d'erreur de la commande "
                         "(par defaut, elle est fusionnee dans --log)")
    ap.add_argument("--gpu-entity", default=None, metavar="MACHINE#gpuN",
                    help="active la garde GPU : entite du device dans le ledger "
                         "gpu-reservation (ex myia-ai-01#gpu2). Sans cette "
                         "option, AUCUN appel au ledger n'est fait (comportement "
                         "inchange). Avec elle : gate check_pending, puis "
                         "reservation held AVANT le lancement, puis released au "
                         "teardown (#22456)")
    ap.add_argument("--gpu-holder", default=None, metavar="LANE",
                    help="lane tenante du device (ex myia-ai-01:CoursIA-2) -- "
                         "requis avec --gpu-entity")
    ap.add_argument("--gpu-workload", default=None, metavar="SLUG",
                    help="slug court du travail lance sur le device -- requis "
                         "avec --gpu-entity")
    ap.add_argument("--gpu-expected-end", default=None, metavar="ISO8601-UTC",
                    help="fin attendue du hold, UTC ISO-8601 avec suffixe Z "
                         "(ex 2026-10-26T18:00:00Z). Absent, une borne par "
                         "defaut est appliquee (maintenant + 24 h) : un hold "
                         "sans fin rend le device ILLIBRE pour toute la "
                         "flotte jusqu'a une liberation manuelle")
    ap.add_argument("--gpu-ledger-remote", default=GPU_LEDGER_REMOTE_DEFAULT,
                    metavar="REMOTE",
                    help="remote git sur lequel la branche du ledger "
                         f"({GPU_LEDGER_BRANCH}) est publiee et lue "
                         f"(defaut : {GPU_LEDGER_REMOTE_DEFAULT}). Parametre, "
                         "pas une decision codee en dur : la cible de "
                         "l'etat vivant de reservation peut etre un depot "
                         "prive")
    ap.add_argument("--gpu-issue", default=None, metavar="REPO#N",
                    help="issue de rattachement du hold (ex jsboige/CoursIA#1454)")
    ap.add_argument("cmd", nargs=argparse.REMAINDER,
                    help="commande a lancer, precedee de --")
    args = ap.parse_args(argv)

    if args.gpu_entity and not (args.gpu_holder and args.gpu_workload):
        ap.error("--gpu-entity exige --gpu-holder et --gpu-workload : la "
                 "reservation doit dire QUI lance QUOI sur le device")

    cmd = args.cmd
    if cmd and cmd[0] == "--":
        cmd = cmd[1:]
    if not cmd:
        ap.error("aucune commande : terminer par -- <cmd> [args...]")

    try:
        import psutil  # noqa: F401
    except ImportError:
        print("run_guarded: psutil requis (pip install psutil)", file=sys.stderr)
        return RC_REFUSED

    limit = int(args.limit_gib * GiB)
    reserve = int(args.reserve_gib * GiB)

    fh = None
    if args.log:
        Path(args.log).parent.mkdir(parents=True, exist_ok=True)
        fh = open(args.log, "a", encoding="utf-8")
        _say(fh, f"run_guarded : plafond processus {args.limit_gib:.1f} GiB, "
                 f"plancher machine {args.reserve_gib:.1f} GiB, journal {args.log}")
        child_out = fh
    else:
        child_out = None

    err_fh = None
    if args.stderr_file:
        Path(args.stderr_file).parent.mkdir(parents=True, exist_ok=True)
        err_fh = open(args.stderr_file, "a", encoding="utf-8")
        _say(fh, f"journal d'erreur de la commande : {args.stderr_file}")

    lock_fh = None

    def close_logs():
        for handle in (fh, err_fh, lock_fh):
            if handle is not None:
                try:
                    handle.close()
                except OSError:
                    pass

    free0 = _available_bytes()
    if free0 < reserve:
        _say(fh, f"REFUS : RAM libre {free0 / GiB:.1f} GiB < plancher "
                 f"{args.reserve_gib:.1f} GiB des le demarrage -- rien n'est lance.")
        close_logs()
        return RC_REFUSED

    # --- Garde d'admission : charge de commit (#21661) ------------------------
    if args.max_commit_charge_pct > 0:
        charge = _commit_charge_pct()
        if charge is None and os.name != "nt":
            # Hors Windows il n'existe pas d'instrument equivalent (la charge
            # de commit est une notion du gestionnaire de memoire Windows ;
            # l'equivalent Linux est un cgroup, pas un compteur). Ce n'est pas
            # une mesure ILLISIBLE : c'est une garde SANS OBJET sur cette
            # plateforme -- refuser ici bloquerait tout lancement Linux.
            _say(fh, "garde de charge de commit : NON APPLICABLE sur cette "
                     "plateforme (pas d'instrument equivalent) -- demarrage "
                     "autorise. Le plafond memoire, lui, reste actif.")
        elif charge is None:
            _say(fh, f"REFUS : charge de commit ILLISIBLE (capteur muet) -- "
                     f"fail-CLOSED, rien n'est lance. Seuil demande : "
                     f"{args.max_commit_charge_pct} %.")
            close_logs()
            return RC_REFUSED
        elif charge > args.max_commit_charge_pct:
            _say(fh, f"REFUS : charge de commit {charge} % > "
                     f"{args.max_commit_charge_pct} % -- rien n'est lance.")
            close_logs()
            return RC_REFUSED
        else:
            _say(fh, f"admission : charge de commit {charge} % <= "
                     f"{args.max_commit_charge_pct} % -- demarrage autorise")

    # --- Exclusion N=1 (#21661) ------------------------------------------------
    if args.exclusive_lock:
        lock_fh = _acquire_exclusive_lock(args.exclusive_lock)
        if lock_fh is None:
            _say(fh, f"REFUS : verrou exclusif {args.exclusive_lock} deja pris -- "
                     f"un autre entrainement CoursIA tourne sur la machine (N = 1).")
            close_logs()
            return RC_REFUSED
        _say(fh, f"exclusion N=1 : verrou {args.exclusive_lock} pris pour la "
                 f"duree du job")

    # --- Garde GPU : gate puis reservation held AVANT l'enfant (#22456) ------
    # Sequence codee du regisseur : consulter le gate, puis porter le held,
    # et seulement ensuite lancer l'enfant -- la reservation existe avant le
    # premier appel CUDA. gpu_res reste None tant que le held n'est pas ecrit
    # (et pour toujours sans --gpu-entity) : le teardown n'ecrit alors rien.
    gpu_res = None
    if args.gpu_entity:
        verdict, detail = _gpu_gate_check(
            args.gpu_entity, args.gpu_holder, args.gpu_ledger_remote)
        if verdict not in GPU_GATE_GREEN_VERDICTS:
            if verdict is None:
                _say(fh, f"REFUS : gate {GPU_LEDGER_NAME} INDISPONIBLE pour "
                         f"{args.gpu_entity} -- {detail} -- fail-CLOSED : on ne "
                         f"lance pas sur un device dont on ne peut pas lire "
                         f"l'etat.")
            else:
                _say(fh, f"REFUS : gate {GPU_LEDGER_NAME} verdict {verdict} pour "
                         f"{args.gpu_entity} ({detail}) -- rien n'est lance.")
            close_logs()
            return RC_REFUSED
        _say(fh, f"admission GPU : verdict {verdict} pour {args.gpu_entity} "
                 f"-- demarrage autorise")
        held_started_at = _utc_now_iso()
        expected_end = args.gpu_expected_end
        if not expected_end:
            # Un hold SANS borne n'est jamais STALE : un lanceur tue
            # brutalement (kill -9, reboot) laisse la reservation vivante
            # pour TOUTE la flotte, sans aucun chemin de sortie. La borne
            # par defaut rend ce cas detectable par l'organe ; elle est
            # journalisee, donc jamais silencieuse.
            expected_end = (
                datetime.now(timezone.utc) + timedelta(hours=GPU_HOLD_DEFAULT_HOURS)
            ).strftime("%Y-%m-%dT%H:%M:%S.%fZ")
            _say(fh, f"gpu-reservation : --gpu-expected-end absent -- borne par "
                     f"defaut appliquee : {expected_end} "
                     f"(+{GPU_HOLD_DEFAULT_HOURS} h)")
        fields = _gpu_build_fields(
            state="held",
            started_at=held_started_at,
            expected_end=expected_end,
            holder=args.gpu_holder,
            workload=args.gpu_workload,
            issue=args.gpu_issue,
        )
        ok, obs_detail = _gpu_append_observation(
            args.gpu_entity, fields, args.gpu_holder or "run_guarded")
        if not ok:
            _say(fh, f"REFUS : la reservation {GPU_LEDGER_NAME} n'a pas pu etre "
                     f"ecrite pour {args.gpu_entity} -- {obs_detail} -- "
                     f"fail-CLOSED : on ne lance pas sur un device dont on n'a "
                     f"pas porte la reservation.")
            close_logs()
            return RC_REFUSED
        gpu_res = {
            "entity": args.gpu_entity,
            "holder": args.gpu_holder,
            "workload": args.gpu_workload,
            "issue": args.gpu_issue,
            "held_started_at": held_started_at,
        }
        _say(fh, f"gpu-reservation : held ecrit pour {args.gpu_entity} "
                 f"(debut {held_started_at}"
                 + (f", observation {obs_detail}" if obs_detail else "")
                 + ") AVANT le lancement -- la reservation existe avant le "
                 "premier appel CUDA")
        # Publication immediate : la reservation doit etre VISIBLE de la
        # flotte (le gate lit la branche). Un held non publie rend `UNPOSTED`
        # au gate et bloquerait le lancement suivant, y compris le nôtre.
        published, pub_detail = _gpu_publish_reservations(
            args.gpu_entity.split("#")[0], args.gpu_ledger_remote)
        if not published:
            _say(fh, f"REFUS : la reservation {GPU_LEDGER_NAME} n'a pas pu etre "
                     f"PUBLIEE pour {args.gpu_entity} -- {pub_detail} -- "
                     f"fail-CLOSED : une reservation invisible de la flotte "
                     f"n'est pas une reservation. Remediation : "
                     f"python scripts/coordination/debt_ledger.py publish --git "
                     f"--ledger {GPU_LEDGER_NAME} --emit")
            # Le `held` EST ecrit (dans le spool) : le refus doit le CLORE.
            # Sans ce release, la reservation reste VIVANTE -- et, si le push
            # a atterri avant l'echec de sa verification, elle est VISIBLE de
            # la flotte sur un device qui ne porte aucun job (le hold de
            # l'admission et le released de l'admission doivent etre
            # symetriques, comme tous les autres chemins de sortie).
            _release_gpu_if_held(
                gpu_res, fh, "publication de la reservation refusee",
                args.gpu_ledger_remote)
            close_logs()
            return RC_REFUSED
        _say(fh, f"gpu-reservation : held PUBLIE sur {GPU_LEDGER_BRANCH} "
                 f"-- la flotte voit la reservation ({pub_detail})")

    job_limit = int(args.job_memory_limit_gib * GiB)
    if args.no_job:
        job = None
        _say(fh, "AUCUN Job Object pose (--no-job) : ni anti-orphelin, ni "
                 "plafond memoire du job -- l'enfant peut survivre a ce "
                 "lanceur et sa memoire n'est pas plafonnee par le noyau.")
    else:
        job = _win_job_kill_on_close(job_limit)
    if os.name == "nt" and job is None and not args.no_job:
        _say(fh, "ATTENTION : Job Object KILL_ON_JOB_CLOSE indisponible sur cette "
                 "machine -- l'anti-orphelin ne sera pas pose.")
    elif os.name != "nt":
        _say(fh, "anti-orphelin : non implemente hors Windows (pas de Job "
                 "Object) -- la garde mesure et tue, mais un enfant survivrait "
                 "a la mort de ce lanceur.")

    t0 = time.time()
    spawn_kwargs = dict(
        cwd=args.cwd,
        stdout=child_out if child_out is not None else None,
        stderr=(err_fh if err_fh is not None
                else (subprocess.STDOUT if child_out is not None else None)))
    # Creation SUSPENDUE quand un job est pose : la fenetre entre le demarrage
    # du fils et son assignation au job doit etre nulle, sinon le fils peut
    # creer ses enfants avant d'etre dans le job -- et ces petits-lains
    # n'heriteront pas du plafond memoire (#21661).
    suspended = False
    if os.name == "nt" and job is not None:
        try:
            proc = subprocess.Popen(cmd, creationflags=CREATE_SUSPENDED, **spawn_kwargs)
            suspended = True
        except (OSError, ValueError):
            suspended = False
    if not suspended:
        try:
            proc = subprocess.Popen(cmd, **spawn_kwargs)
        except (OSError, ValueError) as exc:
            _say(fh, f"la commande n'a pas demarre : {type(exc).__name__}: {exc}")
            _release_gpu_if_held(gpu_res, fh, "la commande n'a pas demarre",
                                 args.gpu_ledger_remote)
            close_logs()
            return RC_NOSTART

    assigned = _assign_to_job(job, proc)
    if os.name == "nt" and not assigned and not args.allow_no_job and not args.no_job:
        _say(fh, "REFUS : l'enfant n'a pas pu etre place dans le Job Object -- "
                 "il pourrait survivre a ce lanceur (orphelin). Relancer avec "
                 "--allow-no-job pour l'assumer explicitement.")
        _kill_tree(proc.pid)
        _release_gpu_if_held(gpu_res, fh, "enfant non place dans le Job Object",
                             args.gpu_ledger_remote)
        close_logs()
        return RC_REFUSED
    if os.name == "nt" and assigned:
        _say(fh, f"anti-orphelin : pid {proc.pid} place dans le Job Object "
                 "KILL_ON_JOB_CLOSE -- il mourra avec ce lanceur")
        if job_limit:
            _say(fh, f"plafond job : {args.job_memory_limit_gib:.2f} GiB de "
                     f"memoire commitee (processus + enfants) -- au-dela, les "
                     f"allocations echouent au lieu de swapper")
    elif os.name == "nt":
        _say(fh, f"anti-orphelin DESACTIVE (--allow-no-job) : pid {proc.pid} "
                 "survivrait a ce lanceur")

    if suspended:
        if _resume_suspended(proc):
            _say(fh, f"enfant demarre en suspension puis repris apres "
                     f"assignation -- la fenetre d'heritage du plafond est fermee")
        else:
            _say(fh, "REFUS : l'enfant demarre en suspension n'a pas pu etre "
                     "repris -- il est tue plutot que lancer hors plafond.")
            _kill_tree(proc.pid)
            _release_gpu_if_held(gpu_res, fh, "enfant suspendu non repris",
                             args.gpu_ledger_remote)
            close_logs()
            return RC_NOSTART

    if args.pid_file:
        try:
            Path(args.pid_file).parent.mkdir(parents=True, exist_ok=True)
            Path(args.pid_file).write_text(str(proc.pid), encoding="utf-8")
            _say(fh, f"pid du processus lance : {proc.pid} -> {args.pid_file}")
        except OSError as exc:
            _say(fh, f"ATTENTION : pid file {args.pid_file} non ecrit "
                     f"({type(exc).__name__}: {exc})")

    peak_rss, min_free, reason = 0, free0, None
    next_report = t0 + args.report_every if args.report_every > 0 else None
    try:
        while proc.poll() is None:
            time.sleep(args.poll)
            rss, free = _rss_bytes(proc.pid), _available_bytes()
            peak_rss = max(peak_rss, rss)
            min_free = min(min_free, free)
            if rss > limit:
                reason = (f"plafond processus franchi : RSS {rss / GiB:.1f} GiB "
                          f"> {args.limit_gib:.1f} GiB")
                break
            if free < reserve:
                reason = (f"plancher machine franchi : RAM libre "
                          f"{free / GiB:.1f} GiB < {args.reserve_gib:.1f} GiB")
                break
            if next_report is not None and time.time() >= next_report:
                _say(fh, f"suivi : RSS {rss / GiB:.1f} GiB, libre {free / GiB:.1f} GiB, "
                         f"{int(time.time() - t0)} s")
                next_report = time.time() + args.report_every
    except KeyboardInterrupt:
        _say(fh, "interruption clavier : arret de l'arbre")
        _kill_tree(proc.pid)
        _release_gpu_if_held(gpu_res, fh, "interruption clavier",
                         args.gpu_ledger_remote)
        close_logs()
        return RC_INTERRUPT

    if reason is not None:
        _say(fh, f"ARRET -- {reason} ; arbre tue apres {int(time.time() - t0)} s")
        _kill_tree(proc.pid)
        try:
            proc.wait(timeout=30)
        except subprocess.TimeoutExpired:
            pass
        _say(fh, f"bilan : pic RSS {peak_rss / GiB:.1f} GiB, RAM libre minimale "
                 f"{min_free / GiB:.1f} GiB, duree {int(time.time() - t0)} s")
        _release_gpu_if_held(gpu_res, fh, f"arret garde ({reason})",
                         args.gpu_ledger_remote)
        close_logs()
        return RC_LIMIT if reason.startswith("plafond") else RC_FLOOR

    rc = proc.returncode
    _say(fh, f"termine rc={rc} en {int(time.time() - t0)} s -- sous les deux "
             f"plafonds (pic RSS {peak_rss / GiB:.1f} GiB / {args.limit_gib:.1f} GiB, "
             f"RAM libre minimale {min_free / GiB:.1f} GiB)")
    released_ok = _release_gpu_if_held(gpu_res, fh, "sortie normale", args.gpu_ledger_remote)
    close_logs()
    if gpu_res is not None and not released_ok and rc == RC_OK:
        # Le travail a reussi mais la reservation n'est pas liberee : code
        # dedie pour qu'une chaine d'appels ne croie pas que tout va bien.
        # Si rc est deja non nul, on le garde : l'echec de l'enfant reste
        # l'information principale, le released manquant est dans le journal.
        return RC_LEDGER
    return rc


if __name__ == "__main__":
    sys.exit(main())
