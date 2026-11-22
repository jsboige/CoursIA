#!/usr/bin/env python3
"""Organe d'hygiene de session — rend VISIBLE la derive quotidienne d'un arbre de travail.

Pourquoi cet organe existe
--------------------------
Le geste est deja prescrit (skill ``/coordinate`` phase 2.0 : « revenir sur main, pull,
submodules »). Il n'a pourtant pas ete fait pendant des jours sur ai-01, et la raison est
mesurable : ``git checkout main`` **echouait en silence** parce qu'un worktree residuel
detenait ``main``. L'arbre est donc reste parke sur une branche de feature, et l'organe B.0
qu'on y lancait avait 437 lignes de moins que celui de ``main`` — assez pour inverser des
verdicts de merge.

Ajouter une ligne de prose disant « pense a revenir sur main » n'aurait rien change : la
consigne existait. Ce qui manquait etait un **signal d'echec**. C'est ce que rend ce script.

Il ne repare rien tout seul : il mesure, il nomme, et il rend un code de sortie.

Usage
-----
    python scripts/coordination/session_hygiene.py             # rapport humain
    python scripts/coordination/session_hygiene.py --json      # sortie structuree
    python scripts/coordination/session_hygiene.py --quiet     # seulement RED et AMBER

Codes de sortie : 0 = rien de rouge · 1 = au moins un RED · 2 = erreur d'execution.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Callable

# Motifs de noms de fichiers qui portent typiquement un secret. On ne lit JAMAIS la valeur :
# un secret ne s'imprime pas pour prouver qu'il est la.
SECRET_NAME_PATTERNS = [
    re.compile(r"(^|/)\.env($|[.\-])", re.IGNORECASE),
    re.compile(r"\.env\.(bak|sav|backup|old|orig)", re.IGNORECASE),
    re.compile(r"(^|/)(id_rsa|id_ed25519|.*\.pem|.*\.p12|.*\.pfx)$", re.IGNORECASE),
    re.compile(r"(secrets?|credentials?|token)s?\.(json|ya?ml|txt|ini)$", re.IGNORECASE),
]

# Chemins d'organes dont une divergence vs origin/main fausse une mesure publiee.
ORGAN_PATHS = [
    "scripts/check_unaddressed_nits.py",
    "scripts/check_lane_claim.py",
    "scripts/pick_idle_grain.py",
]

RED, AMBER, GREEN = "RED", "AMBER", "GREEN"

# Organes planifies LOCAUX (#17748). Une tache Windows survit a la disparition de son
# siege : mesure du 2026-09-25, le worktree D:\CoursIA-wt-merge-ready purge, la tache
# `merge_ready` s'est declenchee toutes les 20 min avec LastTaskResult=2 -- python ne
# trouvait plus le script -- sans ecrire une ligne de journal. 2 h 20 sans merge
# automatique, et rien ne rougissait : la tache etait « prete », le journal se taisait.
# (nom, dossier d'etat sous %LOCALAPPDATA%\CoursIA, intervalle nominal en minutes)
SCHEDULED_ORGANS = [
    ("merge_ready", "merge_ready", 20),
]
# Un journal plus vieux que ce nombre d'intervalles = organe muet.
SILENT_INTERVALS = 3

# Journal de TRAVAIL par organe : la source qui avance a chaque unite de travail
# (pour merge_ready, un verdict par PR evaluee, vide et flush a chaque ligne).
#
# Pourquoi il faut le lire en plus du log de lancement : le lanceur ouvre le log
# du jour et y redirige la sortie de l'organe, mais cette sortie est BUFFERISEE
# cote enfant -- le mtime du log se fige donc des le debut du tir et ne bouge
# plus tant que le tir dure. Mesure du 22/11 sur merge_ready : log fige a 07:03
# (tir lance a 06:56, encore en cours a 11:32) et journal de travail ecrit a
# 11:32 ; l'organe annonçait « journal muet depuis 269 min » alors qu'il
# evaluait 236 PR. Un ROUGE de vivacite ne vaut que si AUCUNE source ne bouge.
JOURNAL_TRAVAIL = {
    "merge_ready": "journal.jsonl",
}

# #19131 : le journal d'un organe porte son propre verdict de fin de tir
# (`=== run end rc=N ===`) et, sur echec de demarrage, la ligne
# `... : impossible de demarrer -- ...` (merge_ready.py:1158, rc 2). Mesurer
# l'AGE d'un journal ne dit rien de son CONTENU : du 2026-10-01 12:09Z au
# 2026-10-04 18:15Z, merge_ready sortait en exit 2 a chaque tir et le controle
# de #17748 affichait « journal ecrit il y a 16 min ». Un journal qui repete un
# echec de demarrage est frais.
_STARTUP_FAILURE = re.compile(r"impossible de demarrer", re.IGNORECASE)
_RUN_END_RC = re.compile(r"run end rc=(\d+)", re.IGNORECASE)
# Vocabulaire d'echec, volontairement borne : il ne sert QU'A qualifier la
# repetition d'une meme ligne de journal d'organe (regime machine, pas prose
# humaine -- l'elargissement d'un filet a mots de prose reste ecarte, #14682).
_JOURNAL_FAILURE_WORDS = re.compile(
    r"impossible|échec|echec|erreur|\berror\b|\bfailed?\b|traceback", re.IGNORECASE)
# Queue de journal relue (lecture bornee) et nombre de tirs identiques qui alertent.
_JOURNAL_TAIL_LINES = 8
_CONSECUTIVE_FAILURES = 2


def _age_min(now: float, path: Path) -> int:
    """Age en minutes d'une source de vivacite (mtime). Entier, jamais negatif."""
    return max(0, int((now - path.stat().st_mtime) // 60))


def _journal_tail(path: Path, limit: int = _JOURNAL_TAIL_LINES) -> list[str]:
    """Dernieres lignes non vides du journal (lecture bornee : 8 Ko suffisent)."""
    try:
        with path.open("rb") as fh:
            fh.seek(0, os.SEEK_END)
            fh.seek(max(0, fh.tell() - 8192))
            raw = fh.read().decode("utf-8", errors="replace")
    except OSError:
        return []
    return [ln.strip() for ln in raw.splitlines() if ln.strip()][-limit:]


def _journal_verdict(lines: list[str]) -> tuple[str, str, int]:
    """(niveau, ligne_lue, tirs_identiques) de la queue d'un journal d'organe.

    RED si la derniere ligne porte une signature d'echec -- `impossible de
    demarrer`, ou un code de sortie non nul que l'organe ecrit lui-meme.
    AMBER si plusieurs tirs consecutifs rendent la MEME ligne d'echec sans
    signature reconnue. Un tir nominal (`rc=0`) ou une ligne isolee sans
    vocabulaire d'echec restent GREEN : la regularite d'un organe sain ne
    doit pas alerter.
    """
    if not lines:
        return GREEN, "", 0
    last = lines[-1]
    same = 1
    for prev in reversed(lines[:-1]):
        if prev != last:
            break
        same += 1
    m = _RUN_END_RC.search(last)
    if m and int(m.group(1)) == 0:
        return GREEN, last, same
    if _STARTUP_FAILURE.search(last) or m:
        return RED, last, same
    if same >= _CONSECUTIVE_FAILURES and _JOURNAL_FAILURE_WORDS.search(last):
        return AMBER, last, same
    return GREEN, last, same


@dataclass
class Check:
    name: str
    level: str
    detail: str
    fix: str = ""
    data: dict = field(default_factory=dict)


def git(*args: str, cwd: Path | None = None) -> str:
    """Lance git et rend stdout strippe. Une commande qui echoue rend une chaine vide."""
    try:
        out = subprocess.run(
            ["git", *args],
            cwd=cwd,
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=60,
        )
    except (OSError, subprocess.SubprocessError):
        return ""
    return out.stdout.strip() if out.returncode == 0 else ""


def git_rc(*args: str, cwd: Path | None = None) -> tuple[int, str, str]:
    """git + code retour + stderr : pour les mesures ou l'ECHEC doit se distinguer du VIDE.

    Le helper ``git()`` rend une chaine vide dans les deux cas, ce qui est juste quand
    l'absence de sortie EST le fait mesure (« pas de stash », « aucune divergence »). C'est
    faux des qu'un verdict en depend : une mesure impossible publiee comme un constat
    fabrique une accusation (nit (b) de #17496 — un ``git diff`` en erreur se lisait comme
    « la branche ne livre rien », donc « parkee sans raison »).

    Rend ``(rc, stdout strippe, stderr strippe)`` ; ``rc = -1`` quand la commande n'a pas
    pu etre lancee du tout.
    """
    try:
        out = subprocess.run(
            ["git", *args],
            cwd=cwd,
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=60,
        )
    except (OSError, subprocess.SubprocessError) as exc:
        return -1, "", str(exc)
    return out.returncode, out.stdout.strip(), out.stderr.strip()


def _premiere_ligne(err: str) -> str:
    """Premiere ligne d'un stderr git, bornee : c'est elle qui nomme la panne."""
    return err.splitlines()[0][:160] if err else "(sans message)"


def repo_root() -> Path:
    root = git("rev-parse", "--show-toplevel")
    if not root:
        print("session_hygiene: pas un depot git", file=sys.stderr)
        sys.exit(2)
    return Path(root)


def check_fetch(root: Path) -> list[Check]:
    """Le fetch est la premiere mesure : s'il echoue, tout ce qui suit compare a un origin/main perime.

    Le helper ``git()`` rend une chaine vide sur echec, ce qui est juste pour une lecture mais
    faux ici : un fetch rate en silence ferait afficher des verts (``behind``, ``organe:*``)
    calcules contre une reference d'hier. L'organe denonce le geste qui echoue sans le dire ;
    il ne peut pas faire la meme chose a sa premiere etape.
    """
    try:
        out = subprocess.run(
            ["git", "fetch", "origin", "--quiet"],
            cwd=root,
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=120,
        )
        rc, err = out.returncode, out.stderr.strip()
    except (OSError, subprocess.SubprocessError) as exc:
        rc, err = -1, str(exc)
    if rc == 0:
        return [Check("fetch", GREEN, "origin a jour")]
    first = err.splitlines()[0][:160] if err else f"rc={rc}"
    return [
        Check(
            "fetch",
            RED,
            f"git fetch origin a echoue ({first}) : chaque mesure ci-dessous compare a un "
            "origin/main perime, un vert n'y vaut rien",
            fix="retablir le reseau ou le credential, puis relancer",
        )
    ]


def check_branch(root: Path) -> list[Check]:
    """Sur quelle branche est l'arbre, et de combien est-il en retard sur origin/main ?"""
    checks: list[Check] = []
    branch = git("rev-parse", "--abbrev-ref", "HEAD", cwd=root) or "(detache)"

    behind = git("rev-list", "--count", "HEAD..origin/main", cwd=root)
    behind_n = int(behind) if behind.isdigit() else -1

    if branch == "main":
        if behind_n > 0:
            checks.append(
                Check(
                    "branche",
                    AMBER,
                    f"sur main mais {behind_n} commits en retard",
                    "git pull --ff-only",
                    {"branch": branch, "behind": behind_n},
                )
            )
        else:
            checks.append(Check("branche", GREEN, "sur main, a jour", data={"branch": branch}))
    else:
        # Une branche de feature n'est pas un defaut EN SOI. Elle le devient quand son
        # travail est deja sur main : l'arbre est alors parke sans raison.
        #
        # Deux tests naifs echouent ici, et tous deux ont ete mesures sur le cas reel :
        #   * `merge-base --is-ancestor` : aveugle au squash-merge, qui efface l'ascendance.
        #   * le diff TROIS-POINTS `origin/main...branche` : apres un squash, la merge-base
        #     precede la livraison, donc il re-presente comme « ajoute » ce qui est DEJA sur
        #     main (mesure : 24 insertions annoncees pour zero contenu manquant).
        # Le test juste compare les ETATS FINAUX, restreint aux fichiers que la branche
        # touche : si le blob de la branche est identique a celui de main partout ou elle a
        # ecrit, elle ne livre plus rien.
        # Mesure, et non lecture : un diff en ERREUR (origin/main absent, objet corrompu,
        # credential) rend une sortie vide comme un diff sans difference. Les confondre
        # publierait « parkee sans raison » sur un arbre qu'on n'a pas su mesurer.
        rc_touch, touched_out, err_touch = git_rc(
            "diff", "--name-only", f"origin/main...{branch}", cwd=root
        )
        delivers = ""
        mesure_impossible = ""
        if rc_touch != 0:
            mesure_impossible = (
                f"git diff --name-only origin/main...{branch} a echoue "
                f"(rc={rc_touch}, {_premiere_ligne(err_touch)})"
            )
        else:
            touched = touched_out.splitlines()
            if touched:
                rc_stat, delivers, err_stat = git_rc(
                    "diff", "--stat", "origin/main", branch, "--", *touched, cwd=root
                )
                if rc_stat != 0:
                    mesure_impossible = (
                        f"git diff --stat origin/main {branch} a echoue "
                        f"(rc={rc_stat}, {_premiere_ligne(err_stat)})"
                    )
                    delivers = ""

        has_upstream = bool(git("rev-parse", "--abbrev-ref", "@{u}", cwd=root))
        if not has_upstream:
            unpushed = "jamais poussee"
        else:
            unpushed = git("log", "--oneline", "@{u}..HEAD", cwd=root)

        if mesure_impossible:
            level = AMBER
            why = (
                f"mesure impossible : {mesure_impossible} — le verdict « parke sans "
                "raison » est suspendu : un echec de mesure n'est pas une preuve d'absence"
            )
        else:
            level = RED if (not delivers and not unpushed) else AMBER
            why = (
                "son contenu est deja integralement sur origin/main (les fichiers qu'elle "
                "touche y portent le meme blob) et rien n'attend d'etre pousse : "
                "l'arbre est parke sans raison"
                if level == RED
                else f"{behind_n} commits de retard"
                + (f", {len(unpushed.splitlines())} non pousse(s)" if unpushed and has_upstream else "")
                + ("" if has_upstream else ", branche jamais poussee")
            )
        checks.append(
            Check(
                "branche",
                level,
                f"sur '{branch}' — {why}",
                "git checkout main && git pull --ff-only",
                {
                    "branch": branch,
                    "behind": behind_n,
                    "unpushed": bool(unpushed),
                    "mesure_impossible": bool(mesure_impossible),
                },
            )
        )
    return checks


def check_main_hostage(root: Path) -> list[Check]:
    """``main`` detenu par un worktree qui n'est pas l'arbre principal = ``git checkout main`` echoue en silence.

    L'arbre principal est la PREMIERE entree de ``git worktree list`` : c'est lui
    qui heberge le depot commun, et c'est dans lui que ``git checkout main`` doit
    aboutir. Mesure du 2026-11-21 (issue #27696) : lance depuis un worktree
    secondaire, le predicat precedent prenait ``root`` pour l'arbre principal et
    signalait l'arbre principal -- detenteur legitime de ``main`` -- comme
    ravisseur, avec un remede destructeur (``git worktree remove`` sur l'arbre
    partage).
    """
    raw = git("worktree", "list", "--porcelain", cwd=root)
    entries: list[tuple[str, str]] = []
    for line in raw.splitlines():
        if line.startswith("worktree "):
            entries.append((line[len("worktree ") :].strip(), ""))
        elif line.strip().startswith("branch ") and entries:
            path, _ref = entries[-1]
            entries[-1] = (path, line.strip()[len("branch ") :])

    principal = Path(entries[0][0]).resolve() if entries else None
    holder = None
    for path, ref in entries[1:]:
        if ref in ("refs/heads/main", "refs/heads/master"):
            holder = path

    count = len(entries)
    checks = []
    if holder:
        checks.append(
            Check(
                "main-otage",
                RED,
                f"'main' est detenu par le worktree secondaire {holder} — un "
                f"`git checkout main` dans l'arbre principal ECHOUE, et son message "
                f"se perd dans le bruit",
                f"lui faire quitter main (git -C {holder} checkout <branche>) ou, "
                f"s'il est propre et inutile, git worktree remove {holder}",
                {"holder": holder, "principal": str(principal) if principal else None},
            )
        )
    else:
        checks.append(
            Check("main-otage", GREEN, "main n'est detenu par aucun worktree secondaire")
        )

    if count > 40:
        lvl = RED if count > 80 else AMBER
        checks.append(
            Check(
                "worktrees",
                lvl,
                f"{count} worktrees enregistres — inflation. ATTENTION : ce compte ne dit "
                f"PAS qu'il y a quelque chose a purger (mesure du 18/09 : 59 enregistres, "
                f"removable=0, tous legitimement detenus). Seul le script tranche.",
                "python scripts/ci/prune_merged_worktrees.py  (puis --apply)",
                {"count": count},
            )
        )
    else:
        checks.append(Check("worktrees", GREEN, f"{count} worktrees", data={"count": count}))
    return checks


def check_organs(root: Path) -> list[Check]:
    """Un organe qui diverge de origin/main mesure autre chose que ce que la regle designe."""
    checks = []
    for rel in ORGAN_PATHS:
        if not (root / rel).exists():
            continue
        stat = git("diff", "--stat", "origin/main", "--", rel, cwd=root)
        if stat:
            nums = re.search(r"(\d+) insertion.*?(\d+) deletion", stat)
            delta = f"{nums.group(1)}+/{nums.group(2)}-" if nums else "diverge"
            checks.append(
                Check(
                    f"organe:{Path(rel).name}",
                    RED,
                    f"diverge de origin/main ({delta}) — toute mesure publiee avec lui "
                    f"est celle de CETTE branche, pas celle du gate",
                    f'git show origin/main:{rel} > "$SCRATCH/organ/{Path(rel).name}"',
                    {"path": rel, "delta": delta},
                )
            )
        else:
            checks.append(Check(f"organe:{Path(rel).name}", GREEN, "conforme a origin/main"))
    return checks


def check_untracked_secrets(root: Path) -> list[Check]:
    """Fichier non suivi ET non ignore dont le NOM evoque un secret = un `git add -A` du bord."""
    raw = git("status", "--porcelain", "--untracked-files=all", cwd=root)
    hits = []
    for line in raw.splitlines():
        if not line.startswith("?? "):
            continue
        path = line[3:].strip().strip('"')
        if any(p.search(path) for p in SECRET_NAME_PATTERNS):
            hits.append(path)
    if hits:
        return [
            Check(
                "secrets-non-ignores",
                RED,
                f"{len(hits)} fichier(s) non suivi(s) ET non ignore(s) au nom evocateur : "
                + ", ".join(hits[:5]),
                "ajouter le motif manquant a .gitignore (ne PAS supprimer le fichier)",
                {"paths": hits},
            )
        ]
    return [Check("secrets-non-ignores", GREEN, "aucun fichier sensible expose")]


def check_stash(root: Path) -> list[Check]:
    raw = git("stash", "list", cwd=root)
    n = len(raw.splitlines()) if raw else 0
    if n >= 3:
        return [
            Check(
                "stash",
                AMBER,
                f"{n} entrees de stash — du travail y dort peut-etre depuis des semaines",
                "git stash list --date=relative  puis trier",
                {"count": n},
            )
        ]
    return [Check("stash", GREEN, f"{n} entree(s) de stash", data={"count": n})]


def _launcher_repo(launcher: Path) -> Path | None:
    """Siege (--repo) nomme par le lanceur VBS de la tache, ou None s'il n'en nomme pas."""
    m = re.search(r'--repo\s+([^"\s]+)', launcher.read_text(encoding="utf-8", errors="replace"))
    return Path(m.group(1)) if m else None


def check_scheduled_organs(local_appdata: Path | None = None, now: float | None = None) -> list[Check]:
    """Vivacite des organes planifies installes sur CETTE machine (#17748).

    Deux predicats, dans l'ordre ou la panne se produit : le siege que nomme le
    lanceur existe, puis le journal avance. Un organe non installe ici est GREEN :
    ce n'est pas une panne, c'est une autre machine.

    La vivacite se mesure sur la source LA PLUS RECENTE parmi celles que l'organe
    ecrit : son log de lancement ET son journal de travail (cf. ``JOURNAL_TRAVAIL``).
    Un tir long fige le log (sortie bufferisee cote enfant) sans arreter l'organe :
    exiger que le log bouge declare a tort un organe en plein travail.
    """
    if local_appdata is None:
        local_appdata = Path(os.environ.get("LOCALAPPDATA", str(Path.home() / "AppData" / "Local")))
    now = time.time() if now is None else now
    checks = []
    for name, sub, interval in SCHEDULED_ORGANS:
        label = f"organe-planifie:{name}"
        state = local_appdata / "CoursIA" / sub
        launcher = state / "run_hidden.vbs"
        if not launcher.exists():
            checks.append(Check(label, GREEN, "non installe sur cette machine"))
            continue
        repo = _launcher_repo(launcher)
        if repo is not None and not repo.exists():
            checks.append(
                Check(
                    label,
                    RED,
                    f"siege {repo} absent : la tache se declenche et meurt avant d'ouvrir son journal",
                    f"git worktree add --detach {repo} origin/main",
                    {"repo": str(repo)},
                )
            )
            continue
        logs = sorted((state / "logs").glob("*.log"), key=lambda f: f.stat().st_mtime)
        last_log = logs[-1] if logs else None
        # Vivacite = la source LA PLUS RECENTE. L'organe n'est muet que si TOUTES
        # ses sources sont muettes : le log de lancement se fige pendant un tir
        # long (sortie bufferisee cote enfant), le journal de travail, lui,
        # avance a chaque verdict.
        sources: list[tuple[str, Path, int]] = []
        if last_log is not None:
            sources.append(("log de lancement", last_log, _age_min(now, last_log)))
        nom_journal = JOURNAL_TRAVAIL.get(name)
        if nom_journal:
            journal = state / nom_journal
            if journal.exists():
                sources.append(
                    (f"journal de travail ({nom_journal})", journal, _age_min(now, journal))
                )
        if not sources:
            checks.append(Check(label, AMBER, "installe, mais aucun journal : jamais tourne ?", data={"repo": str(repo)}))
            continue
        source_label, source_path, age_min = min(sources, key=lambda s: s[2])
        content_level, last_line, same = _journal_verdict(
            _journal_tail(last_log) if last_log is not None else [])
        excerpt = (last_line[:160] + "...") if len(last_line) > 160 else last_line
        data = {
            "age_min": age_min,
            "source": source_label,
            "source_path": str(source_path),
            "log": str(last_log) if last_log is not None else "",
            "last_line": last_line,
        }
        query = "schtasks /Query /TN CoursIA\\" + name + " /V /FO LIST  (Last Result, Task To Run)"
        if age_min > SILENT_INTERVALS * interval:
            checks.append(
                Check(
                    label,
                    RED,
                    f"journal muet depuis {age_min} min sur TOUTES ses sources "
                    f"(intervalle nominal {interval} min)"
                    + (f" -- derniere ligne : {excerpt}" if excerpt else ""),
                    query,
                    data,
                )
            )
        elif content_level == RED:
            repet = f" -- {same} tirs consecutifs identiques" if same >= _CONSECUTIVE_FAILURES else ""
            checks.append(
                Check(label, RED, f"journal frais mais le dernier tir a echoue : {excerpt}{repet}", query, data)
            )
        elif content_level == AMBER:
            checks.append(
                Check(label, AMBER, f"journal frais, meme echec repete {same} fois : {excerpt}", query, data)
            )
        else:
            checks.append(
                Check(
                    label,
                    GREEN,
                    f"journal ecrit il y a {age_min} min (source : {source_label})"
                    + (f" -- derniere ligne : {excerpt}" if excerpt else ""),
                    data=data,
                )
            )
    return checks


# Items que ce script ne PEUT pas mesurer (ils vivent cote MCP). On les rappelle nommement
# plutot que de laisser croire qu'un vert ici vaut hygiene complete.
MANUAL_REMINDERS = [
    ("inbox", 'roosync_messages(action:"inbox", status:"unread")'),
    ("dashboards", 'roosync_dashboard(action:"list") PUIS read section:"all" sur chaque cle pertinente — ENUMERER, jamais une liste apprise'),
    ("memoires", "MEMORY.md + coordinator-handover.md : remplacer ce qui est consomme"),
    ("ledgers", "scripts/coordination/debt_ledger.py — etat des ledgers partages"),
]


# --- verrou de lane : une session par lane, VISIBLE (incident du 14/11) -----
#
# Mesure du 2026-11-14 : sur myia-po-2027:CoursIA, une seconde session de la
# meme lane a pousse un commit sur la branche d'une PR pendant que la premiere
# y travaillait. `check_lane_claim.py` traite deux sessions d'une meme lane
# comme une reprise legitime (premisse « une lane = un agent actif », #14323)
# : il ne peut pas voir ce cas. Ce verrou rend le second processus VISIBLE,
# sur cette machine, au debut du cycle. Le mecanisme d'apparition des
# doublons n'est pas etabli : l'organe ne suppose pas de cause, il mesure.

#: Le verrou vit sous `.tmp/` (ignore par git) : un fichier par depot, une
#: entree par lane -- une machine peut porter plusieurs lanes.
LANE_LOCK_NAME = ".tmp/lane-session.json"


def _pid_windows(pid: int) -> tuple[bool, float | None]:
    """(vivant, heure de creation epoch s) d'un PID sous Windows.

    Un PID qu'on ne peut pas sonder (erreur 5, processus eleve) est VIVANT :
    on ne declare jamais mort un processus qu'on n'a pas pu interroger.
    L'heure de creation defait la reutilisation de numero : le PID est rendu
    a un autre processus, l'heure de creation ne le suit pas.

    Vivance par l'etat signale du handle (``WaitForSingleObject`` 0 ms) :
    ``GetExitCodeProcess`` seul est ambigu -- STILL_ACTIVE (259) est aussi un
    code de sortie legitime, et un processus termine qui a choisi 259 serait
    classe vivant. WAIT_OBJECT_0 = handle signale = termine ; WAIT_TIMEOUT =
    vivant ; toute autre valeur (dont WAIT_FAILED) reste un vivant
    conservateur.
    """
    import ctypes
    import ctypes.wintypes as wt

    process_query_limited_information = 0x1000
    synchronize = 0x00100000
    wait_object_0 = 0x0
    wait_timeout = 0x102
    k32 = ctypes.WinDLL("kernel32", use_last_error=True)
    # Signatures explicites : sans restype, ctypes echange un int 32 bits et
    # tronque un HANDLE natif 64 bits -- la cause racine du faux
    # session-double (#27363) etait un handle invalide, non une absence de
    # processus.
    k32.OpenProcess.restype = wt.HANDLE
    k32.OpenProcess.argtypes = (wt.DWORD, wt.BOOL, wt.DWORD)
    k32.WaitForSingleObject.restype = wt.DWORD
    k32.WaitForSingleObject.argtypes = (wt.HANDLE, wt.DWORD)
    k32.GetProcessTimes.restype = wt.BOOL
    k32.GetProcessTimes.argtypes = (wt.HANDLE, ctypes.POINTER(wt.FILETIME),
                                    ctypes.POINTER(wt.FILETIME),
                                    ctypes.POINTER(wt.FILETIME),
                                    ctypes.POINTER(wt.FILETIME))
    k32.CloseHandle.restype = wt.BOOL
    k32.CloseHandle.argtypes = (wt.HANDLE,)

    handle = k32.OpenProcess(process_query_limited_information | synchronize, False, pid)
    if not handle:
        # 5 = acces refuse (il vit, eleve) ; 87 = parametre invalide (absent).
        return (ctypes.get_last_error() == 5, None)
    try:
        # Un objet processus reste ouvrable apres sa terminaison tant qu'un
        # handle le reference. OpenProcess/GetProcessTimes seuls ne mesurent
        # donc PAS la vivance ; seul l'etat signale du handle la mesure.
        etat = k32.WaitForSingleObject(handle, 0)
        if etat not in (wait_object_0, wait_timeout):
            return (True, None)  # sonde incomplete : jamais une preuve de mort
        creation, exit_t, kern, user = (wt.FILETIME() for _ in range(4))
        if not k32.GetProcessTimes(handle, ctypes.byref(creation), ctypes.byref(exit_t),
                                   ctypes.byref(kern), ctypes.byref(user)):
            return (True, None)
        ticks = (creation.dwHighDateTime << 32) | creation.dwLowDateTime
        return (etat == wait_timeout, (ticks - 116444736000000000) / 1e7)
    finally:
        k32.CloseHandle(handle)


def _pid_posix(pid: int) -> tuple[bool, float | None]:
    """(vivant, None) sous POSIX : os.kill(pid, 0) comme sonde, jamais comme signal."""
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return (False, None)
    except PermissionError:
        return (True, None)
    except OSError:
        return (True, None)  # insondable n'est pas mort
    return (True, None)


def pid_etat(pid: int) -> tuple[bool, float | None]:
    """(vivant, heure de creation epoch s) d'un PID ; robuste a un PID mort."""
    if not isinstance(pid, int) or pid <= 0:
        return (False, None)
    if os.name == "nt":
        try:
            return _pid_windows(pid)
        except OSError:
            return (True, None)  # echec de sonde : pas une preuve de mort
    return _pid_posix(pid)


# --- processus de session : le PID du harnais, pas celui du script ----------
#
# `os.getpid()` designe le processus de CE script, qui vit le temps d'une
# commande : l'enregistrer rend le verrou inerte (review 5908186749, #26634).
# Le porteur d'une lane est le processus de session du harnais
# (`claude.exe`/`claude`, ou le `node` qui l'heberge) : on remonte la chaine
# des parents jusqu'a lui. Aucun ancetre reconnu = mesure impossible, jamais
# un vert (meme doctrine que `check_fetch`).

MAX_ANCETRE_SAUTS = 32
_CLAUDE_NOM = re.compile(r"^claude", re.IGNORECASE)
_NODE_NOM = re.compile(r"^node", re.IGNORECASE)


def _table_processus_windows() -> dict[int, tuple[int, str]]:
    """pid -> (ppid, nom d'image) par `CreateToolhelp32Snapshot` (ctypes seul).

    Aucune dependance externe, aucun sous-processus PowerShell : le harnais
    interdit les deux pour une mesure faite a chaque debut de cycle.
    """
    import ctypes
    import ctypes.wintypes as wt

    th32cs_snapprocess = 0x00000002
    invalid_handle = ctypes.c_void_p(-1).value

    class ProcessEntry32W(ctypes.Structure):
        _fields_ = [
            ("dwSize", wt.DWORD),
            ("cntUsage", wt.DWORD),
            ("th32ProcessID", wt.DWORD),
            ("th32DefaultHeapID", ctypes.c_size_t),
            ("th32ModuleID", wt.DWORD),
            ("cntThreads", wt.DWORD),
            ("th32ParentProcessID", wt.DWORD),
            ("pcPriClassBase", ctypes.c_long),
            ("dwFlags", wt.DWORD),
            ("szExeFile", ctypes.c_wchar * 260),
        ]

    k32 = ctypes.WinDLL("kernel32", use_last_error=True)
    k32.CreateToolhelp32Snapshot.argtypes = [wt.DWORD, wt.DWORD]
    k32.CreateToolhelp32Snapshot.restype = wt.HANDLE
    k32.Process32FirstW.argtypes = [wt.HANDLE, ctypes.POINTER(ProcessEntry32W)]
    k32.Process32FirstW.restype = wt.BOOL
    k32.Process32NextW.argtypes = [wt.HANDLE, ctypes.POINTER(ProcessEntry32W)]
    k32.Process32NextW.restype = wt.BOOL
    k32.CloseHandle.argtypes = [wt.HANDLE]
    k32.CloseHandle.restype = wt.BOOL

    snapshot = k32.CreateToolhelp32Snapshot(th32cs_snapprocess, 0)
    if not snapshot or snapshot == invalid_handle:
        return {}
    table: dict[int, tuple[int, str]] = {}
    try:
        entree = ProcessEntry32W()
        entree.dwSize = ctypes.sizeof(ProcessEntry32W)
        if not k32.Process32FirstW(snapshot, ctypes.byref(entree)):
            return {}
        while True:
            table[int(entree.th32ProcessID)] = (
                int(entree.th32ParentProcessID), entree.szExeFile)
            if not k32.Process32NextW(snapshot, ctypes.byref(entree)):
                break
    finally:
        k32.CloseHandle(snapshot)
    return table


def _table_processus_posix() -> dict[int, tuple[int, str]]:
    """pid -> (ppid, nom) lu dans `/proc`, avec `ps -eo pid=,ppid=,comm=` en repli."""
    table: dict[int, tuple[int, str]] = {}
    proc = Path("/proc")
    if proc.is_dir():
        for dossier in proc.iterdir():
            if not dossier.name.isdigit():
                continue
            try:
                brut = (dossier / "stat").read_text(encoding="utf-8", errors="replace")
            except OSError:
                continue
            try:
                # `comm` peut contenir espaces et parentheses : on prend la
                # DERNIERE parenthese fermante, puis les champs qui suivent.
                gauche = brut.index("(")
                droite = brut.rindex(")")
                pid = int(brut[:gauche])
                nom = brut[gauche + 1:droite]
                champs = brut[droite + 2:].split()
                table[pid] = (int(champs[1]), nom)  # champs[0]=etat, champs[1]=ppid
            except (ValueError, IndexError):
                continue
        if table:
            return table
    try:
        out = subprocess.run(
            ["ps", "-eo", "pid=,ppid=,comm="],
            capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=10,
        )
    except (OSError, subprocess.SubprocessError):
        return {}
    for ligne in out.stdout.splitlines():
        champs = ligne.split(None, 2)
        if len(champs) == 3 and champs[0].isdigit() and champs[1].isdigit():
            table[int(champs[0])] = (int(champs[1]), champs[2].strip())
    return table


def table_processus() -> dict[int, tuple[int, str]]:
    """Table des processus de la machine : pid -> (ppid, nom d'image)."""
    try:
        if os.name == "nt":
            return _table_processus_windows()
        return _table_processus_posix()
    except OSError:
        return {}  # table illisible = mesure impossible, jamais un faux vert


def trouver_ancetre_session(depart: int | None = None,
                            table: dict[int, tuple[int, str]] | None = None,
                            max_sauts: int = MAX_ANCETRE_SAUTS,
                            ) -> tuple[int, str] | None:
    """(pid, nom) du processus de session du harnais, au-dessus de `depart`.

    Remonte la chaine des parents (`ParentProcessId`), bornee (`max_sauts`) et
    protegee contre les cycles. Un ancetre `claude*` l'emporte sur un `node*`
    (le harnais peut tourner sous Node : `node .../claude`). `depart` lui-meme
    n'est jamais candidat : c'est le processus de CE script. Aucun ancetre
    reconnu -> None : l'appelant rend une mesure impossible, pas un vert.
    """
    if table is None:
        table = table_processus()
    pid = os.getpid() if depart is None else depart
    chaine: list[tuple[int, str]] = []
    vus = {pid}
    courant = pid
    for _ in range(max_sauts):
        entree = table.get(courant)
        if entree is None:
            break
        ppid = entree[0]
        if ppid <= 0 or ppid in vus:
            break
        vus.add(ppid)
        parent = table.get(ppid)
        chaine.append((ppid, parent[1] if parent else ""))
        if parent is None:
            break
        courant = ppid
    for motif in (_CLAUDE_NOM, _NODE_NOM):
        for anc_pid, anc_nom in chaine:
            if anc_nom and motif.match(anc_nom):
                return (anc_pid, anc_nom)
    return None


def _lire_verrou(path: Path) -> dict:
    """Le verrou lu : dict lane -> entree ; illisible = absent (remplace plus tard)."""
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return {}
    return data if isinstance(data, dict) else {}


def _ecrire_verrou(path: Path, verrous: dict) -> None:
    """Ecriture remplacee atomiquement : deux demarrages simultanes ne se bribent pas."""
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.parent / f"lane-session.{os.getpid()}.new"
    tmp.write_text(json.dumps(verrous, ensure_ascii=False, indent=1), encoding="utf-8")
    os.replace(tmp, path)


def _entree_verrou(pid: int, session_id: str, maintenant: float | None,
                   etat_pid=pid_etat, nom: str = "") -> dict:
    """Une entree de verrou : PID, heure de debut UTC explicite, session, machine."""
    _, creation = etat_pid(pid)
    debut = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(maintenant or time.time()))
    return {"pid": pid, "debut": debut, "debut_proc": creation,
            "session": session_id or os.environ.get("CLAUDE_SESSION_ID", ""),
            "proc": nom,
            "machine": os.environ.get("COMPUTERNAME")
            or os.environ.get("HOSTNAME") or ""}


def check_lane_lock(root: Path, lane: str, pid: int | None = None,
                    session_id: str = "", maintenant: float | None = None,
                    etat_pid=pid_etat,
                    session_proc: Callable[[], tuple[int, str] | None] | None = None,
                    ) -> list[Check]:
    """Verrou de lane : un second processus VIVANT sous la meme lane, sur ce depot.

    Pose `<repo>/.tmp/lane-session.json` et le lit d'abord. Le PID enregistre
    est celui du **processus de session du harnais** (`session_proc`, par
    defaut `trouver_ancetre_session`), jamais `os.getpid()` : ce script meurt
    a la fin de sa commande, et un PID de script mort a chaque cycle rendait le
    verrou inerte (review 5908186749, #26634). Un PID de session vivant
    different du mien est un ROUGE nomme ; une session enregistree non vide
    qui differe de la mienne est dite explicitement dans le detail. Aucun
    ancetre de session trouve = AMBER « non mesurable », sans ecriture.

    Deux sessions d'une meme lane sont indiscernables pour le protocole de
    claim (#14323), et c'est le doublon qui se supprime -- `CronList` puis
    `CronDelete` DANS la session qui le porte (regle de flotte : une session
    par lane). Robuste a un PID mort (reprise silencieuse du verrou) et, sous
    Windows, a la reutilisation du numero (l'heure de creation ne suit pas le
    numero). Les entrees des AUTRES lanes du depot sont preservees.
    """
    if pid is not None:
        mon_pid, mon_nom = pid, ""
    else:
        session_proc = session_proc or trouver_ancetre_session
        trouve = session_proc()
        if not trouve:
            # Fail-closed : sans ancetre de session, on ne sait pas QUI porte la
            # lane. Ce n'est pas un vert, et on n'ecrit aucun verrou qui aurait
            # l'air valide.
            return [Check(
                "session-double",
                AMBER,
                "non mesurable : aucun processus de session (claude/node) dans la chaine "
                "des parents -- le verrou n'est PAS pose et aucune session concurrente "
                "n'a pu etre ecartee",
                "lancer l'organe depuis une session du harnais (claude visible dans la "
                "chaine des parents)",
                {"lane": lane, "mesurable": False},
            )]
        mon_pid, mon_nom = trouve
    ma_session = session_id or os.environ.get("CLAUDE_SESSION_ID", "")
    path = root / LANE_LOCK_NAME
    verrous = _lire_verrou(path)
    entree = verrous.get(lane)
    autre = entree.get("pid") if isinstance(entree, dict) else None
    if isinstance(autre, int) and autre > 0 and autre != mon_pid:
        vivant, creation = etat_pid(autre)
        debut_proc = entree.get("debut_proc")
        # Numero reutilise : le PID vit mais CE processus a demarre a une autre
        # heure que celui qui a pose le verrou -- le porteur est mort.
        reuse = (vivant and isinstance(creation, float) and isinstance(debut_proc, float)
                 and abs(creation - debut_proc) > 1.0)
        if vivant and not reuse:
            sess_autre = str(entree.get("session") or "").strip()
            # Le PID compare deja les porteurs ; la session le dit explicitement
            # quand les deux cotes la connaissent (deux sessions, deux IDs).
            double_session = bool(sess_autre) and bool(ma_session) and sess_autre != ma_session
            nom_autre = f" ({entree.get('proc')})" if entree.get("proc") else ""
            marque = (
                f" -- la session enregistree '{sess_autre}' differe de la mienne "
                f"'{ma_session}'" if double_session else "")
            return [Check(
                "session-double",
                RED,
                f"le processus {autre}{nom_autre} (lane {lane}, demarre "
                f"{entree.get('debut') or '?'}) est VIVANT : une SECONDE session "
                f"tourne sous cette lane{marque}",
                "regle une session par lane : CronList puis CronDelete du cron du "
                "doublon DANS la session qui le porte ; cette session n'edite rien "
                "tant qu'il vit",
                {"lane": lane, "autre_pid": autre},
            )]
        verrous[lane] = _entree_verrou(mon_pid, ma_session, maintenant, etat_pid, mon_nom)
        _ecrire_verrou(path, verrous)
        return [Check(
            "session-double",
            GREEN,
            f"verrou repris : le processus precedent ({autre}) est mort"
            + (" (son numero a ete reutilise par un autre processus)" if reuse else ""),
            data={"lane": lane, "reprise": True},
        )]
    if isinstance(entree, dict) and autre == mon_pid:
        # Meme numero : verifier que c'est bien le MEME processus (un PID de
        # session recycle par un autre harnais est un porteur mort).
        _, creation = etat_pid(mon_pid)
        debut_proc = entree.get("debut_proc")
        recycle = (isinstance(creation, float) and isinstance(debut_proc, float)
                   and abs(creation - debut_proc) > 1.0)
        if not recycle:
            return [Check(
                "session-double", GREEN,
                f"verrou deja pose par ce processus (meme session, pid {mon_pid}"
                f"{', ' + mon_nom if mon_nom else ''})",
                data={"lane": lane, "pid": mon_pid, "proc": mon_nom})]
        verrous[lane] = _entree_verrou(mon_pid, ma_session, maintenant, etat_pid, mon_nom)
        _ecrire_verrou(path, verrous)
        return [Check(
            "session-double", GREEN,
            f"verrou repris : le numero {mon_pid} a ete reutilise par un autre processus",
            data={"lane": lane, "reprise": True},
        )]
    illisible = path.exists() and not verrous  # lu avant d'y poser sa propre entree
    verrous[lane] = _entree_verrou(mon_pid, ma_session, maintenant, etat_pid, mon_nom)
    _ecrire_verrou(path, verrous)
    detail = f"verrou de lane pose (pid {mon_pid}{', ' + mon_nom if mon_nom else ''})"
    if illisible:
        detail = f"verrou illisible, remplace -- {detail}"
    return [Check("session-double", GREEN, detail,
                  data={"lane": lane, "pid": mon_pid, "proc": mon_nom})]


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--json", action="store_true", help="sortie structuree")
    ap.add_argument("--quiet", action="store_true", help="n'afficher que RED et AMBER")
    ap.add_argument("--lane", default=None,
                    help="machine:workspace -- pose et verifie le verrou de session "
                         "de lane (debut de cycle)")
    ap.add_argument("--session-id", default=None,
                    help="ID de session du harnais (defaut : $CLAUDE_SESSION_ID)")
    args = ap.parse_args(argv)

    root = repo_root()

    checks: list[Check] = check_fetch(root)
    if args.lane:
        # Des le debut du cycle : un doublon vivant invalide tout ce qui suit.
        checks += check_lane_lock(root, args.lane,
                                  session_id=args.session_id or "")
    checks += check_branch(root)
    checks += check_main_hostage(root)
    checks += check_organs(root)
    checks += check_untracked_secrets(root)
    checks += check_stash(root)
    checks += check_scheduled_organs()

    reds = [c for c in checks if c.level == RED]
    ambers = [c for c in checks if c.level == AMBER]

    if args.json:
        print(
            json.dumps(
                {
                    "root": str(root),
                    "red": len(reds),
                    "amber": len(ambers),
                    "checks": [
                        {"name": c.name, "level": c.level, "detail": c.detail, "fix": c.fix, **c.data}
                        for c in checks
                    ],
                    "manual": [{"item": k, "command": v} for k, v in MANUAL_REMINDERS],
                },
                ensure_ascii=False,
                indent=2,
            )
        )
        return 1 if reds else 0

    glyph = {RED: "[RED]  ", AMBER: "[AMBER]", GREEN: "[ok]   "}
    for c in checks:
        if args.quiet and c.level == GREEN:
            continue
        print(f"{glyph[c.level]} {c.name}: {c.detail}")
        if c.fix and c.level != GREEN:
            print(f"          -> {c.fix}")

    print("\nNon mesurable ici — a faire a la main :")
    for item, cmd in MANUAL_REMINDERS:
        print(f"  . {item}: {cmd}")

    if reds:
        print(f"\n{len(reds)} point(s) ROUGE(s). Un vert de ce script ne vaut que pour ce qu'il teste.")
    return 1 if reds else 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except Exception as exc:  # 1 est reserve a « au moins un ROUGE » : une panne n'est pas un verdict
        print(f"session_hygiene: erreur d'execution {exc!r}", file=sys.stderr)
        sys.exit(2)
