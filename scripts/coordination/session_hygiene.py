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
import re
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path

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


def repo_root() -> Path:
    root = git("rev-parse", "--show-toplevel")
    if not root:
        print("session_hygiene: pas un depot git", file=sys.stderr)
        sys.exit(2)
    return Path(root)


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
        touched = git("diff", "--name-only", f"origin/main...{branch}", cwd=root).splitlines()
        if touched:
            delivers = git("diff", "--stat", "origin/main", branch, "--", *touched, cwd=root)
        else:
            delivers = ""

        has_upstream = bool(git("rev-parse", "--abbrev-ref", "@{u}", cwd=root))
        if not has_upstream:
            unpushed = "jamais poussee"
        else:
            unpushed = git("log", "--oneline", "@{u}..HEAD", cwd=root)

        level = RED if (not delivers and not unpushed) else AMBER
        why = (
            "son contenu est deja integralement sur origin/main (diff trois-points vide) "
            "et rien n'attend d'etre pousse : l'arbre est parke sans raison"
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
                {"branch": branch, "behind": behind_n, "unpushed": bool(unpushed)},
            )
        )
    return checks


def check_main_hostage(root: Path) -> list[Check]:
    """``main`` detenu par un worktree secondaire = ``git checkout main`` echoue en silence."""
    raw = git("worktree", "list", "--porcelain", cwd=root)
    holder = None
    current_path = None
    for line in raw.splitlines():
        if line.startswith("worktree "):
            current_path = line[len("worktree ") :].strip()
        elif line.strip() in ("branch refs/heads/main", "branch refs/heads/master"):
            if current_path and Path(current_path).resolve() != root.resolve():
                holder = current_path

    count = len([ln for ln in raw.splitlines() if ln.startswith("worktree ")])
    checks = []
    if holder:
        checks.append(
            Check(
                "main-otage",
                RED,
                f"'main' est detenu par le worktree {holder} — un `git checkout main` "
                f"dans l'arbre principal ECHOUE, et son message se perd dans le bruit",
                f"verifier qu'il est propre, puis: git worktree remove {holder}",
                {"holder": holder},
            )
        )
    else:
        checks.append(Check("main-otage", GREEN, "aucun worktree ne detient main"))

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


# Items que ce script ne PEUT pas mesurer (ils vivent cote MCP). On les rappelle nommement
# plutot que de laisser croire qu'un vert ici vaut hygiene complete.
MANUAL_REMINDERS = [
    ("inbox", 'roosync_messages(action:"inbox", status:"unread")'),
    ("dashboards", 'roosync_dashboard(action:"read", type:"workspace", section:"all") — LES DEUX'),
    ("memoires", "MEMORY.md + coordinator-handover.md : remplacer ce qui est consomme"),
    ("ledgers", "scripts/coordination/debt_ledger.py — etat des ledgers partages"),
]


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--json", action="store_true", help="sortie structuree")
    ap.add_argument("--quiet", action="store_true", help="n'afficher que RED et AMBER")
    args = ap.parse_args()

    root = repo_root()
    git("fetch", "origin", "--quiet", cwd=root)

    checks: list[Check] = []
    checks += check_branch(root)
    checks += check_main_hostage(root)
    checks += check_organs(root)
    checks += check_untracked_secrets(root)
    checks += check_stash(root)

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
    sys.exit(main())
