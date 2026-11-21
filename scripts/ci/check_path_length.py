#!/usr/bin/env python3
"""check_path_length.py - garde cliquet sur la longueur des chemins de fichiers.

Source : issue #27676 (Vibe-Coding/Roo-Code : chemins de 203 caracteres qui
cassent les worktrees Windows, MAX_PATH).

Constat mesure (2026-11-21 sur `origin/main`) : le chemin le plus long du depot
faisait 203 caracteres, et sous Windows `git worktree add` echoue des que le
prefixe du worktree plus le chemin le plus long du depot depasse 260. Sur
`myia-po-2028`, une serie d'executions de fournees est morte sur ce checkout.

Le garde est un **cliquet** : il ne juge que les chemins **ajoutes** (statut
`A`) ou **renommes** (statut `R`, chemin nouveau). Les chemins deja presents
sur la base restent toleres -- sinon le garde rougirait des sa naissance sur la
dette existante, et aucune PR ne pourrait etre verte. C'est ce qui rend le
raccourcissement des livrables 1 progressif : chaque PR rapproche le stock de
la borne, aucune ne peut la repousser.

La mesure porte sur le chemin **relatif a la racine du depot**, en caracteres
(la forme que `git ls-tree` rend). La borne de 160 laisse la marge du prefixe
de worktree Windows : `D:/CoursIA-2-wt/<nom-court>/` + 160 reste sous 260.

Verdict :
  exit 0 = aucun chemin ajoute au-dessus de la borne
  exit 1 = au moins un chemin ajoute au-dessus de la borne (la PR le repare)
  exit 2 = incident d'entree (git illisible, base introuvable) -- le verdict
           est INCONNU, pas un quitus (cf warn_rc du registre de la voie rapide)

Usage :
  python scripts/ci/check_path_length.py --base origin/main --head HEAD
  python scripts/ci/check_path_length.py --base origin/main --head HEAD --json
  python scripts/ci/check_path_length.py --self
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

# Borne par defaut. Mesure : le chemin le plus long du depot au 2026-11-21
# faisait 203 caracteres ; la borne de 160 laisse le prefixe de worktree sous
# la limite Windows de 260 caracteres.
DEFAULT_LIMIT = 160

# Statuts git qui introduisent un chemin NOUVEL dans l'arbre de la tete.
# `A` = ajout, `R` = renommage (le chemin nouveau est juge), `C` = copie.
# `M` et `D` ne changent pas la longueur d'un chemin deja present.
JUDGED_STATUSES = ("A", "R", "C")


def _run_git(args: list[str]) -> subprocess.CompletedProcess:
    return subprocess.run(
        ["git", *args], capture_output=True, text=True, encoding="utf-8",
        errors="replace",
    )


def added_paths(base: str, head: str) -> tuple[list[str], str | None]:
    """Chemins introduits par le diff `base...head` (ajouts + renommages).

    Retourne `(chemins, erreur)`. `erreur` est non None quand le diff n'a pas
    pu etre lu -- le verdict est alors inconnu, jamais un succes.
    """
    proc = _run_git(["diff", "--name-status", "-z", "--find-renames",
                     f"{base}...{head}"])
    if proc.returncode != 0:
        return [], (proc.stderr or "git diff en echec").strip()
    fields = [f for f in proc.stdout.split("\0") if f != ""]
    paths: list[str] = []
    i = 0
    while i < len(fields):
        token = fields[i]
        status = token[0]
        i += 1
        if status in ("R", "C"):
            # format -z : status \0 ancien \0 nouveau
            if i + 1 >= len(fields):
                break
            i += 1  # ancien chemin
            new_path = fields[i]
            i += 1
            if status in JUDGED_STATUSES:
                paths.append(new_path)
            continue
        if i >= len(fields):
            break
        path = fields[i]
        i += 1
        if status in JUDGED_STATUSES:
            paths.append(path)
    return paths, None


def find_overlong(paths: list[str], limit: int) -> list[dict]:
    """Chemins dont la longueur depasse la borne, du plus long au plus court."""
    findings = [
        {"path": p, "length": len(p), "limit": limit}
        for p in paths
        if len(p) > limit
    ]
    findings.sort(key=lambda f: (-f["length"], f["path"]))
    return findings


def self_test() -> int:
    """Cas de controle de l'organe, sans depot ni reseau."""
    cases = [
        (["a/b.md"], 160, []),
        (["a" * 161], 160, [{"path": "a" * 161, "length": 161, "limit": 160}]),
        (["x" * 160], 160, []),
    ]
    for paths, limit, expected in cases:
        got = find_overlong(paths, limit)
        if got != expected:
            sys.stderr.write(
                f"ECHEC : find_overlong({paths!r}, {limit}) -> {got!r}\n")
            return 1
    sys.stdout.write("OK : 3 cas de controle\n")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base", default="",
                        help="base de comparaison (ex. origin/main)")
    parser.add_argument("--head", default="HEAD")
    parser.add_argument("--limit", type=int, default=DEFAULT_LIMIT,
                        help=f"borne de longueur (defaut {DEFAULT_LIMIT})")
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--self", action="store_true",
                        help="cas de controle, sans depot")
    args = parser.parse_args(argv)

    if args.self:
        return self_test()

    if not args.base:
        sys.stderr.write("usage : --base <ref> est obligatoire\n")
        return 2

    paths, error = added_paths(args.base, args.head)
    if error is not None:
        sys.stderr.write(f"INCIDENT : diff illisible ({error})\n")
        return 2

    findings = find_overlong(paths, args.limit)

    if args.json:
        print(json.dumps({
            "base": args.base,
            "head": args.head,
            "limit": args.limit,
            "added_paths": len(paths),
            "overlong": findings,
            "verdict": "FAIL" if findings else "OK",
        }, ensure_ascii=False, indent=2))
        return 1 if findings else 0

    if findings:
        sys.stderr.write(
            f"ECHEC : {len(findings)} chemin(s) ajoute(s) au-dessus de "
            f"{args.limit} caracteres\n")
        for f in findings:
            sys.stderr.write(f"  [{f['length']:>4}] {f['path']}\n")
        sys.stderr.write(
            "Sous Windows, un chemin long casse `git worktree add` "
            "(MAX_PATH). Raccourcissez le chemin, ou declarez pourquoi il est "
            "necessaire.\n")
        return 1

    sys.stdout.write(
        f"OK : {len(paths)} chemin(s) ajoute(s), aucun au-dessus de "
        f"{args.limit} caracteres\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
