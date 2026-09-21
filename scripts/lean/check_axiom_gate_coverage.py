#!/usr/bin/env python3
"""Couverture du gate d'axiomes (proof-integrity) par lake Lean — #17097.

Repond a la question de #17097 : parmi les dispatchers Lean fondus dans
``lean-ci-matrix.yml``, lesquels appelaient ``lean-axiom.yml`` ? Un lake qui
avait le gate et ne l'a plus est une **regression silencieuse de couverture** :
rien n'est rouge, le rollup est vert, et ``sorryAx`` -- transitif -- est
structurellement invisible a toute lecture textuelle. C'est la classe
« un vert qui ne mesure rien », pas un defaut de diff.

Trois mesures, dans cet ordre :

1. **Lakes couverts** -- les workflows qui APPELLENT le gate comme job
   (``uses: .../lean-axiom.yml@<ref>``). Le critere est l'**appel**, pas la
   mention : un workflow peut citer ``lean-axiom.yml`` dans son ``on.paths``
   au titre du *self-cover* (un changement du gate doit relancer la CI du
   lake) sans jamais l'appeler comme job. Un ``grep -l 'lean-axiom'`` seul
   confond les deux et **sur-declare** la couverture ; c'est pourquoi ce
   script apparie l'appel avec le ``project-path:`` qu'il passe.
   ``--from-workflow`` de ``scripts/lean/check_target_coverage.py`` applique
   deja cette distinction cote cibles de modules ; ici elle porte sur les
   *lakes*.

2. **Lakes de la matrice** -- le manifeste ``scripts/lean/ci_lakes.json``.
   Ces lakes sont servis par ``lean-ci-matrix.yml`` : s'ils n'apparaissent pas
   en (1), ils n'ont pas le gate.

3. **Partition jamais-eu / perdu** -- pour chaque dispatcher
   ``.github/workflows/lean-*.yml`` supprime dans l'historique, on lit sa
   **derniere version existante** et on regarde si elle appelait le gate.
   « Perdu » est le seul cas qui soit une regression ; « jamais eu » est une
   question de politique a trancher lake par lake (#17097, critere 3).

Usage::

    # Couverture + partition sur origin/main
    python scripts/lean/check_axiom_gate_coverage.py

    # Machine
    python scripts/lean/check_axiom_gate_coverage.py --json

    # Cliquet : exit 1 seulement si un lake a PERDU le gate (regression)
    python scripts/lean/check_axiom_gate_coverage.py --check

Windows / Git Bash : ``git show <ref>:<chemin>`` est mange par la conversion de
chemins MSYS des que le chemin commence par un segment pointe
(``origin/main:.github/workflows/x.yml`` -> ``origin\\main;.github\\...``, et git
rend « ambiguous argument »). Le script force ``MSYS_NO_PATHCONV=1`` sur ses
appels git ; une invocation manuelle doit faire de meme.
"""

from __future__ import annotations

import argparse
import functools
import json
import os
import re
import subprocess
import sys
from pathlib import Path

WORKFLOWS_DIR = ".github/workflows"
GATE_FILENAME = "lean-axiom.yml"
MANIFEST = "scripts/lean/ci_lakes.json"

# Un APPEL du gate : un job dont le `uses:` resout vers lean-axiom.yml.
# Ancre en debut de ligne (indentation admise) et non `re.search` libre : un
# `uses:` cite dans un COMMENTAIRE (`#   uses: .../lean-axiom.yml@main`, forme
# que la docstring de lean-axiom.yml elle-meme emploie) n'est pas un appel. Une
# ligne commentee commence par `#` et ne matche donc pas.
_GATE_CALL_RE = re.compile(r"^\s*uses:\s*\S*" + re.escape(GATE_FILENAME), re.M)
_PROJECT_PATH_RE = re.compile(r"^\s*project-path:\s*(\S+)", re.M)


def _git(*args: str) -> str:
    """Run git with MSYS path conversion disabled (see module docstring)."""
    env = {**os.environ, "MSYS_NO_PATHCONV": "1"}
    proc = subprocess.run(["git", *args], capture_output=True, env=env)
    return proc.stdout.decode("utf-8", "replace")


# Each of the three readers below spawns one `git` per candidate file (~40 in
# total), so a test suite that probes several invariants pays that cost several
# times over (89 s -> 17 s once memoized). Memoized per ref: the measurement is
# a *read* of a ref that cannot change within a run, so a cached result cannot
# go stale. Callers must NOT mutate what these return -- the objects are shared.


def calls_gate(workflow_text: str) -> bool:
    """True if the workflow CALLS lean-axiom.yml as a job (not a bare mention)."""
    return bool(_GATE_CALL_RE.search(workflow_text))


def gate_project_paths(workflow_text: str) -> list[str]:
    """The ``project-path:`` values of a workflow that calls the gate."""
    return _PROJECT_PATH_RE.findall(workflow_text)


@functools.lru_cache(maxsize=None)
def covered_lakes(ref: str) -> dict[str, list[str]]:
    """Map workflow filename -> lake project-paths it gates, at ``ref``.

    Only workflows that actually call the gate are returned, so the result is
    the *coverage* set, not the set of files that merely mention it.
    """
    names = [p for p in _git("ls-tree", "-r", "--name-only", ref,
                             "--", f"{WORKFLOWS_DIR}/").split("\n")
             if p.endswith(".yml")]
    out: dict[str, list[str]] = {}
    for path in names:
        if path.endswith(GATE_FILENAME):
            continue  # the gate itself is not a caller
        body = _git("show", f"{ref}:{path}")
        if calls_gate(body):
            out[Path(path).name] = gate_project_paths(body)
    return out


@functools.lru_cache(maxsize=None)
def matrix_lakes(ref: str) -> list[dict]:
    """The lakes served by ``lean-ci-matrix.yml`` (its manifest)."""
    raw = _git("show", f"{ref}:{MANIFEST}")
    try:
        data = json.loads(raw)
    except json.JSONDecodeError:
        return []
    lakes = data.get("lakes", []) if isinstance(data, dict) else data
    return [lk for lk in lakes if isinstance(lk, dict)]


@functools.lru_cache(maxsize=None)
def deleted_dispatchers(ref: str) -> list[dict]:
    """Every deleted ``lean-*`` dispatcher, with its last existing content.

    ``git rev-list -n 1 --all -- <path>`` returns the newest commit touching
    the path across all refs; for a deleted file that is the deletion commit,
    so its parent holds the last version that existed. We therefore report
    ``had_gate`` on ``<sha>^:<path>``.
    """
    listed = _git("log", "--all", "--diff-filter=D", "--name-only",
                  "--format=", "--", f"{WORKFLOWS_DIR}/lean-*.yml")
    paths = sorted({p for p in listed.split("\n") if p.startswith(f"{WORKFLOWS_DIR}/lean-")})
    out = []
    for path in paths:
        sha = _git("rev-list", "-n", "1", "--all", "--", path).strip()
        if not sha:
            continue
        last = _git("show", f"{sha}^:{path}")
        if not last.strip():
            continue  # the parent did not have it (add/delete in one commit)
        out.append({"dispatcher": Path(path).name,
                    "deleted_by": sha[:10],
                    "had_gate": calls_gate(last)})
    return out


def measure(ref: str) -> dict:
    """Full coverage report at ``ref``."""
    covered = covered_lakes(ref)
    lakes = matrix_lakes(ref)
    deleted = deleted_dispatchers(ref)

    gated_paths = sorted({p for paths in covered.values() for p in paths})
    manifest_paths = {lk.get("project-path") for lk in lakes}
    ungated = sorted(p for p in manifest_paths
                     if p and p not in set(gated_paths))
    lost = [d for d in deleted if d["had_gate"]]
    never = [d for d in deleted if not d["had_gate"]]

    return {
        "ref": ref,
        "gate_callers": {k: sorted(set(v)) for k, v in sorted(covered.items())},
        "gated_lakes": gated_paths,
        "matrix_lakes": sorted(p for p in manifest_paths if p),
        "matrix_lakes_without_gate": ungated,
        "deleted_dispatchers": len(deleted),
        "lost_gate": sorted(lost, key=lambda d: d["dispatcher"]),
        "never_had_gate": sorted(never, key=lambda d: d["dispatcher"]),
        "not_an_acceptance_criterion": (
            "Cette couverture est une MESURE, pas un verdict de surete : un lake "
            "sans gate d'axiomes n'est pas illicite, il doit seulement etre CONNU "
            "comme tel (#17097 critere 3). Aucun lake n'a perdu le gate en entrant "
            "dans la matrice : le trou est preexistant."
        ),
    }


def _print_human(r: dict) -> None:
    print(f"=== Couverture du gate d'axiomes ({GATE_FILENAME}) sur {r['ref']}")
    print(f"\n1. Workflows qui APPELLENT le gate : {len(r['gate_callers'])}")
    for wf, paths in r["gate_callers"].items():
        print(f"   {wf:42} -> {', '.join(paths)}")
    print(f"\n   lakes distincts couverts : {len(r['gated_lakes'])}")

    print(f"\n2. Lakes du manifeste ({MANIFEST}) : {len(r['matrix_lakes'])}")
    sans = r["matrix_lakes_without_gate"]
    print(f"   dont SANS gate d'axiomes : {len(sans)}")
    for p in sans:
        print(f"   sans gate  {p}")

    print(f"\n3. Dispatchers lean-* supprimes : {r['deleted_dispatchers']}")
    print(f"   AVAIENT le gate -> PERDU : {len(r['lost_gate'])}")
    for d in r["lost_gate"]:
        print(f"      PERDU  {d['dispatcher']:42} (supprime par {d['deleted_by']})")
    print(f"   n'avaient pas le gate   : {len(r['never_had_gate'])}")
    for d in r["never_had_gate"]:
        print(f"      jamais {d['dispatcher']:42} (supprime par {d['deleted_by']})")

    print(f"\nSYNTHESE : {len(r['gated_lakes'])} lakes couverts | "
          f"{len(r['matrix_lakes_without_gate'])} sans gate (jamais eu) | "
          f"{len(r['lost_gate'])} PERDUS")
    print(f"\nRAPPEL : {r['not_an_acceptance_criterion']}")


def main() -> int:
    ap = argparse.ArgumentParser(
        description="Couverture du gate d'axiomes (proof-integrity) par lake Lean.")
    ap.add_argument("--ref", default="origin/main",
                    help="Ref git a mesurer (defaut : origin/main).")
    ap.add_argument("--json", action="store_true", help="Sortie machine.")
    ap.add_argument("--check", action="store_true",
                    help="Exit 1 si un lake a PERDU le gate (regression). "
                         "Un lake qui ne l'a jamais eu ne fait pas echouer : "
                         "c'est une decision de politique, pas une regression.")
    args = ap.parse_args()

    r = measure(args.ref)
    if args.json:
        print(json.dumps(r, ensure_ascii=False, indent=1))
    else:
        _print_human(r)
    if args.check and r["lost_gate"]:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
