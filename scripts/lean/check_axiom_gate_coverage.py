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
   script apparie l'appel avec le ``project-path:`` qu'il passe -- et cette
   paire est **scopee au job**, pas au fichier. La distinction n'est pas
   theorique : ``lean-knot.yml`` passe un ``project-path:`` a ``lean-build.yml``
   (job ``ci``) **et** un a ``lean-axiom.yml`` (job ``proof-integrity``). Une
   lecture fichier-entier collecte les deux et credite le gate d'un lake qu'il
   n'a jamais vu ; elle ne mesurait juste que parce que les deux jobs
   declaraient le **meme** lake. Mesure du 2026-09-21 sur ``origin/main`` :
   **11 des 12** appelants sur-declaraient ainsi.
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
_JOBS_KEY_RE = re.compile(r"^jobs:\s*(?:#.*)?$")
_JOB_KEY_RE = re.compile(r"^([A-Za-z0-9_.-]+):")


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


def iter_jobs(workflow_text: str):
    """Yield ``(job_name, job_body)`` for every job of the ``jobs:`` mapping.

    Indentation-based rather than PyYAML-based: the same reader must serve
    *historical* revisions (``git show <sha>^:<path>``) exactly as it serves the
    working tree, and it must not add a dependency to a CI helper.
    """
    in_jobs = False
    job_indent: int | None = None
    name: str | None = None
    buf: list[str] = []
    for line in workflow_text.splitlines():
        if not in_jobs:
            if _JOBS_KEY_RE.match(line):
                in_jobs = True
            continue
        if line.strip() and not line.lstrip().startswith("#"):
            indent = len(line) - len(line.lstrip())
            if indent == 0:
                break  # a new top-level key closes the jobs mapping
            if job_indent is None:
                job_indent = indent
            if indent == job_indent:
                match = _JOB_KEY_RE.match(line.strip())
                if match:
                    if name is not None:
                        yield name, "\n".join(buf)
                    name, buf = match.group(1), []
                    continue
        if name is not None:
            buf.append(line)
    if name is not None:
        yield name, "\n".join(buf)


def gate_calls(workflow_text: str) -> list[tuple[str, list[str]]]:
    """``(job_name, project-paths)`` for every job that CALLS the gate.

    Single source of truth: ``calls_gate`` and ``gate_project_paths`` are both
    derived from this scan, so the call-vs-mention predicate and the pairing
    cannot drift apart.
    """
    out = []
    for job_name, body in iter_jobs(workflow_text):
        if _GATE_CALL_RE.search(body):
            out.append((job_name, _PROJECT_PATH_RE.findall(body)))
    return out


def calls_gate(workflow_text: str) -> bool:
    """True if the workflow CALLS lean-axiom.yml as a job (not a bare mention)."""
    return bool(gate_calls(workflow_text))


def gate_project_paths(workflow_text: str) -> list[str]:
    """The ``project-path:`` values passed by the job(s) that call the gate.

    Scoped to the calling **job**, never to the file. A file-wide scan credits
    the gate with a lake passed to a *different* reusable workflow: in
    ``lean-knot.yml`` the ``ci`` job hands ``project-path:`` to
    ``lean-build.yml``, and only ``proof-integrity`` hands one to
    ``lean-axiom.yml``. The file-wide form measured correctly on
    ``origin/main`` (2026-09-21) only by accident -- 11 of the 12 callers
    passed the same lake to both jobs, so the surplus was a duplicate rather
    than a wrong answer. The first lake whose build job and gate job diverge
    would have been credited to the gate silently.
    """
    return [p for _, paths in gate_calls(workflow_text) for p in paths]


@functools.lru_cache(maxsize=None)
def _workflow_bodies(ref: str) -> dict[str, str]:
    """Text of every ``.github/workflows/*.yml`` at ``ref`` (memoized per ref).

    Memoized *with the bodies in memory* so the two readers below (coverage and
    the file-wide counterfactual) pay the ~40 ``git show`` calls once between
    them, not once each.
    """
    names = [p for p in _git("ls-tree", "-r", "--name-only", ref,
                             "--", f"{WORKFLOWS_DIR}/").split("\n")
             if p.endswith(".yml")]
    return {Path(p).name: _git("show", f"{ref}:{p}") for p in names}


@functools.lru_cache(maxsize=None)
def covered_lakes_by_job(ref: str) -> dict[str, dict[str, list[str]]]:
    """Map workflow filename -> ``{job: project-paths gated}``, at ``ref``.

    Only workflows that actually call the gate are returned, so the result is
    the *coverage* set, not the set of files that merely mention it. The job
    dimension is kept (rather than flattened immediately) because it is what
    makes the pairing auditable in the report.
    """
    out: dict[str, dict[str, list[str]]] = {}
    for name, body in _workflow_bodies(ref).items():
        if name.endswith(GATE_FILENAME):
            continue  # the gate itself is not a caller
        calls = gate_calls(body)
        if calls:
            out[name] = {job: paths for job, paths in calls}
    return out


@functools.lru_cache(maxsize=None)
def filewide_project_paths(ref: str) -> dict[str, list[str]]:
    """Counterfactual: what a file-wide ``project-path:`` scan would credit.

    Kept in the report as a **measure of the defect** -- ``filewide_only_paths``
    is non-empty exactly when the file-wide form over-declares a lake. Without
    this number the fix would be unfalsifiable: a scoped scan that agrees with
    the file-wide one looks identical to a scoped scan that is never exercised.
    """
    bodies = _workflow_bodies(ref)
    return {name: _PROJECT_PATH_RE.findall(bodies[name])
            for name in covered_lakes_by_job(ref)}


@functools.lru_cache(maxsize=None)
def covered_lakes(ref: str) -> dict[str, list[str]]:
    """Map workflow filename -> lake project-paths it gates, at ``ref``."""
    return {wf: [p for paths in jobs.values() for p in paths]
            for wf, jobs in covered_lakes_by_job(ref).items()}


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
                    "had_gate": calls_gate(last),
                    "gated_paths": gate_project_paths(last)})
    return out


def classify_deleted(deleted: list[dict], gated_now: set[str]) -> dict:
    """Partition deleted dispatchers into lost / relocated / never.

    "Perdu" means lost COVERAGE, not lost FILE: a dispatcher that had the
    gate and whose every former project-path is gated by a live caller
    today moved its coverage rather than dropping it. Fail-closed on the
    unreadable cases: a dispatcher that called the gate without passing a
    project-path cannot prove its coverage moved, so it stays "lost".
    """
    lost, relocated, never = [], [], []
    for d in deleted:
        if not d["had_gate"]:
            never.append(d)
        elif d["gated_paths"] and set(d["gated_paths"]) <= gated_now:
            relocated.append(d)
        else:
            lost.append(d)
    return {"lost": lost, "relocated": relocated, "never": never}


def measure(ref: str) -> dict:
    """Full coverage report at ``ref``."""
    covered = covered_lakes(ref)
    by_job = covered_lakes_by_job(ref)
    lakes = matrix_lakes(ref)
    deleted = deleted_dispatchers(ref)

    gated_paths = sorted({p for paths in covered.values() for p in paths})
    manifest_paths = {lk.get("project-path") for lk in lakes}
    ungated = sorted(p for p in manifest_paths
                     if p and p not in set(gated_paths))
    parts = classify_deleted(deleted, set(gated_paths))
    lost, relocated = parts["lost"], parts["relocated"]
    never = parts["never"]

    # What the file-wide scan would have credited *beyond* the job-scoped one:
    # the measure of the defect the scoping closes. Empty is the good news, not
    # the norm -- 11 of the 12 callers over-declared on origin/main (2026-09-21).
    filewide_only = sorted(
        {p for paths in filewide_project_paths(ref).values() for p in paths}
        - set(gated_paths))

    return {
        "ref": ref,
        "gate_callers": {k: sorted(set(v)) for k, v in sorted(covered.items())},
        "gate_calls_by_job": {wf: {job: sorted(paths) for job, paths in jobs.items()}
                              for wf, jobs in sorted(by_job.items())},
        "filewide_only_paths": filewide_only,
        "gated_lakes": gated_paths,
        "matrix_lakes": sorted(p for p in manifest_paths if p),
        "matrix_lakes_without_gate": ungated,
        "deleted_dispatchers": len(deleted),
        "lost_gate": sorted(lost, key=lambda d: d["dispatcher"]),
        "gate_relocated": sorted(relocated, key=lambda d: d["dispatcher"]),
        "never_had_gate": sorted(never, key=lambda d: d["dispatcher"]),
        "not_an_acceptance_criterion": (
            "Cette couverture est une MESURE, pas un verdict de surete : un lake "
            "sans gate d'axiomes n'est pas illicite, il doit seulement etre CONNU "
            "comme tel (#17097 critere 3). La perte ne se declare que si aucun "
            "appel vivant ne reprend les project-paths de l'ancien dispatcher : "
            "deplacer le gate n'est pas le perdre."
        ),
    }


def _print_human(r: dict) -> None:
    print(f"=== Couverture du gate d'axiomes ({GATE_FILENAME}) sur {r['ref']}")
    print(f"\n1. Workflows qui APPELLENT le gate : {len(r['gate_callers'])}")
    for wf, jobs in r["gate_calls_by_job"].items():
        detail = " + ".join(f"{job}: {', '.join(paths)}" for job, paths in jobs.items())
        print(f"   {wf:42} -> {detail}")
    print(f"\n   lakes distincts couverts : {len(r['gated_lakes'])}")
    surplus = r["filewide_only_paths"]
    print(f"   (une lecture fichier-entier crediterait en plus : "
          f"{surplus if surplus else 'rien'})")

    print(f"\n2. Lakes du manifeste ({MANIFEST}) : {len(r['matrix_lakes'])}")
    sans = r["matrix_lakes_without_gate"]
    print(f"   dont SANS gate d'axiomes : {len(sans)}")
    for p in sans:
        print(f"   sans gate  {p}")

    print(f"\n3. Dispatchers lean-* supprimes : {r['deleted_dispatchers']}")
    print(f"   AVAIENT le gate -> PERDU : {len(r['lost_gate'])}")
    for d in r["lost_gate"]:
        print(f"      PERDU  {d['dispatcher']:42} (supprime par {d['deleted_by']})")
    print(f"   gate DEPLACE (couverture reprise ailleurs) : {len(r['gate_relocated'])}")
    for d in r["gate_relocated"]:
        print(f"      deplace {d['dispatcher']:42} (supprime par {d['deleted_by']})")
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
