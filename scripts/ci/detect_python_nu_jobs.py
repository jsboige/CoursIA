#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Detecteur de jobs `python` nu sans `actions/setup-python` (issue #17444, Q35).

Contexte
--------
Mandat user Q35 : « tout ce qui est necessaire pour que le CI ne soit plus
source de congestion ». Une partie de la congestion vient des jobs qui
invoquent `python` nu (sans `python3`, sans `actions/setup-python`). Les
runners self-hosted `coursia-linux` ont `python3` mais pas `python` -> exit
127. La classe des 10 jobs identifies dans le body de #17444 comprend des
jobs configures `runs-on: ubuntu-latest` qui **sont neanmoins routes** vers
des runners self-hosted par la configuration du cluster -- d'ou la
definition de la classe : tout job qui invoque `python` nu sans
`actions/setup-python` est **vulnerable** a un routage self-hosted, qu'il
soit declare self-hosted ou non dans son `runs-on`.

L'organe ferme la boucle : tout futur workflow qui reintroduit la classe est
attrape avant merge.

Sortie
------
- exit 0 : aucun defaut (clean)
- exit 1 : un ou plusieurs defauts trouves (defects)
- exit 2 : instrument casse (workflow illisible ou YAML invalide)

Format de sortie
----------------
Texte par defaut (un defaut par ligne, compatible grep) :

  .github/workflows/foo.yml job-name -- steps exposant `python` nu: 3

Option `--json` : un objet JSON `{workflow, job, runner, step_count,
steps_with_python, evidence}` par defaut, et un resume `{ok, defects, broken}`
en queue.

Exemption
---------
Le job `windows-dotnet-tests` du workflow `windows-self-hosted-tests.yml`
est exempté **nommement** : sur Windows `python` est l'executable canonique
(pas `python3`), une substitution casserait le job. L'exemption est
nominale, pas par regle generale -- un futur refactor ne peut pas
l'elargir silencieusement (le test canonique verifie le NOM EXACT).

Usage
-----
    python scripts/ci/detect_python_nu_jobs.py
    python scripts/ci/detect_python_nu_jobs.py --json
    python scripts/ci/detect_python_nu_jobs.py --workflows-dir .github/workflows
    python scripts/ci/detect_python_nu_jobs.py --help
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Any

EXIT_OK = 0
EXIT_DEFECT = 1
EXIT_BROKEN = 2

# Motif "python" isole : pas precede de [\w./-] (evite setup-python, cpython,
# my-python, ./python), pas suivi de [\w.-] (evite python3, python.exe,
# python_version). Sur les runs multi-lignes (run: |) la regex est appliquee
# par ligne pour eviter qu'un commentaire ou un shebang declenche le motif
# (les commentaires sont skippes par le prefixe de ligne).
_PY_BARE = re.compile(r"(?<![\w./-])python(?![\w.-])")

# Exemption nommee (workflow + job). Pas une regle generale, pas un
# match par label runner : un nom de job, un nom de fichier, c'est tout.
EXEMPTED = frozenset(
    {
        (
            "windows-self-hosted-tests.yml",
            "windows-dotnet-tests",
        ),
    }
)


def _is_exempted(workflow_rel: str, job_name: str) -> bool:
    """Match sur le basename du fichier + le nom de job (couvre les deux
    formes : chemin relatif et basename seul, robustesse aux refactors de
    structure de repertoires)."""
    workflow_basename = Path(workflow_rel).name
    for ex_wf, ex_job in EXEMPTED:
        if ex_job == job_name and (
            ex_wf == workflow_rel or ex_wf == workflow_basename
        ):
            return True
    return False

# Step `uses:` qualifie comme setup-python (couvre toutes versions de
# Microsoft, et les forks exposes).
SETUP_PYTHON_USES = re.compile(r"^actions/setup-python(@\S+)?$")


@dataclass
class Defect:
    workflow: str  # relative path
    job: str
    runner: list[str] = field(default_factory=list)
    step_count: int = 0
    steps_with_python: list[str] = field(default_factory=list)
    evidence: str = ""

    def to_text(self) -> str:
        return (
            f"{self.workflow} {self.job} -- "
            f"steps exposant `python` nu: {len(self.steps_with_python)}"
        )


def _runs_on_is_self_hosted(runs_on: Any) -> bool:
    """Un job est self-hosted si `runs-on` contient le label `self-hosted`.

    Rejette les expressions dynamiques (DYNAMIC_RUNS_ON), qui ne peuvent
    pas etre prouvees statiquement -- l'equivalent de l'inviolabilite
    documentee dans check_self_hosted_runner_policy.py.
    """
    if isinstance(runs_on, str):
        # `runs-on: self-hosted` ou `runs-on: [self-hosted, ...]` raccourci
        if runs_on.strip().startswith("["):
            # Cas degrade : la string contient '[self-hosted, ...]'
            return "self-hosted" in runs_on
        return runs_on.strip() == "self-hosted" or "self-hosted" in runs_on
    if isinstance(runs_on, list):
        return any(
            isinstance(label, str) and label.strip() == "self-hosted"
            for label in runs_on
        )
    # Expression dynamique (objet, template, etc.) : on ne prouve rien.
    return False


def _step_has_setup_python(step: dict[str, Any]) -> bool:
    if not isinstance(step, dict):
        return False
    uses = step.get("uses")
    if not isinstance(uses, str):
        return False
    return bool(SETUP_PYTHON_USES.match(uses.strip()))


def _step_runs_python_bare(step: dict[str, Any]) -> tuple[bool, str]:
    """Retourne (True, nom du step) si le step invoque `python` nu.

    Definit un step "invoque python nu" comme :
    - un step avec `run:` qui contient `python` comme mot isole (regex
      _PY_BARE), sur une ligne NON commentaire, et
    - dont la longueur indique un appel reel (>= 2 chars apres le mot,
      typiquement un nom de script ou une option).

    Un shebang `#!/usr/bin/env python` est sur la premiere ligne d'un
    `run:` multi-ligne : il n'est pas un appel, c'est un interpretateur
    declaratif. Le test de longueur >= 2 apres le mot tient ce cas
    (apres le shebang il n'y a rien d'exploitable sur la meme ligne).
    """
    if not isinstance(step, dict):
        return False, ""
    run = step.get("run")
    if not isinstance(run, str):
        return False, ""
    name = step.get("name") or ""
    for line in run.splitlines():
        stripped = line.lstrip()
        if not stripped or stripped.startswith("#"):
            continue
        m = _PY_BARE.search(stripped)
        if m is None:
            continue
        # Au moins 2 chars apres `python` (separateur + nom de script ou
        # option). Evite les matches sur des labels seuls (`python:` en
        # YAML est deja hors de `run:`, mais on securise).
        tail = stripped[m.end():]
        if len(tail.strip()) < 2:
            continue
        return True, name if isinstance(name, str) else ""
    return False, ""


def _iter_workflow_files(workflows_dir: Path) -> list[Path]:
    return sorted(
        list(workflows_dir.glob("*.yml")) + list(workflows_dir.glob("*.yaml"))
    )


def _check_one_workflow(
    path: Path, repo_root: Path
) -> tuple[list[Defect], list[str]]:
    """Retourne (defects, broken_reasons) pour un seul fichier workflow."""
    defects: list[Defect] = []
    broken: list[str] = []
    try:
        import yaml
    except ImportError:
        return [], ["pyyaml not installed"]
    try:
        text = path.read_text(encoding="utf-8")
        data = yaml.safe_load(text)
    except yaml.YAMLError as exc:
        broken.append(f"{path.name}: YAML invalide ({exc})")
        return [], broken
    except OSError as exc:
        broken.append(f"{path.name}: lecture impossible ({exc})")
        return [], broken
    if not isinstance(data, dict):
        return [], []
    jobs = data.get("jobs")
    if not isinstance(jobs, dict):
        return [], []
    workflow_rel = str(path.relative_to(repo_root)).replace("\\", "/")
    for job_name, job_def in jobs.items():
        if not isinstance(job_def, dict):
            continue
        if _is_exempted(workflow_rel, job_name):
            continue
        runs_on = job_def.get("runs-on")
        steps = job_def.get("steps")
        if not isinstance(steps, list):
            continue
        has_setup = any(_step_has_setup_python(s) for s in steps)
        if has_setup:
            continue
        steps_with_py: list[str] = []
        for s in steps:
            ok, name = _step_runs_python_bare(s)
            if ok:
                steps_with_py.append(name or "<unnamed>")
        if not steps_with_py:
            continue
        runner_list = (
            runs_on
            if isinstance(runs_on, list)
            else [runs_on] if isinstance(runs_on, str) else []
        )
        runner_norm = [
            r.strip() for r in runner_list if isinstance(r, str)
        ]
        defects.append(
            Defect(
                workflow=workflow_rel,
                job=job_name,
                runner=runner_norm,
                step_count=len(steps),
                steps_with_python=steps_with_py,
                evidence=(
                    "python nu detecte dans "
                    f"{len(steps_with_py)}/{len(steps)} step(s) ; "
                    "actions/setup-python absent"
                ),
            )
        )
    return defects, broken


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Detecteur de jobs `python` nu sur runner self-hosted "
            "(#17444)."
        )
    )
    parser.add_argument(
        "--workflows-dir",
        default=".github/workflows",
        help="Repertoire des workflows (defaut: .github/workflows).",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Sortie JSON (un objet par defaut, resume en queue).",
    )
    parser.add_argument(
        "--repo-root",
        default=".",
        help="Racine du depot pour les chemins relatifs (defaut: cwd).",
    )
    parser.add_argument(
        "--mode",
        choices=("strict", "advisory"),
        default="strict",
        help=(
            "Mode de sortie : 'strict' (defaut) exit 1 sur defaut, "
            "'advisory' exit 0 toujours, signale les defauts en JSON "
            "ou texte. Le CI utilise 'advisory' pour ne pas bloquer "
            "main pendant la migration ; les tests utilisent 'strict' "
            "pour verifier la detection."
        ),
    )
    parser.add_argument(
        "--baseline",
        type=int,
        default=None,
        help=(
            "Nombre de defauts attendus (advisory uniquement). Si le "
            "compte actuel depasse la baseline, exit 1 ; sinon exit 0. "
            "Permet de transformer l'organe en ratchet sur la classe."
        ),
    )
    args = parser.parse_args(argv)
    repo_root = Path(args.repo_root).resolve()
    wf_dir = (repo_root / args.workflows_dir).resolve()
    if not wf_dir.is_dir():
        print(
            f"#17444 detecteur : repertoire introuvable: {wf_dir}",
            file=sys.stderr,
        )
        return EXIT_BROKEN
    files = _iter_workflow_files(wf_dir)
    if not files:
        print(
            f"#17444 detecteur : aucun workflow dans {wf_dir}",
            file=sys.stderr,
        )
        return EXIT_BROKEN
    all_defects: list[Defect] = []
    all_broken: list[str] = []
    for f in files:
        defects, broken = _check_one_workflow(f, repo_root)
        all_defects.extend(defects)
        all_broken.extend(broken)
    if all_broken:
        for b in all_broken:
            print(f"BROKEN: {b}", file=sys.stderr)
    if args.json:
        out = {
            "ok": not all_defects and not all_broken,
            "defects": [asdict(d) for d in all_defects],
            "broken": all_broken,
            "mode": args.mode,
            "baseline": args.baseline,
        }
        print(json.dumps(out, indent=2, ensure_ascii=False))
    else:
        if all_defects:
            for d in all_defects:
                print(d.to_text())
            print(
                f"#17444: {len(all_defects)} defaut(s) detecte(s)",
                file=sys.stderr,
            )
        else:
            print("#17444: aucun defaut detecte")
    if all_broken and not all_defects:
        return EXIT_BROKEN
    # Mode advisory : exit 0 sur main (la migration est en cours), exit 1
    # seulement si la baseline est depassee (regression). Mode strict :
    # exit 1 sur le moindre defaut (utilise par les tests).
    if args.mode == "advisory":
        if args.baseline is not None and len(all_defects) > args.baseline:
            print(
                f"#17444: REGRESSION {len(all_defects)} > baseline {args.baseline}",
                file=sys.stderr,
            )
            return EXIT_DEFECT
        return EXIT_OK
    return EXIT_DEFECT if all_defects else EXIT_OK


if __name__ == "__main__":
    sys.exit(main())
