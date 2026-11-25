#!/usr/bin/env python3
"""Heritage d'execution entre carnets jumeaux : l'artefact copie, detecte.

Ce que fait cet outil
---------------------
Pour chaque famille de carnets jumeaux (paire Python/C# du registre
`twin_pairs.d`, triplet Python/C#/Rust du registre `rust_conformance.d`), il
extrait de chaque carnet les blocs de **metadonnee d'execution** non vides
(`metadata.execution` + `metadata.papermill`, cellule par cellule) et compare
les **ensembles** de blocs.

Une execution reelle ne peut pas reproduire les horodatages `iopub.execute_input`
d'une autre passe a la microseconde : deux carnets d'une meme famille qui
portent un bloc **identique** ne peuvent pas avoir ete executes separement.
L'un a ete **copie** de l'autre, et ses sorties ne sont pas les siennes.

La comparaison est une intersection d'ensembles, pas une comparaison
positionnelle : les carnets d'une famille n'ont pas toujours la meme structure
de cellules (le jumeau C# peut avoir ete reecrit avec moins de cellules que le
jumeau Python).

Mesure d'origine (issue #27992, PR #27872) : le carnet Rust
`Dynamics-05-Agents-Bornes-Rust.ipynb` portait **26** blocs d'execution
identiques a ceux de son jumeau Python, et ses 11 cellules de code avaient les
sorties du jumeau Python au caractere pres. La comparaison annoncee
« jumeau Python / jumeau Rust : 0 divergence » comparait donc une copie avec
sa source.

Sorties
-------
* ``0`` — aucun heritage trouve (ou mode ``--census`` : releve termine) ;
* ``1`` — au moins un heritage trouve (bloquant en mode ``--gate``) ;
* ``2`` — incident : registre ou carnet illisible (jamais un vert muet).

Usage
-----
    python scripts/notebook_tools/check_twin_execution_heritage.py --census
    python scripts/notebook_tools/check_twin_execution_heritage.py --diff origin/main...HEAD
    python scripts/notebook_tools/check_twin_execution_heritage.py --diff origin/main...HEAD --gate --json
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path
from typing import Any, Iterable

import yaml

REPO_ROOT = Path(__file__).resolve().parents[2]

# Les deux registres de familles : un triplet Rust declare python/csharp/rust,
# une paire du registre de parite declare python/csharp.
REGISTRIES: tuple[tuple[str, tuple[str, ...]], ...] = (
    ("scripts/notebook_tools/rust_conformance.d", ("python", "csharp", "rust")),
    ("scripts/notebook_tools/twin_pairs.d", ("python", "csharp")),
)


class Incident(Exception):
    """Le corpus n'a pas pu etre lu : pas de verdict possible."""


def _git(repo: Path, *args: str) -> str:
    proc = subprocess.run(
        ["git", "-C", str(repo), *args],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
    )
    if proc.returncode != 0:
        raise Incident(f"git {' '.join(args)} : {proc.stderr.strip()}")
    return proc.stdout


def _read_notebook(repo: Path, rel_path: str) -> dict[str, Any] | None:
    path = repo / rel_path
    if not path.is_file():
        return None
    try:
        with path.open(encoding="utf-8") as handle:
            return json.load(handle)
    except Exception as exc:  # noqa: BLE001 — un carnet illisible est un incident
        raise Incident(f"{rel_path} illisible : {exc}") from exc


def execution_blocks(notebook: dict[str, Any]) -> list[str]:
    """Les blocs de metadata d'execution **non vides** du carnet, cellule par cellule.

    Une cellule sans aucune metadata d'execution ne porte pas d'information :
    elle est exclue, sinon deux carnets jamais executes se ressembleraient.
    """
    blocks: list[str] = []
    for cell in notebook.get("cells", []):
        meta = cell.get("metadata", {}) or {}
        execution = meta.get("execution", {}) or {}
        papermill = meta.get("papermill", {}) or {}
        if not execution and not papermill:
            continue
        blocks.append(json.dumps(
            {"execution": execution, "papermill": papermill},
            sort_keys=True, ensure_ascii=False,
        ))
    return blocks


def outputs_text(cell: dict[str, Any]) -> str:
    parts: list[str] = []
    for output in cell.get("outputs", []) or []:
        kind = output.get("output_type")
        if kind == "stream":
            parts.append("".join(output.get("text", []) or []))
        elif kind == "execute_result":
            parts.append(str((output.get("data", {}) or {}).get("text/plain", "")))
    return "".join(parts)


def _entries(repo: Path, registry_rel: str) -> list[tuple[str, dict[str, Any]]]:
    registry = repo / registry_rel
    if not registry.is_dir():
        return []
    found: list[tuple[str, dict[str, Any]]] = []
    for yaml_path in sorted(registry.glob("*.yaml")):
        if yaml_path.name.startswith("_"):
            continue
        try:
            with yaml_path.open(encoding="utf-8") as handle:
                data = yaml.safe_load(handle)
        except Exception as exc:  # noqa: BLE001
            raise Incident(f"{yaml_path} illisible : {exc}") from exc
        if isinstance(data, list):
            entries = data
        elif isinstance(data, dict):
            entries = [data]
        else:
            entries = []
        for entry in entries:
            if isinstance(entry, dict):
                found.append((yaml_path.name, entry))
    return found


def families(repo: Path) -> list[dict[str, Any]]:
    """Toutes les familles declarees, avec leurs membres presents sur disque."""
    result: list[dict[str, Any]] = []
    for registry_rel, keys in REGISTRIES:
        for name, entry in _entries(repo, registry_rel):
            members: dict[str, str] = {}
            for key in keys:
                rel = entry.get(key)
                if isinstance(rel, str) and rel.endswith(".ipynb"):
                    members[key] = rel
            if len(members) >= 2:
                result.append({
                    "famille": name,
                    "registre": registry_rel,
                    "membres": members,
                })
    return result


def _changed_paths(repo: Path, base: str, head: str) -> set[str]:
    diff = _git(repo, "diff", "--name-only", f"{base}...{head}")
    return {line.strip() for line in diff.splitlines() if line.strip()}


def touched_families(repo: Path, base: str, head: str) -> list[dict[str, Any]]:
    """Les familles qu'une PR touche : un registre change, ou un membre change."""
    changed = _changed_paths(repo, base, head)
    touched: list[dict[str, Any]] = []
    for family in families(repo):
        members = set(family["membres"].values())
        registry_file = f"{family['registre']}/{family['famille']}"
        if members & changed or registry_file in changed:
            touched.append(family)
    return touched


def examine(repo: Path, family: dict[str, Any]) -> list[dict[str, Any]]:
    """Les heritages d'execution detectes dans une famille."""
    findings: list[dict[str, Any]] = []
    loaded: dict[str, dict[str, Any]] = {}
    for key, rel in family["membres"].items():
        notebook = _read_notebook(repo, rel)
        if notebook is not None:
            loaded[key] = notebook
    names = sorted(loaded)
    block_sets = {key: set(execution_blocks(loaded[key])) for key in names}
    for index, key_a in enumerate(names):
        for key_b in names[index + 1:]:
            shared = block_sets[key_a] & block_sets[key_b]
            if not shared:
                continue
            cells_b = loaded[key_b].get("cells", []) or []
            inherited = 0
            same_outputs = 0
            for cell in cells_b:
                meta = cell.get("metadata", {}) or {}
                execution = meta.get("execution", {}) or {}
                papermill = meta.get("papermill", {}) or {}
                if not execution and not papermill:
                    continue
                block = json.dumps(
                    {"execution": execution, "papermill": papermill},
                    sort_keys=True, ensure_ascii=False,
                )
                if block not in shared:
                    continue
                inherited += 1
                for other in loaded[key_a].get("cells", []) or []:
                    meta_o = other.get("metadata", {}) or {}
                    execution_o = meta_o.get("execution", {}) or {}
                    papermill_o = meta_o.get("papermill", {}) or {}
                    if not execution_o and not papermill_o:
                        continue
                    block_o = json.dumps(
                        {"execution": execution_o, "papermill": papermill_o},
                        sort_keys=True, ensure_ascii=False,
                    )
                    if block_o == block and outputs_text(cell) == outputs_text(other):
                        same_outputs += 1
                        break
            findings.append({
                "famille": family["famille"],
                "registre": family["registre"],
                "source": key_a,
                "cible": key_b,
                "source_notebook": family["membres"][key_a],
                "cible_notebook": family["membres"][key_b],
                "blocs_partages": len(shared),
                "cellules_heritees": inherited,
                "cellules_memes_sorties": same_outputs,
            })
    return findings


def render(findings: Iterable[dict[str, Any]]) -> None:
    for finding in findings:
        print(
            "HERITAGE -- {famille} : le carnet {cible} ({cible_notebook}) porte "
            "{cellules_heritees} bloc(s) de metadata d'execution identiques a ceux de "
            "{source} ({source_notebook}) ; {cellules_memes_sorties} cellule(s) ont les "
            "MEMES sorties. Re-executer le carnet sous son noyau : la copie n'est pas "
            "une execution.".format(**finding)
        )


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0] if __doc__ else "")
    parser.add_argument("--repo-root", default=str(REPO_ROOT))
    parser.add_argument("--census", action="store_true", help="releve toutes les familles")
    parser.add_argument("--diff", default=None, metavar="BASE...HEAD")
    parser.add_argument("--gate", action="store_true", help="code de sortie bloquant")
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)

    repo = Path(args.repo_root).resolve()
    try:
        if args.diff:
            base, _, head = args.diff.partition("...")
            if not base or not head:
                raise Incident(f"--diff mal forme : {args.diff}")
            scope = touched_families(repo, base, head)
        else:
            scope = families(repo)
        findings: list[dict[str, Any]] = []
        for family in scope:
            findings.extend(examine(repo, family))
    except Incident as exc:
        payload = {"statut": "incident", "message": str(exc)}
        if args.json:
            print(json.dumps(payload, ensure_ascii=False, indent=2))
        else:
            print(f"INCIDENT -- {exc}")
        return 2

    payload = {
        "statut": "trouve" if findings else "propre",
        "familles_examinees": len(scope),
        "heritages": findings,
    }
    if args.json:
        print(json.dumps(payload, ensure_ascii=False, indent=2))
    else:
        if not findings:
            print(f"OK -- {len(scope)} famille(s) examinee(s), aucun heritage d'execution")
        else:
            render(findings)
            print(f"{len(findings)} heritage(s) detecte(s) sur {len(scope)} famille(s)")
    if findings and args.gate:
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
