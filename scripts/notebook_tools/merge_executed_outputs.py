#!/usr/bin/env python3
"""Replace les sorties d'un carnet execute ailleurs dans le carnet de la branche.

Cas d'usage : un carnet QuantBook execute sur QC Cloud (routes B et C de
docs/qc/quantbook-execution-routes.md) revient avec ses sorties, mais le carnet
de la branche porte le texte markdown a jour. L'outil copie, cellule de code par
cellule de code, `outputs` et `execution_count` du carnet execute vers le carnet
de la branche, sans toucher au markdown ni aux metadonnees.

Usage :
  python scripts/notebook_tools/merge_executed_outputs.py <carnet_branche> <carnet_execute>
  python scripts/notebook_tools/merge_executed_outputs.py <carnet_branche> <carnet_execute> --dry-run
  python scripts/notebook_tools/merge_executed_outputs.py --fingerprint <carnet> [<carnet> ...]

Contrat :
  - meme nombre de cellules de code et sources de code identiques, sinon refus (exit 1) ;
  - carnet execute complet : chaque cellule de code a un `execution_count` et aucune
    sortie `error`, sinon refus (exit 2, levable par --allow-incomplete) ;
  - indentation JSON, ordre des cles, fins de ligne et saut de ligne final du
    carnet de la branche conserves ; les sorties texte sont remises en liste de lignes (forme nbformat).

Empreinte (--fingerprint) : sha256 des sources des cellules de code jointes par
un saut de ligne, 16 premiers caracteres hexadecimaux. Elle verifie que le carnet
execute a distance est bien celui de la branche ; le markdown n'y entre pas.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path


class MergeError(Exception):
    """Les deux carnets n'ont pas le meme code : la fusion est refusee."""


def source_text(cell: dict) -> str:
    src = cell.get("source", "")
    return src if isinstance(src, str) else "".join(src)


def code_cells(nb: dict) -> list[dict]:
    return [c for c in nb.get("cells", []) if c.get("cell_type") == "code"]


def fingerprint(nb: dict) -> str:
    joined = "\n".join(source_text(c) for c in code_cells(nb))
    return hashlib.sha256(joined.encode("utf-8")).hexdigest()[:16]


def normalise_output(output: dict) -> dict:
    """Remet `text` et les `data` text/* en liste de lignes, comme nbformat."""
    out = dict(output)
    if isinstance(out.get("text"), str):
        out["text"] = out["text"].splitlines(keepends=True)
    data = out.get("data")
    if isinstance(data, dict):
        out["data"] = {
            mime: value.splitlines(keepends=True)
            if isinstance(value, str) and mime.startswith("text/")
            else value
            for mime, value in data.items()
        }
    return out


def incomplete_cells(executed: dict) -> list[str]:
    """Cellules de code du carnet execute sans execution_count ou en erreur."""
    problems = []
    for i, cell in enumerate(code_cells(executed), 1):
        if cell.get("execution_count") is None:
            problems.append(f"code cell {i}: execution_count is null "
                            "(not executed, or outputs not saved)")
        for out in cell.get("outputs", []):
            if out.get("output_type") == "error":
                problems.append(f"code cell {i}: error output ({out.get('ename', '?')})")
    return problems


def _first_difference(a: str, b: str) -> str:
    la, lb = a.splitlines(), b.splitlines()
    for n, (x, y) in enumerate(zip(la, lb), 1):
        if x != y:
            return f"line {n}: {x[:60]!r} != {y[:60]!r}"
    return f"{len(la)} lines vs {len(lb)} lines"


def merge(target: dict, executed: dict) -> int:
    """Copie outputs et execution_count ; rend le nombre de cellules de code."""
    tc, ec = code_cells(target), code_cells(executed)
    if len(tc) != len(ec):
        raise MergeError(f"{len(tc)} code cells in target, {len(ec)} in executed notebook")
    for i, (t, e) in enumerate(zip(tc, ec), 1):
        st, se = source_text(t), source_text(e)
        if st != se:
            raise MergeError(f"code cell {i}: source differs ({_first_difference(st, se)})")
    for t, e in zip(tc, ec):
        t["outputs"] = [normalise_output(o) for o in e.get("outputs", [])]
        t["execution_count"] = e.get("execution_count")
    return len(tc)


def _layout(raw: str) -> dict:
    """Retrouve la mise en forme JSON du fichier cible pour la reproduire."""
    lines = raw.splitlines()
    indent = 1
    if len(lines) > 1:
        indent = max(1, len(lines[1]) - len(lines[1].lstrip(" ")))
    nb = json.loads(raw)
    ensure_ascii = raw.isascii() and "\\u" in raw
    tail = "\n" if raw.endswith("\n") else ""
    sort_keys = json.dumps(nb, indent=indent, ensure_ascii=ensure_ascii,
                           sort_keys=True) + tail == raw
    return {"indent": indent, "ensure_ascii": ensure_ascii,
            "sort_keys": sort_keys, "tail": tail, "newline": "\n"}


def dump(nb: dict, layout: dict) -> str:
    return json.dumps(nb, indent=layout["indent"], ensure_ascii=layout["ensure_ascii"],
                      sort_keys=layout["sort_keys"]) + layout["tail"]


def load(path: str) -> dict:
    return json.loads(Path(path).read_text(encoding="utf-8"))


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(
        description="Copy outputs and execution_count of an executed notebook into the "
                    "branch notebook (identical code sources required).")
    p.add_argument("paths", nargs="+", help="<branch_notebook> <executed_notebook>, "
                   "or notebooks to fingerprint with --fingerprint")
    p.add_argument("--fingerprint", action="store_true",
                   help="print the code fingerprint of each notebook and exit")
    p.add_argument("--dry-run", action="store_true", help="check and report, write nothing")
    p.add_argument("--allow-incomplete", action="store_true",
                   help="merge even if the executed notebook has null execution_count "
                        "or error outputs")
    args = p.parse_args(argv)

    if args.fingerprint:
        for path in args.paths:
            print(f"{fingerprint(load(path))}  {path}")
        return 0
    if len(args.paths) != 2:
        p.error("expected two paths: <branch_notebook> <executed_notebook>")

    target_path, executed_path = args.paths
    with open(target_path, encoding="utf-8", newline="") as fh:
        raw = fh.read()
    crlf = "\r\n" in raw
    raw = raw.replace("\r\n", "\n")
    layout = _layout(raw)
    if crlf:
        layout["newline"] = "\r\n"
    target = json.loads(raw)
    executed = load(executed_path)

    problems = incomplete_cells(executed)
    if problems and not args.allow_incomplete:
        print("REFUSED: executed notebook is incomplete", file=sys.stderr)
        for line in problems:
            print(f"  {line}", file=sys.stderr)
        return 2
    try:
        n = merge(target, executed)
    except MergeError as exc:
        print(f"REFUSED: {exc}", file=sys.stderr)
        return 1

    n_outputs = sum(len(c["outputs"]) for c in code_cells(target))
    print(f"fingerprint {fingerprint(target)}: {n} code cells, {n_outputs} outputs merged"
          + (" (dry run, nothing written)" if args.dry_run else ""))
    if not args.dry_run:
        with open(target_path, "w", encoding="utf-8", newline=layout["newline"]) as fh:
            fh.write(dump(target, layout))
    return 0


if __name__ == "__main__":
    sys.exit(main())
