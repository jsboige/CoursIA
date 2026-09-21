#!/usr/bin/env python
"""Census de provenance d'une serie de notebooks : quel interpreteur a produit les outputs committes ?

Le champ `metadata.language_info.version` d'un notebook enregistre l'interpreteur de sa **derniere
execution**. C'est exactement la variable que compare `check_kernel_drift.py`, et c'est le seul temoin
lisible dans le depot de *qui* a produit quoi : sur une serie re-executee par des lanes aux envs
differents, ce champ se disperse et aucun env unique ne peut plus reproduire l'ensemble des outputs.

Sert donc a **etablir ou refuter** qu'une serie a UN env canonique avant de declarer un drift
« accidentel » ou de pinner un artefact d'env (cf #17185) : si les versions sont dispersees, toute
re-execution produira du drift contre une partie du corpus, par construction.

Usage:
    python scripts/notebook_tools/notebook_env_census.py <repertoire-ou-glob> [--json]

Sortie: table version x kernelspec, total, et comptage de l'empreinte NumPy 2 (voir la reserve
ci-dessous). Sort toujours en 0 : c'est un instrument de mesure, pas un garde.

Reserve sur l'empreinte NumPy 2 -- instrument UNILATERAL. Le repr NumPy 2 des scalaires
(`np.float64(0.1)` au lieu de `0.1`) est cherche **dans les outputs uniquement** : la *presence*
prouve NumPy 2, l'*absence* ne prouve RIEN (un notebook qui n'imprime aucun repr de scalaire n'en
porte pas, quelle que soit sa version de NumPy). Ne jamais lire une absence comme « NumPy 1 ».
"""

from __future__ import annotations

import argparse
import collections
import glob
import json
import pathlib
import re
import sys

_NUMPY2_SCALAR = re.compile(r"np\.(?:float|int|bool|complex)\d*\(")


def _output_text(cell: dict) -> str:
    """Texte des SORTIES d'une cellule -- jamais la source.

    Le code contient des identifiants comme `np.float64(`, qui disent ce que le notebook *appelle*,
    pas sous quel env il a tourne. Compter dans la source fabrique un faux signal (mesure: 75
    occurrences attribuees a tort a des notebooks qui n'en portent aucune en sortie).
    """
    chunks: list[str] = []
    for out in cell.get("outputs") or []:
        chunks.append("".join(out.get("text") or []))
        chunks.append("".join((out.get("data") or {}).get("text/plain") or []))
        chunks.append("".join(out.get("traceback") or []))
    return "\n".join(chunks)


def census(paths: list[pathlib.Path]) -> dict:
    versions: collections.Counter = collections.Counter()
    kernels: collections.Counter = collections.Counter()
    pairs: collections.Counter = collections.Counter()
    numpy2_nbs: collections.Counter = collections.Counter()
    no_version: list[str] = []
    for nb in paths:
        doc = json.loads(nb.read_text(encoding="utf-8"))
        meta = doc.get("metadata") or {}
        version = (meta.get("language_info") or {}).get("version")
        kernel = (meta.get("kernelspec") or {}).get("name")
        versions[str(version)] += 1
        kernels[str(kernel)] += 1
        pairs[f"{kernel} | {version}"] += 1
        if version is None:
            no_version.append(nb.name)
        hits = sum(len(_NUMPY2_SCALAR.findall(_output_text(c))) for c in doc.get("cells") or [])
        if hits:
            numpy2_nbs[str(version)] += 1
    return {
        "notebooks": len(paths),
        "versions": dict(versions.most_common()),
        "kernels": dict(kernels.most_common()),
        "pairs": dict(pairs.most_common()),
        "numpy2_marker_notebooks": dict(numpy2_nbs.most_common()),
        "no_version": no_version,
    }


def _expand(target: str) -> list[pathlib.Path]:
    """Resout `target` (repertoire, fichier, ou motif) en liste de notebooks.

    On passe par `glob.glob` (stdlib) et non `pathlib.Path().glob` : ce dernier leve
    `NotImplementedError: Non-relative patterns are unsupported` des que le motif est
    **absolu** -- precisement la forme qu'un lecteur de doc tape naturellement.
    """
    p = pathlib.Path(target)
    if p.is_dir():
        return sorted(p.glob("*.ipynb"))
    if any(c in target for c in "*?["):
        return sorted(pathlib.Path(g) for g in glob.glob(target, recursive=True))
    return [p]


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description="Census de provenance d'une serie de notebooks.")
    ap.add_argument("target", help="repertoire, fichier, ou glob des notebooks")
    ap.add_argument("--json", action="store_true", help="sortie JSON au lieu de la table")
    args = ap.parse_args(argv)

    paths = _expand(args.target)
    if not paths:
        print(f"aucun notebook pour {args.target!r}", file=sys.stderr)
        return 0

    data = census(paths)
    if args.json:
        print(json.dumps(data, ensure_ascii=False, indent=2))
        return 0

    print(f"notebooks : {data['notebooks']}")
    print(f"\n== language_info.version (interpreteur des outputs committes) ==")
    for v, n in data["versions"].items():
        marker = f"  [{data['numpy2_marker_notebooks'].get(v, 0)} avec empreinte NumPy 2]" \
            if data["numpy2_marker_notebooks"].get(v) else ""
        print(f"  {v:12} {n:>5}{marker}")
    print(f"\n== kernelspec stocke ==")
    for k, n in data["kernels"].items():
        print(f"  {k:24} {n:>5}")
    print(f"\n== paires (kernelspec | version) ==")
    for p, n in data["pairs"].items():
        print(f"  {p:40} {n:>5}")
    if data["no_version"]:
        print(f"\nsans language_info.version : {len(data['no_version'])} {data['no_version'][:4]}")
    print(
        "\nReserve : l'empreinte NumPy 2 est UNILATERALE -- sa presence prouve NumPy 2, son absence"
        "\nne prouve rien (aucun controle positif). Ne pas lire une absence comme « NumPy 1 »."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
