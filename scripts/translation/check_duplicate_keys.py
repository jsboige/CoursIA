#!/usr/bin/env python3
"""Signale les cles (notebook, cell_id) dupliquees dans les CSV translations.

Contexte (#21489) : 237 cles dupliquees mesurees sur 2 CSV (ml-datascience
168, planners 69, dont 53 a occurrences divergentes). La resync T1
(`extract_cells_to_csv.py --update`) indexe par (notebook, cell_id) et ne
rafraichit que la PREMIERE occurrence : les suivantes conservent un pivot et
une traduction d'une autre version de la cellule. Le doublon est invisible
pour check_translation_sync.py -- chaque ligne prise isolement est valide ;
il ne se revele que par la divergence interne du CSV. Cet organe le rend
visible : exit 1, fichier + cle + nombre d'occurrences.

Cable dans la garde existante des traductions :
- verdict DUPLICATE_KEY emis par check_translation_sync.py (scan principal) ;
- entree fast_lane_registry.py (bloquante sur les PR touchant translations/).

Usage :
    python scripts/translation/check_duplicate_keys.py            # tout le corpus
    python scripts/translation/check_duplicate_keys.py a.csv b.csv
    python scripts/translation/check_duplicate_keys.py --self-test
"""

from __future__ import annotations

import argparse
import csv
import io
import json
import sys
import tempfile
from collections import Counter
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
DEFAULT_GLOB = "translations/**/*.csv"


def scan_csv(paths: list[Path]) -> list[dict]:
    """Retourne une entree par cle dupliquee : csv, notebook, cell_id, occurrences."""
    findings: list[dict] = []
    for path in paths:
        with io.open(path, encoding="utf-8", newline="") as handle:
            rows = list(csv.DictReader(handle))
        counts = Counter(
            (row.get("notebook", ""), row.get("cell_id", ""))
            for row in rows
            if row.get("notebook") and row.get("cell_id")
        )
        for (nb, cid), n in sorted(counts.items()):
            if n > 1:
                findings.append(
                    {
                        "csv": str(path),
                        "notebook": nb,
                        "cell_id": cid,
                        "occurrences": n,
                    }
                )
    return findings


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument(
        "paths",
        nargs="*",
        type=Path,
        help=f"CSV a scanner (defaut : {DEFAULT_GLOB} depuis la racine du depot)",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="sortie JSON machine-lisible (verdict identique)",
    )
    parser.add_argument(
        "--self-test",
        action="store_true",
        help="controle positif sur CSV synthetiques (aucune ecriture hors tmp)",
    )
    args = parser.parse_args(argv)

    if args.self_test:
        return _self_test()

    if args.paths:
        paths = args.paths
    else:
        paths = sorted(REPO_ROOT.glob(DEFAULT_GLOB))
    if not paths:
        print(f"INFO : aucun CSV sous {DEFAULT_GLOB}", file=sys.stderr)
        return 0

    findings = scan_csv(paths)
    if args.json:
        print(json.dumps({"csvs": len(paths), "duplicate_keys": len(findings), "findings": findings}))
    else:
        for f in findings:
            print(f"{f['csv']}: {f['notebook']} cell_id={f['cell_id']} -- {f['occurrences']} occurrences")
        summary = (
            f"DOUBLONS: {len(findings)} cles dupliquees sur {len(paths)} CSV"
            if findings
            else f"OK: 0 cle dupliquee sur {len(paths)} CSV"
        )
        print(summary, file=sys.stderr if findings else sys.stdout)
    return 1 if findings else 0


def _self_test() -> int:
    """Controle positif : un CSV avec doublon doit etre detecte, un propre doit passer."""
    with tempfile.TemporaryDirectory() as tmp:
        dirty = Path(tmp) / "dirty.csv"
        clean = Path(tmp) / "clean.csv"
        header = "notebook,cell_id,src_hash,text_fr\n"
        dirty.write_text(
            header
            + "nb.ipynb,c1,aaa,un\n"
            + "nb.ipynb,c1,bbb,deux\n"
            + "nb.ipynb,c2,ccc,trois\n",
            encoding="utf-8",
        )
        clean.write_text(header + "nb.ipynb,c1,aaa,un\nnb.ipynb,c2,ccc,trois\n", encoding="utf-8")

        findings = scan_csv([dirty, clean])
        assert len(findings) == 1, f"attendu 1 finding, eu {findings}"
        assert findings[0]["cell_id"] == "c1" and findings[0]["occurrences"] == 2, findings
        assert scan_csv([clean]) == [], "le CSV propre ne doit rien signaler"
    print("OK: self-test check_duplicate_keys (controle positif + negatif)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
