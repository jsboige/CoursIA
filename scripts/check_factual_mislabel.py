#!/usr/bin/env python3
"""Organe factual-mislabel (#18354 tranche 2, campagne #17073).

Détecte une cellule markdown qui énonce un compte d'entité CONTREDIT par
le stream text committé de la cellule code qu'elle décrit -- canon :
App-5-Timetabling énonce « 3 salles » et « (3 × 20)^8 » alors que le
stream committé imprime « Salles : 4 » et « (4 x 20)^8 = 1.68e+15 ».

Deux facettes, toutes deux des contradictions (un compte DIFFÉRENT du
stream) -- l'absence pure d'un nombre relève de l'organe stale-claim
(tranche 1) :

1. compte d'unité : « N <unit> » en markdown vs « <Unit> : M » dans le
   stream d'une cellule code adjacente (fenêtre +-2), même unité,
   N != M ;
2. formule-tuple : « (N × K)^P » en markdown vs « (M x K)^P » dans le
   stream, N != M.

Sortie : rc=0 propre, rc=1 au moins un finding, rc=2 erreur d'usage.
Advisory par construction (patron #11435) -- jamais bloquant seul.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
import unicodedata
from pathlib import Path

UNITS = (
    "salles?|cours|cre?neaux?|enseignants?|professeurs?|etudiants?|"
    "agents?|variables?|contraintes?|jours?|rooms?|courses?|slots?|teachers?"
)

MD_COUNT_RE = re.compile(rf"(?i)\b(\d{{1,5}})\s*({UNITS})\b")
STREAM_COUNT_RE = re.compile(rf"(?i)\b({UNITS})\s*[:=]\s*(\d{{1,5}})\b")
MD_TUPLE_RE = re.compile(r"\(\s*(\d{1,5})\s*(?:[x×]|\\times\s*)\s*(\d{1,5})\s*\)\s*\^")
STREAM_TUPLE_RE = re.compile(r"\(\s*(\d{1,5})\s*x\s*(\d{1,5})\s*\)\s*\^")

# Sous-comptes par entite (« Dupont enseigne 2 cours », « chacun 2 cours »,
# « par jour », bornes « au moins/au plus ») : le total du stream ne les
# contredit pas -- mesure sur App-5 (md c.6 : 3 faux « 2 cours » vs
# stream « Cours : 8 »).
SUBCOUNT_CONTEXT_RE = re.compile(
    r"(?i)(enseign\w*|chacun\w*|par\s+\w+|au\s+(?:moins|plus)|maximum|minimum|"
    r"environ|centaines?|dizaines?)"
)

WINDOW = 3


def _unaccent(s: str) -> str:
    return "".join(
        c for c in unicodedata.normalize("NFD", s) if unicodedata.category(c) != "Mn"
    )


def _output_text(cell: dict) -> str:
    parts: list[str] = []
    for o in cell.get("outputs", []):
        t = o.get("text", "")
        parts.append("".join(t) if isinstance(t, list) else (t if isinstance(t, str) else ""))
        data = o.get("data", {}) if isinstance(o.get("data"), dict) else {}
        for key in ("text/plain", "text/html"):
            v = data.get(key, "")
            parts.append("".join(v) if isinstance(v, list) else (v if isinstance(v, str) else ""))
    return "\n".join(parts)


def _nearby_streams(cells: list[dict], idx: int) -> str:
    lo = max(0, idx - WINDOW)
    hi = min(len(cells), idx + WINDOW + 1)
    parts = [
        _output_text(c)
        for c in cells[lo:hi]
        if c["cell_type"] == "code" and _output_text(c).strip()
    ]
    return "\n".join(parts)


def _singular(unit: str) -> str:
    return unit.rstrip("s").lower()


def scan_notebook(path: Path) -> list[dict]:
    try:
        nb = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        return [{"file": str(path), "error": f"unreadable notebook: {exc}"}]
    findings: list[dict] = []
    for idx, cell in enumerate(nb["cells"]):
        if cell["cell_type"] != "markdown":
            continue
        src = _unaccent("".join(cell.get("source", [])))
        stream = _unaccent(_nearby_streams(nb["cells"], idx))
        if not stream.strip():
            continue
        # facette 1 : comptes d'unites contredits
        stream_counts: dict[str, set[int]] = {}
        for m in STREAM_COUNT_RE.finditer(stream):
            stream_counts.setdefault(_singular(m.group(1)), set()).add(int(m.group(2)))
        seen_unit_claims: set[tuple[int, str, str]] = set()
        for m in MD_COUNT_RE.finditer(src):
            n, unit = int(m.group(1)), _singular(m.group(2))
            key = (idx, unit, str(n))
            if key in seen_unit_claims:
                continue
            after = src[m.end(): m.end() + 12]
            before = src[max(0, m.start() - 15): m.start()]
            ctx_before = src[max(0, m.start() - 60): m.start()]
            if SUBCOUNT_CONTEXT_RE.search(ctx_before) or SUBCOUNT_CONTEXT_RE.search(
                src[m.end(): m.end() + 30]
            ):
                continue
            # composé hypotheque (creneaux-salles) ou rapport (creneaux/jour) :
            # l'unite n'y est PAS la meme grandeur que le total du stream
            if after.lstrip().startswith("-") or re.match(r"\s*/\s*\w", after):
                continue
            # operande droite d'un produit « 5 jours x 4 creneaux » : c'est une
            # decomposition du total, pas un compte total contredit
            if re.search(r"[x×]\s*$", before) or re.search(r"\d\s*[x×]\s*$", before):
                continue
            if unit in stream_counts and n not in stream_counts[unit]:
                seen_unit_claims.add(key)
                findings.append(
                    {
                        "file": str(path),
                        "cell_index": idx,
                        "verdict": "FACTUAL_MISLABEL",
                        "kind": "unit-count",
                        "unit": unit,
                        "claimed": str(n),
                        "stream": sorted(stream_counts[unit]),
                        "context": src[max(0, m.start() - 40): m.end() + 30].strip()[:160],
                    }
                )
        # facette 2 : tuples de formule contredits
        stream_tuples = {(int(m.group(1)), int(m.group(2))) for m in STREAM_TUPLE_RE.finditer(stream)}
        for m in MD_TUPLE_RE.finditer(src):
            t = (int(m.group(1)), int(m.group(2)))
            if stream_tuples and t not in stream_tuples and any(
                t[1] == s[1] and t[0] != s[0] for s in stream_tuples
            ):
                findings.append(
                    {
                        "file": str(path),
                        "cell_index": idx,
                        "verdict": "FACTUAL_MISLABEL",
                        "kind": "tuple-formula",
                        "unit": "tuple",
                        "claimed": f"({t[0]} x {t[1]})^",
                        "stream": [f"({a} x {b})^" for a, b in sorted(stream_tuples)],
                        "context": src[max(0, m.start() - 40): m.end() + 30].strip()[:160],
                    }
                )
    return findings


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--json", action="store_true")
    ap.add_argument("notebooks", nargs="+", type=Path)
    args = ap.parse_args(argv)

    findings: list[dict] = []
    for p in args.notebooks:
        findings.extend(scan_notebook(p))

    if args.json:
        print(json.dumps({"anomaly_count": len(findings), "findings": findings}, ensure_ascii=False, indent=1))
    else:
        for f in findings:
            if "error" in f:
                print(f"[ERROR] {f['file']}: {f['error']}")
                continue
            print(
                f"[FACTUAL_MISLABEL] {f['file']} cell={f['cell_index']} "
                f"{f['kind']} unit={f['unit']} claimed={f['claimed']} "
                f"stream={f['stream']} :: {f['context'][:110]}"
            )
        print(f"anomaly_count: {len(findings)}")
    return 1 if findings else 0


if __name__ == "__main__":
    sys.exit(main())
