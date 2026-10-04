#!/usr/bin/env python3
"""Organe stale-claim (#18354 tranche 1, campagne #17073).

Détecte une cellule markdown d'interprétation qui affirme une valeur
numérique de mesure ABSENTE de tous les outputs committés du notebook --
le cas canonique étant un nombre importé d'un twin ou d'un autre carnet,
jamais produit localement (App-4b : « ≈ 12 » affiché, optimum réel
committé = 11).

Pourquoi ADVISORY : comme #11435 (check_markdown_claims_output.py), la
prose pédagogique cite légitimement des nombres de domaine. On borne
donc le signal : seules les cellules dont l'en-tête annonce une
interprétation/lecture/résultat sont scannées, et seuls les nombres
portant un marqueur de claim (≈ ~ ≥ ≤ > < %) sont considérés. Le verdict
est un rapport JSON + rc=1, jamais un blocage seul.

Sortie : rc=0 propre, rc=1 au moins un finding, rc=2 erreur d'usage.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
import unicodedata
from pathlib import Path

INTERPRETATION_HEADING_RE = re.compile(
    r"(?im)^#{2,4}\s*\**\s*(interpretation|lecture|resultat)\b"
)

NUM_RE = re.compile(r"\d+(?:[.,]\d+)?")

CLAIM_MARKER_BEFORE_RE = re.compile(r"[≈~≥≤><%]\s*$")
CLAIM_MARKER_AFTER_RE = re.compile(r"^\s*[≈~≥≤><%]")

YEAR_RE = re.compile(r"(19|20)\d\d")
DURATION_RE = re.compile(r"(?i)~?\s*\d+(?:[.,]\d+)?\s*(min|ms|s\b|h\b|heure)")
VERSION_RE = re.compile(r"v\d+(?:\.\d+)+", re.IGNORECASE)
TUPLE_RE = re.compile(r"\b\d+\s*[x×]\s*\d+\b")
EXPONENT_RE = re.compile(r"\^\{?\d+")
ISSUE_REF_RE = re.compile(r"#\s*\d+$")
ORDINAL_RE = re.compile(r"^\d+[.)]")

FENCE_RE = re.compile(r"```.*?```|`[^`]*`", re.DOTALL)
LINK_RE = re.compile(r"\[[^\]]*\]\([^)]*\)|https?://\S+")
MATH_RE = re.compile(r"\$[^$]*\$")

# Constantes statistiques de convention (p, alpha, |r|, confiance) : la
# mesure FP du 29/09 (#18354) montre qu'elles dominent le bruit -- ce ne
# sont pas des mesures, ce sont des seuils disciplinaires (07_Code_
# Interpreter c.32 : 9 findings sur une seule cellule).
STAT_CONSTANT_CONTEXT_RE = re.compile(
    r"(?i)(\bp[- ]?val|\balpha\b|α\b|corr[eé]lation|\bconfiance\b|\bp\s*[<>=≈])"
)
ORDER_OF_MAGNITUDE_RE = re.compile(r"(?i)(de l'ordre|ordre de grandeur)")
CHAINED_BAND_RE = re.compile(r"\d\s*(?:<|≤|>|≥)\s*[^<>\n]{1,14}?\s*(?:<|≤|>|≥)\s*\d")


def _unaccent(s: str) -> str:
    return "".join(
        c for c in unicodedata.normalize("NFD", s) if unicodedata.category(c) != "Mn"
    )


def _normalize_num(tok: str) -> set[str]:
    """Variantes acceptables d'un nombre côté outputs (12 vs 12,0 vs 12.0)."""
    raw = tok.replace(",", ".")
    out = {tok, raw}
    try:
        f = float(raw)
        out.add(str(int(f)) if f == int(f) else str(f))
        out.add(f"{f:g}")
    except ValueError:
        pass
    return out


def _output_text(cell: dict) -> str:
    parts: list[str] = []
    for o in cell.get("outputs", []):
        t = o.get("text", "")
        if isinstance(t, list):
            t = "".join(t)
        parts.append(t if isinstance(t, str) else "")
        data = o.get("data", {}) if isinstance(o.get("data"), dict) else {}
        for key in ("text/plain", "text/html"):
            v = data.get(key, "")
            if isinstance(v, list):
                v = "".join(v)
            parts.append(v if isinstance(v, str) else "")
    return "\n".join(parts)


def _notebook_output_numbers(nb: dict) -> set[str]:
    nums: set[str] = set()
    for c in nb["cells"]:
        if c["cell_type"] == "code":
            for tok in NUM_RE.findall(_output_text(c)):
                nums |= _normalize_num(tok)
    return nums


def _claim_numbers(src_stripped: str) -> list[tuple[str, str]]:
    """(nombre, ligne) pour chaque nombre à marqueur de claim, hors gardes.

    Les gardes durée/dimension sont PAR SPAN (un « 6x6 » ailleurs dans la
    ligne ne doit pas masquer un « ≈ 12 » légitime à signaler — mesuré sur
    App-4b c.15, la garde par ligne avalait le finding canonique).
    """
    findings: list[tuple[str, str]] = []
    for line in src_stripped.splitlines():
        norm = _unaccent(line)
        guard_spans: list[tuple[int, int]] = [
            (s.start() - 1, s.end() + 1)
            for s in list(DURATION_RE.finditer(norm)) + list(TUPLE_RE.finditer(norm))
        ]
        for m in NUM_RE.finditer(norm):
            tok = m.group(0)
            s, e = m.span()
            if any(gs <= e and s <= ge for gs, ge in guard_spans):
                continue
            if CHAINED_BAND_RE.search(norm) and s in (
                b.start() for b in CHAINED_BAND_RE.finditer(norm)
            ):
                continue
            if ORDER_OF_MAGNITUDE_RE.search(norm):
                continue
            if STAT_CONSTANT_CONTEXT_RE.search(norm):
                try:
                    is_small_decimal = float(tok.replace(",", ".")) < 1
                except ValueError:
                    is_small_decimal = False
                if is_small_decimal or "%" in norm[max(0, e - 2): e + 3]:
                    continue
            before = norm[: m.start()]
            after = norm[m.end():]
            if VERSION_RE.search(before + tok):
                continue
            if YEAR_RE.fullmatch(tok):
                continue
            if EXPONENT_RE.search(after[:4]):
                continue
            if ORDINAL_RE.match(after.strip() if not before.strip() else "x"):
                continue
            marked = CLAIM_MARKER_BEFORE_RE.search(
                before[-4:]
            ) or CLAIM_MARKER_AFTER_RE.match(after[:4])
            if not marked:
                continue
            findings.append((tok, line.strip()))
    return findings


def scan_notebook(path: Path) -> list[dict]:
    try:
        nb = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        return [{"file": str(path), "error": f"unreadable notebook: {exc}"}]
    out_nums = _notebook_output_numbers(nb)
    findings: list[dict] = []
    for idx, cell in enumerate(nb["cells"]):
        if cell["cell_type"] != "markdown":
            continue
        src = "".join(cell.get("source", []))
        head = src.splitlines()[0] if src.splitlines() else ""
        if not INTERPRETATION_HEADING_RE.match(_unaccent(head)):
            continue
        stripped = MATH_RE.sub(" ", FENCE_RE.sub(" ", LINK_RE.sub(" ", src)))
        for tok, line in _claim_numbers(stripped):
            if _normalize_num(tok) & out_nums:
                continue
            findings.append(
                {
                    "file": str(path),
                    "cell_index": idx,
                    "heading": head.strip()[:90],
                    "verdict": "STALE_CLAIM",
                    "claimed": tok,
                    "context": line[:160],
                    "hint": (
                        "nombre à marqueur de claim absent de TOUS les outputs "
                        "committés du notebook -- probablement importé d'un twin "
                        "ou d'un autre carnet (cf #18354)"
                    ),
                }
            )
    return findings


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--json", action="store_true", help="sortie JSON machine-lisible")
    ap.add_argument("notebooks", nargs="+", type=Path)
    args = ap.parse_args(argv)

    findings: list[dict] = []
    for p in args.notebooks:
        findings.extend(scan_notebook(p))

    if args.json:
        print(json.dumps({"anomaly_count": len(findings), "findings": findings}, ensure_ascii=False, indent=1))
    else:
        for f in findings:
            print(
                f"[STALE_CLAIM] {f['file']} cell={f.get('cell_index')} "
                f"claimed={f['claimed']} :: {f.get('context', f.get('error', ''))[:120]}"
            )
        print(f"anomaly_count: {len(findings)}")
    return 1 if findings else 0


if __name__ == "__main__":
    sys.exit(main())
