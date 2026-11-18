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
portant un marqueur de claim (≈ ~ ≥ ≤ > < %) sont considérés. Deux
bornes supplémentaires (#25616) : une claim explicitement approximative
(~, ≈, « environ ») peut être l'arrondi d'un output exact, et une
citation entre guillemets n'est pas une mesure locale. Le verdict
est un rapport JSON + rc=1, jamais un blocage seul.

Sortie : rc=0 propre, rc=1 au moins un finding, rc=2 erreur d'usage.
"""

from __future__ import annotations

import argparse
import json
import math
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

# #25616 : marqueur d'approximation. Il ouvre aussi le statut de claim
# (« environ 0,5 » n'a ni ~ ni %) et autorise la tolerance d'arrondi.
APPROX_MARKER_BEFORE_RE = re.compile(r"(?i)(?:[~≈]\s*|environ\s+)$")
APPROX_MARKER_AFTER_RE = re.compile(r"^\s*[~≈]")

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

# #25616 : une citation (« ... », "..." ou “...”) rapporte la valeur d'un
# tiers, ce n'est pas une mesure que le carnet doit produire localement.
QUOTE_RE = re.compile(r"«[^»]*»|\"[^\"]*\"|“[^”]*”")

# Constantes statistiques de convention (p, alpha, |r|, confiance) : la
# mesure FP du 29/09 (#18354) montre qu'elles dominent le bruit -- ce ne
# sont pas des mesures, ce sont des seuils disciplinaires (07_Code_
# Interpreter c.32 : 9 findings sur une seule cellule).
STAT_CONSTANT_CONTEXT_RE = re.compile(
    r"(?i)(\bp[- ]?val|\balpha\b|α\b|corr[eé]lation|\bconfiance\b|\bp\s*[<>=≈])"
)
ORDER_OF_MAGNITUDE_RE = re.compile(r"(?i)(de l'ordre|ordre de grandeur)")
CHAINED_BAND_RE = re.compile(r"\d\s*(?:<|≤|>|≥)\s*[^<>\n]{1,14}?\s*(?:<|≤|>|≥)\s*\d")

# #24289 famille 3 (dérivée montrée) : la prose écrit la formule qui
# produit la valeur (« 4 683² ≈ 21,9 millions »), et l'opérande est
# imprimée par les sorties -- la claim est auditable par le lecteur.
DERIVED_SQUARE_RE = re.compile(
    r"(?P<base>\d{1,3}(?:[   ]\d{3})+|\d+(?:[.,]\d+)?)"
    r"\s*(?:²|\^2|\*\*2)\s*(?:≈|=|→)\s*"
    r"(?P<val>\d+(?:[.,]\d+)?)"
)


def _unaccent(s: str) -> str:
    return "".join(
        c for c in unicodedata.normalize("NFD", s) if unicodedata.category(c) != "Mn"
    )


def _normalize_num(tok: str) -> set[str]:
    """Variantes acceptables d'un nombre côté outputs (12 vs 12,0 vs 12.0).

    Une valeur non finie (suite d'environ 309 chiffres ou plus selon ses
    premiers chiffres, float() = inf, ou nan) ne donne que le jeton brut :
    int(inf) lève OverflowError.
    """
    raw = tok.replace(",", ".")
    out = {tok, raw}
    try:
        f = float(raw)
    except ValueError:
        return out
    if not math.isfinite(f):
        return out
    out.add(str(int(f)) if f == int(f) else str(f))
    out.add(f"{f:g}")
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


def _claim_numbers(src_stripped: str) -> list[tuple[str, str, bool]]:
    """(nombre, ligne, approximatif) pour chaque claim, hors gardes.

    Les gardes durée/dimension sont PAR SPAN (un « 6x6 » ailleurs dans la
    ligne ne doit pas masquer un « ≈ 12 » légitime à signaler — mesuré sur
    App-4b c.15, la garde par ligne avalait le finding canonique).
    """
    findings: list[tuple[str, str, bool]] = []
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
            approx = bool(
                APPROX_MARKER_BEFORE_RE.search(before[-12:])
                or APPROX_MARKER_AFTER_RE.match(after[:4])
            )
            if not marked and not approx:
                continue
            findings.append((tok, line.strip(), approx))
    return findings


def _ungroup(token: str) -> str:
    """« 4 683 » -> « 4683 » : compare un opérande de prose groupée au
    jeton plat qu'imprime une sortie."""
    return token.replace(" ", "").replace(" ", "").replace("\xa0", "").replace(",", ".")


def _rounding_supported(tok: str, out_nums: set[str]) -> bool:
    """#25616 : une claim approximative peut être l'arrondi d'un output.

    « ~0,83 » est couvert par un output « 0.8325 » : arrondi au même
    nombre de décimales, l'output dit bien ce que la prose affirme. La
    tolérance est limitée à une demi-unité du dernier chiffre affiché —
    « ~0,84 » face à 0.8325 reste un finding, et le contrôle négatif
    canonique « ≈ 12 » face à 11 n'est pas atteint (écart 1 > 0,5).
    """
    try:
        value = float(tok.replace(",", "."))
    except ValueError:
        return False
    if not math.isfinite(value):
        return False
    decimals = len(tok.split(",")[1]) if "," in tok else (
        len(tok.split(".")[1]) if "." in tok else 0
    )
    tolerance = 0.5 * 10**-decimals + 1e-9
    for out_tok in out_nums:
        try:
            out_value = float(out_tok)
        except ValueError:
            continue
        if math.isfinite(out_value) and abs(out_value - value) <= tolerance:
            return True
    return False


def _derived_or_complement_supported(tok: str, stripped: str, out_nums: set[str]) -> bool:
    """#24289 famille 3 -- deux exemptions mesurées sur GT-20c (carnet sain):

    1. Dérivée montrée : la MÊME cellule écrit « base² ≈ valeur » et la
       base est imprimée par les sorties (« 4 683² ≈ 21,9 millions » avec
       4683 imprimée, c.16). La valeur n'est pas importée d'ailleurs : sa
       dérivation est écrite noir sur blanc.
    2. Complément affiché : un pourcentage dont le complément à 100 est
       porté par la même cellule avec son % ET imprimé par les sorties
       (« 85 % des paires ne raccourcissent pas », c.14, complément
       « 15,0 % » imprimée par la cellule de code 13).
    """
    tok_variants = _normalize_num(tok)
    for m in DERIVED_SQUARE_RE.finditer(stripped):
        if (
            _ungroup(m.group("base")) in out_nums
            and _normalize_num(m.group("val")) & tok_variants
        ):
            return True
    try:
        value = float(tok.replace(",", "."))
    except ValueError:
        return False
    # Une claim de ~400 chiffres donne value = inf : int(inf) leve
    # OverflowError (garde heritee de _normalize_num, meme classe de
    # plantage -- test_huge_digit_claim_in_interpretation_does_not_crash).
    if not math.isfinite(value):
        return False
    # #24289 famille 3, variante ratio (mesuree sur GT-18c c.34, carnet
    # sain) : « 48/120 = 40 % » -- le pourcentage n'est JAMAIS imprime tel
    # quel, mais la paire d'entiers l'est (cellule 33 : « total : 120
    # instances », « humour_reussi : 48 »). Prescrit par l'issue :
    # « resoudre les fractions a/b = x % contre les entiers presents dans
    # la fenetre ». Limite au pourcentages : la claim doit etre portee
    # par CETTE cellule sous la forme « <tok> % ».
    if 0 < value < 100 and re.search(
        r"(?<![A-Za-z0-9.,])" + re.escape(tok) + r"\s*%", stripped
    ):
        decimals = len(tok.split(",")[1]) if "," in tok else 0
        tol = 0.5 * 10**-decimals + 1e-9
        out_ints: set[int] = set()
        for out_tok in out_nums:
            try:
                v = float(out_tok)
            except ValueError:
                continue
            if math.isfinite(v) and v > 0 and v == int(v):
                out_ints.add(int(v))
        for a in out_ints:
            for b in out_ints:
                if b <= a:
                    continue
                if abs(100.0 * a / b - value) <= tol:
                    return True
    complement = round(100.0 - value, 6)
    comp_variants: set[str] = set()
    for rep in (repr(complement), f"{complement:g}", f"{complement:.1f}"):
        comp_variants.add(rep)
    if complement == int(complement):
        comp_variants.add(str(int(complement)))
    if comp_variants & out_nums:
        # le complément doit aussi être porté par CETTE cellule en pourcentage
        for rep in comp_variants:
            for form in (rep.replace(".", ","), rep):
                if re.search(re.escape(form) + r"\s*%", stripped):
                    return True
    return False


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
        stripped = QUOTE_RE.sub(
            " ", MATH_RE.sub(" ", FENCE_RE.sub(" ", LINK_RE.sub(" ", src)))
        )
        for tok, line, approx in _claim_numbers(stripped):
            if _normalize_num(tok) & out_nums:
                continue
            if approx and _rounding_supported(tok, out_nums):
                continue
            if _derived_or_complement_supported(tok, stripped, out_nums):
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
