"""Associe chaque diapositive Slidev capturee a son original PPTX.

Le port Slidev et le PPTX d'origine n'ont pas la meme numerotation (02 :
88 diapositives rendues contre 93 dans le PPTX ; 06 : 124 contre 128 ;
S3 : 105 contre 64). L'association se fait donc par **titre**, jamais par un
decalage suppose :

  - 02 : titres issus de `extracted/inventory.json` (numero = numero PPTX) ;
  - 06 et S3 : titres issus du PDF de reference (une page = une diapositive).

Sortie : JSON `{slidev_no: {pptx, method}}` + la liste des non-associes.

Usage :

    python slides/_tools/map_pptx.py <deck> <manifest-rendu.json> <sortie.json> \
           [--overrides <overrides.json>] [--slides-root <racine slides>]

`<deck>` vaut `02`, `06` ou `S3`. Le deck `S8` n'a pas de reference PPTX : il
n'a pas d'original auquel comparer, et l'assemblage le traite comme tel.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
import unicodedata
import warnings
from pathlib import Path
from typing import Any

warnings.filterwarnings("ignore")
try:  # PyMuPDF >= 1.24 expose `pymupdf` ; `fitz` reste l'alias historique
    import pymupdf as fitz  # noqa: E402
except ImportError:  # pragma: no cover — anciennes versions
    import fitz  # noqa: E402

DECK_DIR: dict[str, str] = {
    "02": "02-resolution-problemes",
    "06": "06-apprentissage",
    "S3": "S3-acculturation",
}


def norm(s: str) -> str:
    s = unicodedata.normalize("NFKD", s or "")
    s = "".join(c for c in s if not unicodedata.combining(c))
    s = s.lower().replace("’", "'").replace("–", "-")
    s = re.sub(r"[^a-z0-9]+", " ", s)
    return re.sub(r"\s+", " ", s).strip()


def titles_from_inventory(deck_dir: Path) -> list[tuple[int, str, str]]:
    inv = json.loads((deck_dir / "extracted" / "inventory.json").read_text(encoding="utf-8"))
    return [(s["number"], norm(s.get("title") or ""), s.get("title") or "") for s in inv["slides"]]


def titles_from_pdf(deck_dir: Path) -> tuple[list[tuple[int, str, str]], dict[int, str]]:
    pdf = deck_dir / "pptx-reference" / "slides.pdf"
    doc = fitz.open(pdf)
    out: list[tuple[int, str, str]] = []
    full: dict[int, str] = {}
    for i in range(doc.page_count):
        lines = [norm(line) for line in doc[i].get_text().split("\n") if norm(line)]
        out.append((i + 1, lines[0] if lines else "", lines[0] if lines else ""))
        full[i + 1] = " ".join(lines)
    return out, full


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Associe les diapositives capturees a leur original PPTX, par titre."
    )
    parser.add_argument("deck", choices=sorted(DECK_DIR), help="deck a associer")
    parser.add_argument("manifest", type=Path, help="manifeste de rendu (render_deck.py)")
    parser.add_argument("sortie", type=Path, help="fichier JSON de sortie")
    parser.add_argument(
        "--overrides",
        type=Path,
        default=None,
        help="associations forcees (titre reecrit dans l'original)",
    )
    parser.add_argument(
        "--slides-root",
        type=Path,
        default=Path(__file__).resolve().parents[1],
        help="racine du dossier slides/ (defaut : le depot courant)",
    )
    args = parser.parse_args()

    manifest = json.loads(args.manifest.read_text(encoding="utf-8"))
    deck_dir = args.slides_root / DECK_DIR[args.deck]

    full: dict[int, str] = {}
    if args.deck == "02":
        norm_cand = titles_from_inventory(deck_dir)
    else:
        norm_cand, full = titles_from_pdf(deck_dir)

    used: set[int] = set()
    mapping: dict[str, Any] = {}
    unmatched: list[dict[str, Any]] = []

    overrides: dict[str, Any] = {}
    if args.overrides and args.overrides.exists():
        overrides = json.loads(args.overrides.read_text(encoding="utf-8"))

    for entry in manifest["matched"]:
        sv = str(entry["no"])
        if sv in overrides:
            mapping[sv] = overrides[sv]
            used.add(overrides[sv]["pptx"])
            continue
        h1 = entry.get("h1") or ""
        h = norm(h1)
        hit: int | None = None
        method: str | None = None
        for n, t, _raw in norm_cand:
            if n in used:
                continue
            if t and t == h:
                hit, method = n, "exact"
                break
        if hit is None:
            for n, t, _raw in norm_cand:
                if n in used:
                    continue
                if h and h in t:
                    hit, method = n, "prefix"
                    break
        if hit is None and args.deck != "02":
            for n, blob in full.items():
                if n in used:
                    continue
                if h and h in blob:
                    hit, method = n, "in-page"
                    break
        if hit is None:
            unmatched.append({"slidev": entry["no"], "h1": h1})
        else:
            used.add(hit)
            mapping[sv] = {"pptx": hit, "method": method}

    out = {"deck": args.deck, "mapping": mapping, "unmatched": unmatched}
    args.sortie.parent.mkdir(parents=True, exist_ok=True)
    args.sortie.write_text(
        json.dumps(out, ensure_ascii=False, indent=2) + "\n", encoding="utf-8", newline="\n"
    )
    print(f"[{args.deck}] associees {len(mapping)} / {len(manifest['matched'])}")
    for u in unmatched:
        print(f"   NON ASSOCIE slidev {u['slidev']} : {u['h1']!r}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
