"""Analyse du TSV produit par `ocr_trames.ps1` sur les trames d'un film Gource.

Trois mesures, une seule passe :
  1. la courbe date <-> temps (bandeau du haut, y + h/2 < 130 px en 4K) ;
  2. le nombre d'etiquettes de repertoire par trame, bandeau exclu -- c'est le
     controle sur trames intermediaires ;
  3. la duree de vie de quelques noms (nombre de trames, plus longue serie).

Sortie texte sur stdout, a rediriger vers un fichier.

Usage :
    python analyse_etiquettes.py <tsv> [trame ...]

Les trames nommees en argument sont imprimees en detail (y, x, texte).

Deux bornes de lecture, portees par les chiffres eux-memes :
- le bandeau est une horloge *interpolee* entre deux commits, pas l'horodatage
  d'un commit : l'arbre d'une trame se relit sur le dernier commit anterieur ;
- l'OCR de Windows lit mal un nom en fondu ou masque par un autre : les comptes
  sont des ordres de grandeur, pas des enumerations.
"""
from __future__ import annotations

import re
import sys
from collections import Counter
from pathlib import Path

BANNER_Y = 130  # en 3840x2160, le bandeau de date tient dans les 130 premiers pixels

MONTHS = {
    # francais
    "janvier": 1, "fevrier": 2, "février": 2, "mars": 3, "avril": 4, "mai": 5,
    "juin": 6, "juillet": 7, "aout": 8, "août": 8, "septembre": 9,
    "octobre": 10, "novembre": 11, "decembre": 12, "décembre": 12,
    # anglais
    "january": 1, "february": 2, "march": 3, "april": 4, "may": 5, "june": 6,
    "july": 7, "august": 8, "september": 9, "october": 10, "november": 11,
    "december": 12,
}
YEAR_RE = re.compile(r"\b(19|20)\d{2}\b")
NUM_RE = re.compile(r"\b(\d{1,2})\b")

# Noms suivis. La forme cherchee est une expression reguliere appliquee au texte
# OCR brut : `scripts` est compte sur le mot exact, `MyIA.AI.Notebooks` sur le
# fragment `otebo`, seul morceau que l'OCR restitue de facon stable (le nom est
# long, souvent coupe par le fondu ou par un autre noeud).
LIFETIMES = [
    ("scripts (texte exact)", r"^scripts$"),
    ("docs (texte exact)", r"^docs$"),
    ("MyIA.AI.Notebooks (fragment otebo)", r"otebo"),
    ("tests (texte exact)", r"^tests$"),
    ("prover (texte exact)", r"^prover$"),
]


def parse_date(text: str) -> tuple[int, int, int] | None:
    """Rend (annee, mois, jour) si le bandeau porte une date complete."""
    m = YEAR_RE.search(text)
    if not m:
        return None
    year = int(m.group(0))
    low = text.lower()
    month = None
    for name, num in MONTHS.items():
        if name in low:
            month = num
            break
    head = text[: m.start()]
    days = [int(d) for d in NUM_RE.findall(head)]
    day = days[-1] if days else None
    if month is None:
        return (year, 0, 0)
    return (year, month, day or 0)


def longest_run(hit: set[int], first: int, last: int) -> int:
    """Plus longue suite de trames consecutives presentes dans `hit`."""
    best = cur = 0
    for i in range(first, last + 1):
        if i in hit:
            cur += 1
            best = max(best, cur)
        else:
            cur = 0
    return best


def main() -> int:
    if len(sys.argv) < 2:
        print("usage: analyse_etiquettes.py <tsv> [trame ...]", file=sys.stderr)
        return 2
    tsv = Path(sys.argv[1])
    focus = {int(a) for a in sys.argv[2:]}

    banner: dict[int, list[str]] = {}
    labels: dict[int, list[tuple[float, float, str]]] = {}
    for raw in tsv.read_text(encoding="utf-8", errors="replace").splitlines():
        if raw.startswith("#") or not raw.strip():
            continue
        parts = raw.split("\t")
        if len(parts) != 7:
            continue
        _, idx_s, x_s, y_s, _w, h_s, text = parts
        idx, x, y = int(idx_s), float(x_s), float(y_s)
        if y + float(h_s) / 2 < BANNER_Y:
            banner.setdefault(idx, []).append(text)
        else:
            labels.setdefault(idx, []).append((x, y, text))

    frames = sorted(set(banner) | set(labels))
    if not frames:
        print("aucune ligne exploitable", file=sys.stderr)
        return 1
    print(f"# trames lues : {len(frames)}  (de {frames[0]} a {frames[-1]})")
    print(f"# moteur      : {tsv.name}")

    # --- 1. courbe date <-> temps ------------------------------------------
    print("\n## Courbe date <-> temps (bandeau, y < %d px)" % BANNER_Y)
    dated: list[tuple[int, tuple[int, int, int], str]] = []
    unreadable = []
    for idx in frames:
        text = " ".join(banner.get(idx, []))
        d = parse_date(text)
        if d is None or d[1] == 0:
            unreadable.append(idx)
        else:
            dated.append((idx, d, text))
    print(f"dates completes    : {len(dated)}")
    print(f"dates illisibles   : {len(unreadable)} {unreadable[:12]}")

    if dated:
        for year in sorted({d[0] for _, d, _ in dated}):
            hits = [(i, d, t) for i, d, t in dated if d[0] == year]
            print(f"  {year} : trames {hits[0][0]}..{hits[-1][0]} "
                  f"({len(hits)} mesures) premier bandeau : {hits[0][2]}")

        print("\n  transitions :")
        for (i0, d0, _), (i1, d1, t1) in zip(dated, dated[1:]):
            if d1[0] != d0[0]:
                print(f"    {d0[0]} -> {d1[0]} entre la trame {i0} ({d0}) "
                      f"et la trame {i1} ({d1}) : {t1}")

        last_change = dated[0][0]
        for (i0, d0, _), (i1, d1, _) in zip(dated, dated[1:]):
            if d1 != d0:
                last_change = i1
        print(f"\n  derniere variation de date : trame {last_change} ({dated[-1][1]})")
        print(f"  bandeau final             : {dated[-1][2]}")
        print(f"  duree du film             : {frames[-1]} s (derniere trame lue)")

        years = [(i, d[0]) for i, d, _ in dated]
        back = [(a, b) for a, b in zip(years, years[1:]) if b[1] < a[1]]
        print(f"  retours en arriere        : {len(back)} {back[:5]}")

    # --- 2. etiquettes par trame ------------------------------------------
    print("\n## Etiquettes de repertoire par trame (bandeau exclu)")
    counts = {i: len(labels.get(i, [])) for i in frames}
    series = [counts[i] for i in frames]
    total = sum(series)
    med = sorted(series)[len(series) // 2]
    print(f"total lignes   : {total}")
    print(f"moyenne        : {total / len(series):.2f}")
    print(f"mediane        : {med}")
    print(f"maximum        : {max(series)} (trame {max(frames, key=lambda i: counts[i])})")
    print(f"trames sans aucune etiquette : {sum(1 for v in series if v == 0)}")

    top = sorted(frames, key=lambda i: -counts[i])[:12]
    print("\n  douze trames les plus denses :")
    for i in top:
        print(f"    trame {i:4d}  {counts[i]:3d} etiquettes")

    print("\n  profil par tranches de 10 s :")
    for start in range(0, frames[-1] + 1, 10):
        window = [counts[i] for i in range(start, min(start + 10, frames[-1] + 1)) if i in counts]
        if window:
            print(f"    {start:3d}-{start + 9:3d} s  moy {sum(window) / len(window):5.2f}  "
                  f"max {max(window):3d}")

    freq = Counter()
    for i in frames:
        for _x, _y, t in labels.get(i, []):
            freq[t] += 1
    print("\n  quarante textes les plus frequents :")
    for text, n in freq.most_common(40):
        print(f"    {n:4d}  {text}")

    # --- 3. duree de vie des noms -----------------------------------------
    print("\n## Duree de vie des noms (bandeau exclu)")
    print("  %-38s %5s %8s %6s" % ("nom", "trames", "part", "serie"))
    first, last = frames[0], frames[-1]
    for name, pattern in LIFETIMES:
        rx = re.compile(pattern, re.IGNORECASE)
        hit = {i for i in frames if any(rx.search(t) for _x, _y, t in labels.get(i, []))}
        part = 100.0 * len(hit) / len(frames)
        print("  %-38s %5d %7.1f%% %6d"
              % (name, len(hit), part, longest_run(hit, first, last)))

    for i in sorted(focus & set(frames)):
        print(f"\n  trame {i} : {counts[i]} etiquettes")
        for x, y, t in sorted(labels.get(i, []), key=lambda r: (r[1], r[0])):
            print(f"    y={y:6.0f} x={x:6.0f}  {t}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
