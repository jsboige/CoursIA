"""Detection du debordement par le bas des slides exportees en PNG (EPIC #11508, lot L2).

Reinstrumentation de la passe S3-acculturation (issue #11508, section 2) : une
slide deborde quand de l'encre atteint les N dernieres lignes de pixels du PNG
exporte -- le contenu est coupe au rendu, et le defaut est invisible dans le
``.md`` source. Methode : sur chaque PNG du repertoire d'export
(``slidev export --format png``), compter les pixels d'encre (luminance sous le
seuil) dans les ``--rows`` dernieres lignes ; une slide est signalee OVERFLOW si
le ratio encre / largeur mesuree depasse ``--threshold``.

Deux choix mesures, pas devines :

- ``--ignore-right-frac`` (defaut 0.10) retire de la mesure la bande droite de
  la slide, ou le theme rend le numero de page -- sans elle, toute slide
  numerotee serait signalee et l'instrument ne distinguerait plus rien. Le
  numero est de l'encre legitime, pas un debordement.
- l'encre est relative au fond dominant de la slide (mesure sur la ligne du
  haut, tolerance ``BG_TOLERANCE``) : une page de titre sombre n'est pas un
  debordement -- seul ce qui DIFFERE du fond compte, sur fond clair comme
  sur fond sombre.

Ce scan mesure, il ne qualifie pas : une slide signalee se relit a l'oeil sur
le PNG (planches-contact puis pleine taille) avant tout correctif -- le
mandat de l'EPIC exige la verification visuelle, et une lane sans vision ne
prononce pas qu'un rendu est correct (model-delegation).

L'instrument repond de façon bruyante aux entrees qu'il ne sait pas lire :
repertoire absent, vide de PNG, ou PNG illisible sortent en erreur nommee sur
stderr avec un exit non nul -- jamais un tableau vide qui se lirait comme
« aucun debordement ». C'est le mode de panne consigne par la note de methode
de l'EPIC (six instruments faux en une session, dont le resultat etait
systematiquement plus petit et plus propre que la verite).

Usage:
  python scan_slidev_overflow.py <repertoire_png>                # table lisible
  python scan_slidev_overflow.py <repertoire_png> --json         # sortie machine
  python scan_slidev_overflow.py <repertoire_png> --rows 6 --threshold 0.01
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

try:
    from PIL import Image
except ImportError:  # pragma: no cover - environnement sans Pillow
    print("PIL (Pillow) est requis : pip install Pillow", file=sys.stderr)
    sys.exit(2)

BG_TOLERANCE = 12        # un pixel a moins de ceci du fond n'est PAS de l'encre
DEFAULT_ROWS = 6         # les 6 dernieres lignes, comme la passe S3
DEFAULT_THRESHOLD = 0.01 # 1 % de la largeur mesurable en encre -> OVERFLOW
DEFAULT_IGNORE_RIGHT = 0.10  # bande droite retiree (numero de page du theme)


def _natural_key(path: Path):
    """Cle de tri numerique : 1, 2, ... 10, 11 -- pas 1, 10, 11, 2."""
    return [
        int(part) if part.isdigit() else part.lower()
        for part in re.split(r"(\d+)", path.name)
    ]


def _ink_ratio(png: Path, rows: int, ignore_right_frac: float) -> float:
    """Ratio encre / largeur mesurable sur les ``rows`` dernieres lignes du PNG.

    L'encre est RELATIVE au fond dominant de la slide (mesure sur la ligne du
    haut) : sur un deck a pages sombres, le fond sombre n'est pas un
    debordement -- seule la matiere qui DIFFERE du fond compte. Sur fond
    blanc, un pixel sombre differe du fond ; sur fond sombre, un pixel clair
    aussi. Les deux cas se mesurent avec la meme regle.

    Leve une exception nommee si le PNG est illisible -- l'appelant la rapporte,
    il ne l'avale pas.
    """
    with Image.open(png) as img:
        gray = img.convert("L")
        w, h = gray.size
        band = gray.crop((0, h - rows, w, h))
        # fond dominant = valeur la plus frequente de l'image entiere : une
        # cover a degrade ou a fond image est pleine page par design, la ligne
        # du haut seule ne la represente pas -- la mode de l'image, si
        histogram = gray.histogram()
        background = histogram.index(max(histogram))
    measurable = max(1, int(band.width * (1.0 - ignore_right_frac)))
    pixels = band.tobytes()
    # bytes ligne par ligne : sauter la bande droite exige de trancher CHAQUE
    # ligne, pas les premiers measurable*rows octets (sinon l'encre de la bande
    # droite glisse dans la mesure des lignes paires)
    ink = 0
    for r in range(band.height):
        row = pixels[r * band.width : (r + 1) * band.width]
        ink += sum(1 for v in row[:measurable] if abs(v - background) > BG_TOLERANCE)
    return ink / (measurable * band.height)


def scan_export_dir(export_dir: Path, rows: int, threshold: float,
                    ignore_right_frac: float) -> dict:
    """Scanne un repertoire d'export PNG ; retourne le rapport par slide."""
    if not export_dir.is_dir():
        raise FileNotFoundError(f"repertoire d'export introuvable : {export_dir}")
    pngs = sorted(export_dir.glob("*.png"), key=_natural_key)
    if not pngs:
        raise FileNotFoundError(f"aucun PNG dans {export_dir}")

    slides, unreadable = [], []
    for png in pngs:
        try:
            ratio = _ink_ratio(png, rows, ignore_right_frac)
        except Exception as exc:  # PNG corrompu / format inattendu : nommer, pas taire
            unreadable.append({"slide": png.name, "error": f"{type(exc).__name__}: {exc}"})
            continue
        slides.append({
            "slide": png.name,
            "ink_ratio": round(ratio, 5),
            "overflow": ratio >= threshold,
        })

    if not slides:
        raise RuntimeError(
            f"tous les PNG de {export_dir} sont illisibles : "
            f"{[u['slide'] for u in unreadable]}"
        )

    flagged = [s for s in slides if s["overflow"]]
    return {
        "export_dir": str(export_dir),
        "rows": rows,
        "threshold": threshold,
        "ignore_right_frac": ignore_right_frac,
        "slides_total": len(slides),
        "slides_overflow": len(flagged),
        "slides": slides,
        "unreadable": unreadable,
    }


def _print_table(report: dict) -> None:
    print(f"export   : {report['export_dir']}")
    print(f"mesure   : {report['rows']} dernieres lignes, seuil {report['threshold']}, "
          f"bande droite ignoree {report['ignore_right_frac']:.0%}")
    print(f"verdict  : {report['slides_overflow']}/{report['slides_total']} slides OVERFLOW")
    for u in report["unreadable"]:
        print(f"ILLISIBLE {u['slide']} -- {u['error']}", file=sys.stderr)
    for s in report["slides"]:
        if s["overflow"]:
            print(f"  OVERFLOW {s['slide']:>18}  encre {s['ink_ratio']:.1%}")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("export_dir", type=Path,
                        help="repertoire des PNG exportes (slidev export --format png)")
    parser.add_argument("--rows", type=int, default=DEFAULT_ROWS,
                        help=f"nombre de lignes de pixels en bas (defaut {DEFAULT_ROWS})")
    parser.add_argument("--threshold", type=float, default=DEFAULT_THRESHOLD,
                        help=f"ratio d'encre declenchant OVERFLOW (defaut {DEFAULT_THRESHOLD})")
    parser.add_argument("--ignore-right-frac", type=float, default=DEFAULT_IGNORE_RIGHT,
                        help="fraction droite retiree de la mesure, zone du numero de page "
                             f"(defaut {DEFAULT_IGNORE_RIGHT})")
    parser.add_argument("--json", action="store_true", help="sortie machine")
    args = parser.parse_args(argv)

    try:
        report = scan_export_dir(args.export_dir, args.rows, args.threshold,
                                 args.ignore_right_frac)
    except (FileNotFoundError, RuntimeError) as exc:
        print(f"ERREUR : {exc}", file=sys.stderr)
        return 2

    if args.json:
        print(json.dumps(report, ensure_ascii=False, indent=2))
    else:
        _print_table(report)
    # exit 1 si des debordements sont mesures : l'instrument peut servir de gate
    return 1 if report["slides_overflow"] else 0


if __name__ == "__main__":
    sys.exit(main())
