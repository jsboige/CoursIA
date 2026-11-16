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
- l'encre est relative au fond dominant de la slide (mesure sur la MODE de
  l'image entiere, tolerance ``BG_TOLERANCE``) : une page de titre sombre n'est
  pas un debordement -- seul ce qui DIFFERE du fond compte, sur fond clair comme
  sur fond sombre. Le fond est la valeur la plus frequente de l'image entiere,
  pas la ligne du haut : une cover a degrade ou a fond image est pleine page par
  design, et la seule ligne du haut ne la represente pas.

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
  python scan_slidev_overflow.py <repertoire_png> --archive releve.json
  python scan_slidev_overflow.py --compare releve-avant.json releve-apres.json

L'opposabilite d'un releve (#24171) : le rendu Slidev ne depend que des
polices SYSTEME (aucune ``@font-face`` dans ``slides/``), donc deux releves
du meme deck pris sur deux machines ne sont pas comparables. L'instrument le
dit dans sa sortie, archive le releve avec le hash de chaque PNG mesure
(``--archive``), et compare deux ARTEFACTS (``.compare``) -- jamais deux
compteurs rejoues.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import platform
import re
import sys
from datetime import datetime, timezone
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

# Le rendu Slidev ne depend que des polices SYSTEME : `slides/` ne declare
# aucune `@font-face`, donc les metriques de texte -- et la hauteur des blocs
# -- varient d'une machine a l'autre. Deux releves du meme deck, sur deux
# machines, ne sont pas opposables : c'est le constat de #24171 (ecart
# 2 -> 1 diapositive hors canvas sur `S8-semantic-web`, sans modification du
# depot qui l'explique). L'instrument le DIT dans sa sortie et propose la voie
# qui reste opposeable : archiver le releve (avec le hash des PNG) et comparer
# deux ARTEFACTS, plutot que rejouer un compteur sur la machine de chacun.
FONT_DEPENDENCY = (
    "les metriques dependent des polices systeme resolues : un releve n'est "
    "pas opposable d'une machine a l'autre -- comparer des artefacts "
    "archives (--archive), pas des compteurs rejoues (cf #24171)"
)


def _natural_key(path: Path):
    """Cle de tri numerique : 1, 2, ... 10, 11 -- pas 1, 10, 11, 2."""
    return [
        int(part) if part.isdigit() else part.lower()
        for part in re.split(r"(\d+)", path.name)
    ]


def _ink_ratio(png: Path, rows: int, ignore_right_frac: float) -> float:
    """Ratio encre / largeur mesurable sur les ``rows`` dernieres lignes du PNG.

    L'encre est RELATIVE au fond dominant de la slide (mesure sur la MODE de
    l'image entiere, pas sur la ligne du haut) : sur un deck a pages sombres, le
    fond sombre n'est pas un debordement -- seule la matiere qui DIFFERE du
    fond compte. Sur fond blanc, un pixel sombre differe du fond ; sur fond
    sombre, un pixel clair aussi. Les deux cas se mesurent avec la meme regle.

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


def _platform_fingerprint() -> dict:
    """Empreinte de la machine qui a produit le releve.

    Elle n'explique pas la mesure -- elle dit sur QUELLE machine elle a ete
    prise, ce qui est la premiere question a se poser quand deux releves ne
    concordent pas (#24171). Les polices systeme ne sont pas versionnees :
    l'empreinte est donc une indication, pas une garantie de reproductibilite.
    """
    return {
        "system": platform.system(),
        "release": platform.release(),
        "machine": platform.machine(),
        "python": platform.python_version(),
    }


def _sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as fh:
        for block in iter(lambda: fh.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()


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
        "font_dependency": FONT_DEPENDENCY,
        "platform": _platform_fingerprint(),
    }


def archive_report(report: dict, archive_path: Path) -> dict:
    """Ecrit le releve sous forme d'ARTEFACT versionne et opposable.

    L'artefact porte le hash de chaque PNG mesure : deux releves ne sont
    comparables que si les images qu'ils ont mesurees sont les memes. C'est la
    voie opposeable que #24171 demande en alternative a l'embarquement de
    polices dans le depot.
    """
    export_dir = Path(report["export_dir"])
    hashes = {}
    for slide in report["slides"]:
        png = export_dir / slide["slide"]
        hashes[slide["slide"]] = _sha256(png) if png.is_file() else None
    artifact = {
        "kind": "scan_slidev_overflow",
        "version": 1,
        "generated_at": datetime.now(timezone.utc).isoformat(timespec="seconds"),
        "report": report,
        "png_sha256": hashes,
    }
    # Le contenu se hash LUI-MEME (empreinte calculee sur l'artefact sans ce
    # champ) : un tiers peut verifier l'artefact sans l'avoir produit. Le
    # sha256 du FICHIER entier, lui, est affiche par l'outil -- un fichier ne
    # peut pas porter son propre hash.
    payload = json.dumps(artifact, ensure_ascii=False, indent=2)
    artifact["content_sha256"] = hashlib.sha256(payload.encode("utf-8")).hexdigest()
    payload = json.dumps(artifact, ensure_ascii=False, indent=2)
    archive_path.parent.mkdir(parents=True, exist_ok=True)
    archive_path.write_text(payload + "\n", encoding="utf-8", newline="")
    artifact["artifact_sha256"] = hashlib.sha256(payload.encode("utf-8")).hexdigest()
    return artifact


def _overflow_set(artifact: dict) -> set:
    slides = artifact.get("report", {}).get("slides", [])
    return {s["slide"] for s in slides if s.get("overflow")}


def compare_artifacts(left: dict, right: dict) -> dict:
    """Compare deux artefacts archives -- jamais deux compteurs rejoues.

    Le resultat separe ce qui a ete corrige de ce qui est apparu, et signale
    les comparaisons non concluantes : images differentes, ou machines
    differentes (les polices systeme ne sont pas versionnees).
    """
    l_over, r_over = _overflow_set(left), _overflow_set(right)
    l_hashes = left.get("png_sha256", {})
    r_hashes = right.get("png_sha256", {})
    common = set(l_hashes) & set(r_hashes)
    changed = sorted(n for n in common if l_hashes[n] and r_hashes[n]
                     and l_hashes[n] != r_hashes[n])
    # Une image qui change sur une diapositive corrigee est ATTENDUE : elle ne
    # rend pas la comparaison non concluante. Ce qui la rend non concluante,
    # c'est une diapositive qui deborde DANS LES DEUX releves ET dont l'image
    # a change : on a alors compare deux rendus differents de la meme slide.
    differ = sorted(n for n in changed if n in (l_over & r_over))
    return {
        "slides_total": (left.get("report", {}).get("slides_total"),
                         right.get("report", {}).get("slides_total")),
        "overflow": (len(l_over), len(r_over)),
        "fixed": sorted(l_over - r_over),
        "new": sorted(r_over - l_over),
        "common_overflow": sorted(l_over & r_over),
        "png_changed": changed,
        "png_differ": differ,
        "platform_differs": left.get("report", {}).get("platform")
        != right.get("report", {}).get("platform"),
        "font_dependency": FONT_DEPENDENCY,
    }


def _print_table(report: dict) -> None:
    print(f"export   : {report['export_dir']}")
    print(f"mesure   : {report['rows']} dernieres lignes, seuil {report['threshold']}, "
          f"bande droite ignoree {report['ignore_right_frac']:.0%}")
    print(f"verdict  : {report['slides_overflow']}/{report['slides_total']} slides OVERFLOW")
    plate = report.get("platform", {})
    print(f"machine  : {plate.get('system', '?')} {plate.get('release', '?')} "
          f"({plate.get('machine', '?')})")
    print(f"dependance : {report['font_dependency']}")
    for u in report["unreadable"]:
        print(f"ILLISIBLE {u['slide']} -- {u['error']}", file=sys.stderr)
    for s in report["slides"]:
        if s["overflow"]:
            print(f"  OVERFLOW {s['slide']:>18}  encre {s['ink_ratio']:.1%}")


def _print_comparison(left_path: Path, right_path: Path, cmp: dict) -> None:
    total_l, total_r = cmp["slides_total"]
    print(f"compare  : {left_path.name} -> {right_path.name}")
    print(f"slides   : {total_l} -> {total_r}")
    print(f"overflow : {cmp['overflow'][0]} -> {cmp['overflow'][1]}")
    print(f"corriges : {', '.join(cmp['fixed']) or 'aucune'}")
    print(f"nouveaux : {', '.join(cmp['new']) or 'aucune'}")
    print(f"communes : {', '.join(cmp['common_overflow']) or 'aucune'}")
    if cmp["png_differ"]:
        print(f"AVERTISSEMENT : {len(cmp['png_differ'])} diapositives debordent dans les "
              f"DEUX releves et leur PNG a change -- la comparaison y porte sur des "
              f"images differentes : {', '.join(cmp['png_differ'])}")
    if cmp["platform_differs"]:
        print("AVERTISSEMENT : releves pris sur des machines differentes -- les "
              "polices systeme ne sont pas versionnees, l'ecart peut etre "
              "machine (cf #24171)")
    print(f"dependance : {cmp['font_dependency']}")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("export_dir", type=Path, nargs="?",
                        help="repertoire des PNG exportes (slidev export --format png)")
    parser.add_argument("--rows", type=int, default=DEFAULT_ROWS,
                        help=f"nombre de lignes de pixels en bas (defaut {DEFAULT_ROWS})")
    parser.add_argument("--threshold", type=float, default=DEFAULT_THRESHOLD,
                        help=f"ratio d'encre declenchant OVERFLOW (defaut {DEFAULT_THRESHOLD})")
    parser.add_argument("--ignore-right-frac", type=float, default=DEFAULT_IGNORE_RIGHT,
                        help="fraction droite retiree de la mesure, zone du numero de page "
                             f"(defaut {DEFAULT_IGNORE_RIGHT})")
    parser.add_argument("--json", action="store_true", help="sortie machine")
    parser.add_argument("--archive", type=Path, metavar="PATH",
                        help="ecrit le releve sous forme d'artefact versionne "
                             "(hash de chaque PNG) : la voie opposeable de #24171")
    parser.add_argument("--compare", nargs=2, type=Path, metavar=("A", "B"),
                        help="compare deux artefacts archives -- jamais deux "
                             "compteurs rejoues sur deux machines")
    args = parser.parse_args(argv)

    if args.compare:
        artifacts = []
        for path in args.compare:
            try:
                artifacts.append(json.loads(path.read_text(encoding="utf-8")))
            except (OSError, json.JSONDecodeError) as exc:
                print(f"ERREUR : artefact illisible : {path} -- {exc}", file=sys.stderr)
                return 2
        cmp = compare_artifacts(artifacts[0], artifacts[1])
        if args.json:
            print(json.dumps(cmp, ensure_ascii=False, indent=2))
        else:
            _print_comparison(args.compare[0], args.compare[1], cmp)
        return 1 if cmp["overflow"][1] else 0

    if args.export_dir is None:
        parser.error("export_dir est requis (ou --compare A B)")

    try:
        report = scan_export_dir(args.export_dir, args.rows, args.threshold,
                                 args.ignore_right_frac)
    except (FileNotFoundError, RuntimeError) as exc:
        print(f"ERREUR : {exc}", file=sys.stderr)
        return 2

    if args.archive:
        artifact = archive_report(report, args.archive)
        print(f"archive   : {args.archive} (sha256 {artifact['artifact_sha256']})",
              file=sys.stderr)

    if args.json:
        print(json.dumps(report, ensure_ascii=False, indent=2))
    else:
        _print_table(report)
    # exit 1 si des debordements sont mesures : l'instrument peut servir de gate
    return 1 if report["slides_overflow"] else 0


if __name__ == "__main__":
    sys.exit(main())
