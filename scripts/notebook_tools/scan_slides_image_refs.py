"""Scan du referencement des images des decks slides/ (EPIC #11508, lot L4).

Mesure, par deck, dans quelle classe tombe chaque fichier d'image du deck. Les
deux emplacements sont enumeres : ``<deck>/images/`` et ``<deck>/public/images/``
(layout Slidev servant les visuels sous ``/images/``). Un deck peut porter les
deux ; l'union est comptee, dedoublonnee par nom de fichier.

  ACTIVE          reference dans un .md Slidev (hors ``slides.marp.md``) sur une
                  ligne NON commentee -- l'image est rendue par le deck actif
                  -- ou reference dans un composant Vue **monte** par une
                  diapositive (``components/IntelligencePyramid.vue`` importe
                  ``/images/img_022.jpg``) : le composant etant rendu, ses
                  imports le sont.  Un composant Vue non monte n'est PAS une
                  source de reference : ses images restent NOWHERE.
  COMMENT_TRAPPED reference dans un .md Slidev uniquement sur des lignes
                  ``<!-- ... -->`` -- le port a conserve la reference en
                  commentaire HTML, elle n'est jamais rendue (classe de defaut
                  #4 de l'EPIC, corrigee a la main sur S3-acculturation)
  MARP_ONLY       absente des .md Slidev, presente dans le ``slides.marp.md``
                  legacy -- le port a perdu l'image entierement (cas extreme :
                  05-theorie-des-jeux, 54/54)
  NOWHERE         aucune reference nulle part -- fichier orphelin

Le verdict final (une image COMMENT_TRAPPED doit-elle etre restauree, une
NOWHERE supprimee ?) reste un jugement de domaine -- notamment visuel : une lane
sans vision ne prononce pas qu'un rendu est correct (model-delegation). Ce scan
mesure, il ne qualifie pas.

Heuristique de commentaire : ligne dont le contenu, espaces de tete retires,
commence par ``<!--``. Un commentaire multi-lignes ouvre par ``<!--`` mais les
refs sont comptees par ligne ; les decks existants utilisent des commentaires
mono-ligne ``<!-- Image: images/img_089.png -->`` (verifie sur les 13 decks
porteurs, dont 01-introduction et son layout ``public/images/``). ``COURSE_RECAP_*``
est exclu (notes de session, pas un deck).

Usage:
  python scan_slides_image_refs.py --repo <racine>            # table lisible
  python scan_slides_image_refs.py --repo <racine> --json     # sortie machine
  python scan_slides_image_refs.py --repo <racine> --deck 03-logique
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

REF_RE = re.compile(r"images/([\w\-. ]+\.\w{3,4})")
IMAGE_EXTS = {".png", ".jpg", ".jpeg", ".gif", ".svg", ".webp"}
# Nom d'un composant Vue tel qu'il est monte (`<IntelligencePyramid />`) ou
# importe (`import Pyramid from './Pyramid.vue'`).
VUE_NAME_RE = re.compile(r"<\s*([A-Za-z][A-Za-z0-9_]*)")
VUE_IMPORT_RE = re.compile(r"import\s+([A-Za-z][A-Za-z0-9_]*)\s+from")


def _is_comment_line(line: str) -> bool:
    return line.lstrip().startswith("<!--")


def _refs_by_class(files: list[Path]) -> tuple[set[str], set[str]]:
    """Retourne (refs actives, refs piegees en commentaire) sur l'ensemble des fichiers."""
    active, trapped = set(), set()
    for md in files:
        try:
            text = md.read_text(encoding="utf-8", errors="replace")
        except OSError:
            continue
        for line in text.splitlines():
            names = REF_RE.findall(line)
            if not names:
                continue
            bucket = trapped if _is_comment_line(line) else active
            for n in names:
                bucket.add(n)
    return active, trapped


def _image_dirs(deck_dir: Path) -> list[Path]:
    """Dossiers d'images d'un deck : ``images/`` et ``public/images/`` (layout Slidev).

    L'enumeration d'un seul des deux omettait silencieusement les decks ranges sous
    ``public/images/`` -- 01-introduction, 38 fichiers, invisible du scan L4 jusqu'au
    2026-11-01 alors que le zero 669/669 le certifiait solde.
    """
    return [d for d in (deck_dir / "images", deck_dir / "public" / "images") if d.is_dir()]


def _mounted_vue_files(deck_dir: Path, slidev_md: list[Path]) -> list[Path]:
    """Composants Vue du deck reellement montes par une diapositive.

    Un composant monte rend ses imports : les images qu'il importe sont
    rendues par le deck actif, donc ACTIVE.  Un composant **non monte** ne
    rend rien : ses images restent NOWHERE -- c'est la declaration de portee
    de ce scan (un `.vue` orphelin n'est pas une source de reference).

    Le montage est etabli par le marquage du deck (``<Nom ...>`` dans un
    ``.md``) et par l'usage transitif (un composant monte par un composant
    monte).  Un composant jamais monte n'est pas une source de reference.
    """
    vue_files = [
        p for p in deck_dir.rglob("*.vue") if "node_modules" not in p.parts
    ]
    if not vue_files:
        return []

    def text_of(p: Path) -> str:
        try:
            return p.read_text(encoding="utf-8", errors="replace")
        except OSError:
            return ""

    stems = {p.stem for p in vue_files}
    md_text = "\n".join(text_of(p) for p in slidev_md)
    used: set[str] = set()
    changed = True
    while changed:
        changed = False
        for name in VUE_NAME_RE.findall(md_text):
            if name in stems and name not in used:
                used.add(name)
                changed = True
        for p in vue_files:
            if p.stem not in used:
                continue
            body = text_of(p)
            for name in VUE_IMPORT_RE.findall(body):
                if name in stems and name not in used:
                    used.add(name)
                    changed = True
    return [p for p in vue_files if p.stem in used]


def scan_deck(deck_dir: Path) -> dict:
    images = {
        f.name
        for d in _image_dirs(deck_dir)
        for f in d.iterdir()
        if f.is_file() and f.suffix.lower() in IMAGE_EXTS
    }
    all_md = [p for p in deck_dir.glob("*.md") if "RECAP" not in p.name]
    slidev_md = [p for p in all_md if "marp" not in p.name]
    marp_md = [p for p in all_md if "marp" in p.name]

    active, trapped = _refs_by_class(slidev_md)
    marp_refs, _ = _refs_by_class(marp_md)

    # Les composants Vue montes par une diapositive sont des sources de
    # reference : sans eux, une image importee par un composant tombait en
    # NOWHERE alors qu'elle est rendue (01-introduction,
    # components/IntelligencePyramid.vue).
    vue_active, vue_trapped = _refs_by_class(_mounted_vue_files(deck_dir, slidev_md))
    active |= vue_active
    trapped |= vue_trapped

    classes: dict[str, list[str]] = {"ACTIVE": [], "COMMENT_TRAPPED": [], "MARP_ONLY": [], "NOWHERE": []}
    for name in sorted(images):
        if name in active:
            classes["ACTIVE"].append(name)
        elif name in trapped:
            classes["COMMENT_TRAPPED"].append(name)
        elif name in marp_refs:
            classes["MARP_ONLY"].append(name)
        else:
            classes["NOWHERE"].append(name)
    return {
        "deck": deck_dir.name,
        "total": len(images),
        "classes": classes,
    }


def scan_slides_dir(slides_dir: Path) -> list[dict]:
    decks = sorted(
        d
        for d in slides_dir.iterdir()
        if d.is_dir() and _image_dirs(d)
    )
    return [scan_deck(d) for d in decks]


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--repo", required=True, help="Racine du depot (contient slides/)")
    ap.add_argument("--deck", help="Limiter a un deck (nom du sous-dossier)")
    ap.add_argument("--json", action="store_true", help="Sortie JSON machine")
    args = ap.parse_args(argv)

    slides_dir = Path(args.repo) / "slides"
    if not slides_dir.is_dir():
        print(f"ERREUR: {slides_dir} introuvable", file=sys.stderr)
        return 2

    if args.deck:
        deck_dir = slides_dir / args.deck
        if not _image_dirs(deck_dir):
            print(f"ERREUR: {deck_dir} sans dossier images/ ni public/images/", file=sys.stderr)
            return 2
        results = [scan_deck(deck_dir)]
    else:
        results = scan_slides_dir(slides_dir)

    totals = {k: 0 for k in ("ACTIVE", "COMMENT_TRAPPED", "MARP_ONLY", "NOWHERE")}
    grand = 0
    for r in results:
        grand += r["total"]
        for k in totals:
            totals[k] += len(r["classes"][k])

    if args.json:
        print(json.dumps({"decks": results, "totals": totals, "grand_total": grand}, ensure_ascii=False, indent=1))
        return 0

    header = f'{"deck":40s} {"imgs":>4s} {"active":>6s} {"comment":>7s} {"marp-only":>9s} {"nowhere":>7s}'
    print(header)
    print("-" * len(header))
    for r in results:
        c = r["classes"]
        print(
            f'{r["deck"]:40s} {r["total"]:4d} {len(c["ACTIVE"]):6d} '
            f'{len(c["COMMENT_TRAPPED"]):7d} {len(c["MARP_ONLY"]):9d} {len(c["NOWHERE"]):7d}'
        )
    print("-" * len(header))
    rate = 100 * totals["ACTIVE"] / grand if grand else 0.0
    print(
        f'TOTAL {grand} fichiers | actifs {totals["ACTIVE"]} ({rate:.0f}%) | '
        f'pieges-commentaire {totals["COMMENT_TRAPPED"]} | marp-only {totals["MARP_ONLY"]} | '
        f'orphelins {totals["NOWHERE"]}'
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
