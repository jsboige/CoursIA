"""Lit nom par nom les etiquettes qu'un journal `--dir-label-boxes` dit retenues.

Le journal dit quelles boites le binaire a gardees ; il ne dit pas si le nom
se lit dans les pixels. Pour le mesurer, chaque boite retenue est decoupee de
la trame 4K -- avec ce qui est dessous, etincelles de fichiers comprises --
agrandie, et ecrite en PNG sous la forme que parcourt `ocr_trames.ps1`
(`<dossier>/trame_N.png`). L'OCR se lance ensuite avec ce script, puis
`joindre` confronte le texte lu au nom attendu.

Le journal porte treize colonnes ; la septieme est le haut de la ligne telle
qu'elle est dessinee, et la neuvieme sa hauteur. Un journal a douze colonnes
vient d'un binaire anterieur, qui notait le haut de la boite 28 px trop haut
pour une police de taille 20 : ce script le refuse plutot que de decouper a
cote.

Une trame tiree a une image par seconde pour la seconde s n'est pas le top
60*s : `ffmpeg -vf fps=1` retient l'image 30*s+14, soit le top 60*s+28
(mesure sur un film a 30 images par seconde). `--decalage` porte ce 28 ; le
mettre a 0 pour une trame exportee a un top connu exactement.

Usage :
    python lire_noms.py decouper <journal> <trame.png> <seconde> <sortie> \
        [--facteur 3] [--marge 10] [--decalage 28]
    powershell -File ocr_trames.ps1 -Root <sortie> -Out <sortie>/lignes.tsv
    python lire_noms.py joindre <sortie>/lignes.tsv <sortie>/boites.tsv

`decouper` ecrit <sortie>/s<seconde>/trame_N.png et <sortie>/boites.tsv
(une ligne par nom retenu, dans le repere de la trame).

Verdicts de `joindre` : entier (le texte lu est le nom attendu, cas, signes
et espaces ignores), partiel (l'un tient dans l'autre, deux caracteres au
moins), autre. Un nom que l'OCR ne rend pas n'est pas forcement illisible :
c'est une borne inferieure de la lisibilite, pas son jugement.
"""
from __future__ import annotations

import argparse
import sys
from collections import Counter
from pathlib import Path

TOPS_PAR_SECONDE = 60
GROUPES = {0: "hors hub", 1: "hub", 2: "sous hub nomme"}
TRANCHES_ALPHA = ((0.75, 1.01, "alpha >= 0,75"),
                  (0.50, 0.75, "0,50 <= alpha < 0,75"),
                  (0.25, 0.50, "0,25 <= alpha < 0,50"),
                  (-0.01, 0.25, "alpha < 0,25"))


def normaliser(texte: str) -> str:
    """Minuscules, sans espaces ni signes : compare `MGS-vs-mealpy` a `MGS vs mealpy`."""
    return "".join(ch for ch in texte.lower() if ch.isalnum())


def verdict(attendu: str, lu: str) -> str:
    a, l = normaliser(attendu), normaliser(lu)
    if not l:
        return "autre"
    if a == l:
        return "entier"
    if len(l) >= 2 and (l in a or a in l):
        return "partiel"
    return "autre"


def lire_journal(journal: Path, top: int) -> list[dict]:
    """Les lignes L d'un top, retenues seulement, triees par alpha decroissant."""
    lignes: list[dict] = []
    for raw in journal.read_text(encoding="utf-8", errors="replace").splitlines():
        c = raw.split("\t")
        if c[0] != "L":
            continue
        if len(c) == 12:
            raise SystemExit(
                f"{journal.name} : journal a 12 colonnes, ecrit par un binaire "
                f"anterieur -- son ordonnee est 28 px trop haut pour une police "
                f"de taille 20. Regenerer le journal avec le binaire courant.")
        if len(c) != 13 or int(c[1]) != top:
            continue
        if int(c[9]) != 1:
            continue
        lignes.append({"texte": c[2], "profondeur": int(c[3]),
                       "alpha": float(c[4]), "x": float(c[5]),
                       "y": float(c[6]), "l": float(c[7]), "h": float(c[8]),
                       "groupe": int(c[11])})
    return sorted(lignes, key=lambda e: -e["alpha"])


def tops_lus(journal: Path) -> list[int]:
    """Les tops auxquels le journal porte des noms, pour un message d'erreur utile."""
    tops: set[int] = set()
    for raw in journal.read_text(encoding="utf-8", errors="replace").splitlines():
        c = raw.split("\t")
        if c[0] == "L" and len(c) == 13:
            tops.add(int(c[1]))
    return sorted(tops)


def decouper(journal: Path, trame: Path, seconde: int, sortie: Path,
             facteur: int, marge: int, decalage: int) -> int:
    from PIL import Image  # import local : PIL ne sert qu'a ce sous-programme

    top = seconde * TOPS_PAR_SECONDE + decalage
    noms = lire_journal(journal, top)
    if not noms:
        lus = tops_lus(journal)
        plus_proche = min(lus, key=lambda t: abs(t - top)) if lus else None
        print(f"aucun nom retenu au top {top} (seconde {seconde}, decalage "
              f"{decalage}) ; tops lus : {len(lus)}"
              + (f", le plus proche {plus_proche} (ecart {plus_proche - top:+d})"
                 if plus_proche is not None else ""), file=sys.stderr)
        return 1
    dossier = sortie / f"s{seconde}"
    dossier.mkdir(parents=True, exist_ok=True)
    image = Image.open(trame).convert("RGB")
    lignes = ["variante\tindice\ttexte\tprofondeur\talpha\tgroupe\tx\ty\tlargeur\thauteur"]
    for k, nom in enumerate(noms):
        gauche = max(0, int(nom["x"]) - marge)
        haut = max(0, int(nom["y"]) - marge)
        droite = min(image.width, int(nom["x"] + nom["l"]) + marge)
        bas = min(image.height, int(nom["y"] + nom["h"]) + marge)
        decoupe = image.crop((gauche, haut, droite, bas))
        decoupe = decoupe.resize((decoupe.width * facteur, decoupe.height * facteur),
                                 Image.LANCZOS)
        decoupe.save(dossier / f"trame_{k}.png")
        lignes.append(f"{dossier.name}\t{k}\t{nom['texte']}\t{nom['profondeur']}\t"
                      f"{nom['alpha']:.2f}\t{nom['groupe']}\t{nom['x']:.0f}\t"
                      f"{nom['y']:.0f}\t{nom['l']:.0f}\t{nom['h']:.0f}")
    (sortie / "boites.tsv").write_text("\n".join(lignes) + "\n", encoding="utf-8")
    print(f"seconde {seconde} (top {top}) : {len(noms)} noms retenus decoupes "
          f"x{facteur} dans {dossier}")
    return 0


def joindre(lignes_ocr: Path, boites: Path) -> int:
    lus: dict[str, list[str]] = {}
    for raw in lignes_ocr.read_text(encoding="utf-8", errors="replace").splitlines():
        if raw.startswith("#") or not raw.strip():
            continue
        c = raw.split("\t")
        if len(c) >= 7:
            lus.setdefault(f"{c[0]}\t{c[1]}", []).append(c[6])

    attends: list[dict] = []
    lignes = boites.read_text(encoding="utf-8").splitlines()
    for raw in lignes[1:]:
        c = raw.split("\t")
        if len(c) >= 10:
            attends.append({"cle": f"{c[0]}\t{c[1]}", "texte": c[2],
                            "profondeur": int(c[3]), "alpha": float(c[4]),
                            "groupe": int(c[5]), "lu": " ".join(lus.get(f"{c[0]}\t{c[1]}", []))})

    if not attends:
        print("aucune boite lue", file=sys.stderr)
        return 1
    for a in attends:
        a["verdict"] = verdict(a["texte"], a["lu"])

    total = Counter(a["verdict"] for a in attends)
    n = len(attends)
    print(f"noms retenus : {n}")
    for v in ("entier", "partiel", "autre"):
        print(f"  {v:8s}: {total.get(v, 0):4d} ({100.0 * total.get(v, 0) / n:.1f} %)")

    def recap(titre: str, selection: list[dict]) -> None:
        if not selection:
            return
        c = Counter(a["verdict"] for a in selection)
        print(f"    {titre:24s} {len(selection):4d} noms, entiers {c.get('entier', 0):4d} "
              f"({100.0 * c.get('entier', 0) / len(selection):.1f} %), "
              f"partiels {c.get('partiel', 0):3d}, autres {c.get('autre', 0):3d}")

    print("  par groupe :")
    for groupe in sorted(GROUPES):
        recap(GROUPES[groupe], [a for a in attends if a["groupe"] == groupe])
    print("  par tranche d'alpha :")
    for bas, haut, titre in TRANCHES_ALPHA:
        recap(titre, [a for a in attends if bas <= a["alpha"] < haut])

    print("\n  detail (alpha decroissant) :")
    for a in attends:
        print(f"    {a['verdict']:8s} prof.{a['profondeur']} groupe {a['groupe']} "
              f"alpha {a['alpha']:.2f}  {a['texte']:32s} lu : {a['lu']!r}")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sous = parser.add_subparsers(dest="commande", required=True)
    d = sous.add_parser("decouper", help="decouper et agrandir les noms retenus d'une seconde")
    d.add_argument("journal", type=Path)
    d.add_argument("trame", type=Path)
    d.add_argument("seconde", type=int)
    d.add_argument("sortie", type=Path)
    d.add_argument("--facteur", type=int, default=3)
    d.add_argument("--marge", type=int, default=10)
    d.add_argument("--decalage", type=int, default=28,
                   help="top de la trame par rapport a 60*s (ffmpeg fps=1 : 28)")
    j = sous.add_parser("joindre", help="confronter le texte OCR au nom attendu")
    j.add_argument("lignes_ocr", type=Path)
    j.add_argument("boites", type=Path)
    args = parser.parse_args(argv)

    # Les noms et le texte OCR portent des caracteres hors cp1252 : une
    # console paree qui ne peut pas les encoder arrete le script en silence.
    for flux in (sys.stdout, sys.stderr):
        if hasattr(flux, "reconfigure"):
            flux.reconfigure(encoding="utf-8", errors="replace")

    if args.commande == "decouper":
        return decouper(args.journal, args.trame, args.seconde, args.sortie,
                        args.facteur, args.marge, args.decalage)
    return joindre(args.lignes_ocr, args.boites)


if __name__ == "__main__":
    raise SystemExit(main())
