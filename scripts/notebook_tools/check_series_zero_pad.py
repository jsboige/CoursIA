"""Garde de convention zero-pad d'une serie de notebooks (#11840, #12586).

Une serie qui a tranche sa numerotation a deux chiffres (GameTheory : 01..26,
side-tracks en lettres 03a/08d) doit y rester. Six side-tracks au chiffre
unique sont arrives sur main ENTRE la review et le merge de la tranche 1
(#12241) : un invariant verifie a l'instant t n'est pas une propriete du
livrable, seul un garde qui rougit en fait une. Sans lui, chaque nouveau
side-track rouvre une tranche de renommage, indefiniment.

Le motif vise exactement le chiffre unique : un premier chiffre NON suivi
d'un second chiffre. Les formes valides ne matchent pas :

    GameTheory-03a-...  (zero-pade, le 0 est suivi de 3)
    GameTheory-26-...   (deux chiffres)
    GameTheory-04c-...  (deux chiffres + lettre de side-track)

Portee volontairement ETROITE : la serie passee en argument, GameTheory par
defaut (la seule zero-padee a ce jour). Ne pas l'etendre a une autre serie
sans avoir mesure si elle a une convention arretee -- une regle imposee a une
serie qui n'a pas tranche fabrique du rouge sans defaut (scope fige par
#12586).
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]

# Grammaire de nom partagee (#5081/#15489) : le numero d'un `Prefixe-NN` se lit
# avec les autres gardes de nommage, pas avec un motif local.
_here = str(Path(__file__).resolve().parent)
if _here not in sys.path:
    sys.path.insert(0, _here)
from naming_canon import parse_name  # noqa: E402


def violations(series_dir: Path, prefix: str = "GameTheory") -> list[dict]:
    """Fichiers de la serie dont le numero n'est PAS zero-pade.

    Le chiffre unique se lit dans le numero rendu par le parseur du canon
    (#15489) : ``GameTheory-3a`` livre ``number="3"`` (un chiffre), ``GameTheory-26``
    livre ``"26"``, ``GameTheory-04c`` livre ``"04"``. La regle porte sur la
    LONGUEUR du numero et non sur un motif du nom complet -- un motif local
    re-encode la grammaire du canon, et deux encodages divergent au premier cas
    limite (c'est ce que #15489 corrige).
    """
    out: list[dict] = []
    for path in sorted(series_dir.rglob(f"{prefix}-*")):
        if not path.is_file():
            continue
        parsed = parse_name(path.name)
        if parsed.series != prefix or parsed.number is None:
            continue
        if len(parsed.number) == 1:
            try:
                shown = path.relative_to(REPO_ROOT).as_posix()
            except ValueError:
                shown = path.as_posix()
            out.append({"file": shown, "name": path.name})
    return out


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Echoue si un fichier de la serie porte un numero "
                    "non zero-pade (convention NN, #11840/#12586).")
    parser.add_argument("--series-dir", default="MyIA.AI.Notebooks/GameTheory",
                        help="repertoire de la serie (relatif a la racine du depot)")
    parser.add_argument("--prefix", default="GameTheory",
                        help="prefixe des fichiers de la serie")
    parser.add_argument("--json", action="store_true",
                        help="sortie machine-readable")
    args = parser.parse_args(argv)

    series_dir = Path(args.series_dir)
    if not series_dir.is_absolute():
        series_dir = REPO_ROOT / series_dir
    if not series_dir.is_dir():
        print(f"[zero-pad] repertoire introuvable : {series_dir}",
              file=sys.stderr)
        return 2

    found = violations(series_dir, args.prefix)
    if args.json:
        print(json.dumps({
            "series_dir": args.series_dir,
            "prefix": args.prefix,
            "count": len(found),
            "violations": found,
        }, ensure_ascii=False, indent=1))
    else:
        for v in found:
            print(f"VIOLATION {v['file']}")
    if found:
        print(f"[zero-pad] {len(found)} fichier(s) au chiffre unique -- la "
              f"convention {args.prefix}-NN exige deux chiffres "
              f"(side-tracks valides : {args.prefix}-03a, -08d).",
              file=sys.stderr)
        return 1
    if not args.json:
        print(f"[zero-pad] OK : aucun {args.prefix}-<chiffre unique> "
              f"dans {args.series_dir}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
