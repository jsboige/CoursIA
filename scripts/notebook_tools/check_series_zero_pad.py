"""Garde de convention zero-pad d'une serie de notebooks (#11840, #12586, #15489).

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

PORTEE : REGISTRE EXPLICITE, JAMAIS UN DEFAUT (#15489, defaut 5)
--------------------------------------------------------------
L'issue est explicite -- "check_series_zero_pad.py doit rester opt-in par
series migrees ; une activation globale avant cartographie creerait un mur
rouge inutilisable" -- et son acceptance demande "Padding active par liste
explicite de series migrees, avec tests de non-regression sur familles non
encore adoptees".

Avant cette tranche, la portee vivait dans deux defauts argparse
(`--series-dir` = GameTheory, `--prefix` = GameTheory) et une phrase de
docstring. C'etait une convention de fait : non datee, non justifiee, et
invisible a tout controle automatique -- rien ne distinguait "GameTheory est
la seule serie zero-padee" (vrai en #12586) de "GameTheory est la seule
serie zero-padee" (faux depuis que sept autres l'ont adopte en silence).
La portee vit desormais dans `zero_pad_series.json`, ou chaque serie est
nommee, datee, mesuree et justifiee.

Le critere d'admission a DEUX moities, et les deux sont mesurees :

  (a) la serie PROUVE son padding -- au moins un fichier dont le numero porte
      un zero de tete (`01`, `04a`). Une serie qui ne porte que des numeros
      >= 10 n'a rien adopte : elle n'a simplement aucun numero a un chiffre,
      donc son etat ne dit rien de sa convention. Sept familles sont dans ce
      cas et restent hors registre ;
  (b) la serie ne porte AUCUNE violation sur son arbre ENTIER. C'est ce qui
      distingue ce garde du garde de casse canonique des suffixes (#15489
      defaut 3) : celui-la est DELTA (`--diff-filter=A`) et peut donc
      declarer une serie en laissant ses fichiers herites non conformes.
      Ici le scan est whole-tree (`rglob` recursif), donc declarer une serie
      non migree rougit des dizaines de fichiers d'un seul coup -- le mur
      rouge que l'issue interdit. La mesure du 2026-09-11 en denombre 20.

Ces 20 familles et leurs comptes sont conserves dans le registre sous
`_not_declared`, pour que la liste ne soit pas "elargie" par inadvertance :
chaque ligne y porte le nombre de fichiers qui rougiraient.

CE QUE CE GARDE NE FAIT PAS
---------------------------
Il ne migre aucune serie : renommer les fichiers d'une famille est une
tranche a part, avec ses README et ses navlinks. Il ne verifie pas non plus
que le registre est "complet" -- l'absence d'une serie n'est pas un defaut,
c'est le regime par defaut (opt-in).

Usage
-----
    python scripts/notebook_tools/check_series_zero_pad.py
        -> scanne TOUTES les series du registre (c'est l'invocation CI)

    python scripts/notebook_tools/check_series_zero_pad.py --series-dir <d> --prefix <P>
        -> scanne une seule serie (surcharge explicite, prime sur le registre)

    python scripts/notebook_tools/check_series_zero_pad.py --json
    python scripts/notebook_tools/check_series_zero_pad.py --list-series

Sortie : 0 = aucune violation ; 1 = violation(s) ; 2 = erreur d'invocation
(dont un repertoire declare absent du disque, qui est un defaut du registre).
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

#: Registre des series ayant adopte le zero-pad. Vit a cote de l'organe : le
#: registre et le garde qui le lit ne doivent pas pouvoir deriver l'un de
#: l'autre sans que le diff le montre.
REGISTRY_PATH = Path(__file__).resolve().parent / "zero_pad_series.json"


def violations(series_dir: Path, prefix: str = "GameTheory") -> list[dict]:
    """Fichiers de la serie dont le numero n'est PAS zero-pade.

    Le chiffre unique se lit dans le numero rendu par le parseur du canon
    (#15489) : ``GameTheory-3a`` livre ``number="3"`` (un chiffre), ``GameTheory-26``
    livre ``"26"``, ``GameTheory-04c`` livre ``"04"``. La regle porte sur la
    LONGUEUR du numero et non sur un motif du nom complet -- un motif local
    re-encode la grammaire du canon, et deux encodages divergent au premier cas
    limite (c'est ce que #15489 corrige).

    Le balayage est RECURSIF : un sous-dossier non declare compte. C'est
    volontaire -- l'arbre entier d'une serie declaree est sous la convention,
    sans quoi une sous-serie pourrait deriver sans que le garde le voie.
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


def load_registry(path: Path | None = None) -> list[dict]:
    """Series declarees zero-padees, telles que lues dans le registre.

    Leve ``RegistryError`` si le registre est illisible ou malforme : un
    registre casse doit faire echouer l'organe, jamais le rendre muet en
    retombant sur une portee vide (une portee vide rend 0 violation, donc un
    vert -- le pire des modes de defaillance pour un garde).
    """
    path = path or REGISTRY_PATH
    try:
        raw = json.loads(path.read_text(encoding="utf-8"))
    except OSError as exc:
        raise RegistryError(f"registre illisible : {path} ({exc})") from exc
    except json.JSONDecodeError as exc:
        raise RegistryError(f"registre malforme : {path} ({exc})") from exc

    adopted = raw.get("adopted")
    if not isinstance(adopted, list) or not adopted:
        raise RegistryError(
            f"registre sans section 'adopted' non vide : {path}")

    out: list[dict] = []
    for entry in adopted:
        if not isinstance(entry, dict):
            raise RegistryError(f"entree de registre non-objet : {entry!r}")
        series, directory = entry.get("series"), entry.get("dir")
        if not series or not directory:
            raise RegistryError(
                f"entree de registre sans 'series'/'dir' : {entry!r}")
        out.append({"series": series, "dir": directory,
                    "note": entry.get("note", "")})
    return out


class RegistryError(Exception):
    """Le registre est absent, illisible, malforme, ou pointe dans le vide."""


def _resolve(directory: str) -> Path:
    p = Path(directory)
    return p if p.is_absolute() else REPO_ROOT / p


def _scan_registry(entries: list[dict]) -> tuple[list[dict], list[str]]:
    """Scanne chaque serie declaree. Rend (rapport par serie, repertoires absents).

    Un repertoire declare absent n'est PAS silencieusement ignore : le registre
    nomme des series qui doivent exister, et une serie declaree disparue est un
    defaut du registre, pas une raison de rendre un vert.
    """
    report: list[dict] = []
    missing: list[str] = []
    for entry in entries:
        series_dir = _resolve(entry["dir"])
        if not series_dir.is_dir():
            missing.append(entry["dir"])
            continue
        found = violations(series_dir, entry["series"])
        report.append({"series": entry["series"], "dir": entry["dir"],
                       "count": len(found), "violations": found})
    return report, missing


def _emit_text(report: list[dict]) -> None:
    for block in report:
        for v in block["violations"]:
            print(f"VIOLATION {block['series']} {v['file']}")
    for block in report:
        state = "OK" if not block["count"] else f"{block['count']} violation(s)"
        print(f"[zero-pad] {block['series']:<12} {block['dir']} : {state}")


def _summarize(report: list[dict]) -> str:
    total = sum(b["count"] for b in report)
    clean = [b["series"] for b in report if not b["count"]]
    dirty = [f"{b['series']} ({b['count']})" for b in report if b["count"]]
    parts = [f"{len(report)} serie(s) declaree(s), {total} violation(s)"]
    if clean:
        parts.append("conformes : " + ", ".join(clean))
    if dirty:
        parts.append("a corriger : " + ", ".join(dirty))
    return "[zero-pad] " + " | ".join(parts)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Echoue si un fichier d'une serie DECLAREE zero-padee "
                    "porte un numero non zero-pade (convention NN, #11840/"
                    "#12586). Sans argument, scanne les series du registre "
                    "explicite (#15489 defaut 5).")
    parser.add_argument("--series-dir", default=None,
                        help="surcharge : repertoire d'UNE serie (relatif a la "
                             "racine du depot). Omettez-le pour scanner le "
                             "registre entier.")
    parser.add_argument("--prefix", default="GameTheory",
                        help="prefixe des fichiers, avec --series-dir "
                             "(defaut : GameTheory, forme historique)")
    parser.add_argument("--registry", default=None,
                        help=f"chemin du registre (defaut : {REGISTRY_PATH.name})")
    parser.add_argument("--list-series", action="store_true",
                        help="liste les series declarees et sort")
    parser.add_argument("--json", action="store_true",
                        help="sortie machine-readable")
    args = parser.parse_args(argv)

    if args.list_series:
        try:
            entries = load_registry(Path(args.registry) if args.registry else None)
        except RegistryError as exc:
            print(f"[zero-pad] {exc}", file=sys.stderr)
            return 2
        for e in entries:
            print(f"{e['series']}\t{e['dir']}")
        return 0

    # --- Mode surcharge : une seule serie, forme historique ----------------
    if args.series_dir is not None:
        series_dir = _resolve(args.series_dir)
        if not series_dir.is_dir():
            print(f"[zero-pad] repertoire introuvable : {series_dir}",
                  file=sys.stderr)
            return 2
        found = violations(series_dir, args.prefix)
        if args.json:
            print(json.dumps({
                "schema": 2,
                "mode": "series",
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
                  f"dans {series_dir}")
        return 0

    # --- Mode registre : c'est l'invocation CI -----------------------------
    try:
        entries = load_registry(Path(args.registry) if args.registry else None)
    except RegistryError as exc:
        print(f"[zero-pad] {exc}", file=sys.stderr)
        return 2

    report, missing = _scan_registry(entries)
    for d in missing:
        print(f"[zero-pad] serie declaree introuvable sur le disque : {d}",
              file=sys.stderr)

    total = sum(b["count"] for b in report)
    if args.json:
        print(json.dumps({
            "schema": 2,
            "mode": "registry",
            "series": report,
            "count": total,
            "violations": [dict(v, series=b["series"])
                           for b in report for v in b["violations"]],
            "missing_dirs": missing,
        }, ensure_ascii=False, indent=1))
    else:
        _emit_text(report)
        print(_summarize(report))

    if missing:
        return 2
    if total:
        print(f"[zero-pad] {total} fichier(s) au chiffre unique dans des "
              f"series declarees -- la convention exige deux chiffres "
              f"(side-track valide : GameTheory-03a).", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
