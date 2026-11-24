#!/usr/bin/env python3
"""Deplace les references d'EPIC hors de l'en-tete d'un carnet (Epic #20250, phase 3).

Le probleme
------------
Le premier paragraphe d'un carnet (et, plus generalement, sa cellule d'en-tete)
annonce le contenu a l'apprenant. L'EPIC #20250 tranche :

    « une mention ponctuelle de provenance ("carnet issu de l'Epic #N"), en pied
    de carnet ou dans une note discrete, jamais dans le premier paragraphe ».

Le carnet doit donc presenter son etat final, sans le vocabulaire de
coordination de l'EPIC qui l'a produit (« EPIC #N, Prong B. »).

La reparation
-------------
Deux gestes mecaniques, sur la **seule** cellule d'en-tete :

1. la **clause de coordination** (« EPIC #1206, Prong B. ») est retiree de
   l'en-tete ; le reste de la phrase (la provenance pedagogique : « Port pyz3
   du notebook C# ... ») est **conserve** ;
2. la reference est deposee en **pied de carnet**, sous forme d'une note
   discrete : ``> Carnet issu de l'EPIC #1206.``

Ce qui n'est PAS touche
-----------------------
- les **cellules de code** et leurs **sorties** : l'operation ne modifie que
  des cellules markdown, donc aucune re-execution C.2 n'est due ;
- la cellule d'en-tete au-dela de la clause retiree : le reste de la cellule
  est byte-identique ;
- les carnets dont l'en-tete ne cite **aucune** EPIC : ils ne sont pas
  candidates.

Invariant de round-trip
-----------------------
Le fichier est reecrit en ``json.dumps(nb, ensure_ascii=False, indent=1)`` (+ la
convention de fin de ligne du fichier d'origine). Le script **refuse d'ecrire**
si le round-trip d'un carnet **non modifie** n'est pas byte-identique a
l'octet : un carnet non canonique ne doit pas subir de churn.

Usage
-----
    python scripts/notebook_tools/fix_epic_refs.py --scan  <notebook|dir>
    python scripts/notebook_tools/fix_epic_refs.py --apply <notebook|dir>

``--scan`` mesure (classe de defaut) et n'ecrit rien ; ``--apply`` repare.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

# La clause de coordination retiree de l'en-tete.
#
# Forme canonique mesuree (serie SMT/Z3-API, 4 carnets) :
#     « ... . EPIC #1206, Prong B. »
#     « ... . EPIC #1206, Prong B. (La section B7 Rational du C#, ...) »
#
# Le motif retient la reference d'EPIC **et** le vocabulaire de revue qui la
# suit dans la meme phrase (« Prong A/B »), qui n'a pas sa place dans un carnet
# presente a l'apprenant. Il ne retient PAS la reference elle-meme : elle est
# re-deposee en pied de carnet.
#
# La frontiere est volontairement etroite : une reference d'EPIC **hors** des
# formes ci-dessous (autre casse, « issue #N », « PR #N ») n'est pas traitee
# par cet outil — la phase 3 de l'EPIC #20250 les laisse au triage manuel.
_EPIC_CORE = r"EPIC\s*#\d+(?:[ \t]*,[ \t]*Prong[ \t]+[A-Z]\.)?"

EPIC_CLAUSE_RE = re.compile(
    # branche 1 : un groupe parenthese dont le contenu est **exactement** la
    # clause (« (epic #4960) ») -- le retrait emporte alors les parentheses,
    # donc il ne laisse pas de parenthese vide derriere lui.
    r"\([ \t]*" + _EPIC_CORE + r"[ \t]*\)"
    # branche 2 : la clause nue, eventuellement precedee de son elision
    # (« l'EPIC #1206 ») et suivie de son point final.
    r"|[ \t]*(?:[A-Za-z]'[ \t]*)?" + _EPIC_CORE + r"\.?",
    re.IGNORECASE,
)

# Le vocabulaire de revue adjoint, separe de la reference par une virgule et
# demarrant une phrase (donc precedee d'un point).
PRONG_RE = re.compile(r"(?<=[\s.!?])Prong\s+[A-Z]\.?(?=\s|$|[),.])", re.IGNORECASE)

# Les reliquats de ponctuation qu'un retrait de clause pourrait laisser
# derriere lui. Le controle est **local** (fenetre autour de la couture) : un
# carnet peut contenir des `..` legitimes (`{0..9}`, `1.4142...`,
# `../Z3-Linq2Z3`), qui ne sont pas des residus de retrait. On controle donc
# deux espaces consecutifs et une ponctuation precedee d'un espace, plus la
# paire de caracteres a la couture meme.
SEAM_RESIDUE_RE = re.compile(
    r"[ \t]{2,}"
    r"|[ \t]+[,;:]"
    r"|\(\s*[,;:]"          # parenthese vide, suite a une clause retiree
    r"|[,;]\s*[)]"          # virgule fermant une parenthese
    r"|[A-Za-z]'[ ,;:.]"    # elision danglingue (« l'EPIC #N » -> « l', »)
    r"|\.\s+\."             # points separes
)
SEAM_WINDOW = 40
SEAM_BAD_PAIRS = {(".", "."), (",", ","), (";", ";")}

# La note de pied de carnet deposee par l'organe.
FOOTER_TEMPLATE = "> Carnet issu de l'EPIC #{ref}."

# Le separateur qui precede la note de pied. La forme `***` est celle du
# depot : le hook pre-commit `fix-hr-separator` convertit toute ligne `---`
# d'un carnet (ouvreur de bloc YAML) en `***`, et la forme emise ici est donc
# deja celle qu'atteindrait le hook -- l'ecriture est donc idempotente.
FOOTER_SEPARATOR = "***"


def _iter_notebooks(target: Path):
    if target.is_dir():
        yield from sorted(target.rglob("*.ipynb"))
    elif target.suffix == ".ipynb":
        yield target
    else:
        raise SystemExit(f"cible illisible : {target}")


def _header_index(cells: list[dict]) -> int | None:
    """Index de la cellule d'en-tete : la premiere cellule markdown.

    Un carnet commence par une cellule markdown d'en-tete (titre, navigation,
    provenance). Le carnet commence autrement (cellule de code, ou pas de
    cellule markdown du tout) n'est pas candidat.
    """
    for i, cell in enumerate(cells):
        if cell.get("cell_type") == "markdown":
            return i
    return None


def _last_markdown_index(cells: list[dict]) -> int | None:
    for i in range(len(cells) - 1, -1, -1):
        if cells[i].get("cell_type") == "markdown":
            return i
    return None


def _source_text(cell: dict) -> str:
    src = cell.get("source", [])
    return src if isinstance(src, str) else "".join(src)


def _set_source_text(cell: dict, text: str) -> None:
    """Ecrit la source en conservant la forme d'origine (chaine ou liste)."""
    if isinstance(cell.get("source"), str):
        cell["source"] = text
        return
    lines = text.splitlines(keepends=True)
    cell["source"] = lines


def _serialise(nb: dict, trailing_newline: bool) -> bytes:
    out = json.dumps(nb, ensure_ascii=False, indent=1)
    if trailing_newline:
        out += "\n"
    return out.encode("utf-8")


def _clean_seam(text: str, pos: int) -> tuple[str, int]:
    """Nettoie la couture locale du retrait.

    Trois residus mecaniques, tous produits par le retrait lui-meme :

    - l'espace qui precedait la clause et qui se retrouve devant une virgule
      (« `fallacy_rules.py` (epic #4960), » -> « `fallacy_rules.py`, ») ;
    - l'espace qui suivait la clause et qui se retrouve apres une parenthese
      ouvrante (« (Epic #2137 Phase 2 » -> « (Phase 2 ») ;
    - le double espace.

    Le nettoyage est **local** (deux caracteres de part et d'autre de la
    coupe) : le reste de la cellule reste byte-identique.
    """
    for _ in range(4):
        before = text[pos - 1: pos]
        after = text[pos: pos + 1]
        if after == " " and before in "(,":
            text = text[:pos] + text[pos + 1:]
            continue
        if before == " " and after in ",;:)":
            text = text[: pos - 1] + text[pos:]
            pos -= 1
            continue
        if before == " " and after == " ":
            text = text[:pos] + text[pos + 1:]
            continue
        break
    return text, pos


def _strip_clause(text: str) -> tuple[str, list[str]] | None:
    """Retire la clause de coordination d'un fragment de source.

    Renvoie ``(nouveau fragment, numeros d'EPIC retires)`` ou ``None`` si le
    fragment ne contient aucune clause. Le retrait est **chirurgical** : seuls
    les spans de la clause sont effaces, plus les trois residus mecaniques de
    la couture (voir ``_clean_seam``). Si le retrait laisse un residu de
    ponctuation, la fonction **refuse** plutot que de retoucher le fragment --
    l'appelant ecrit alors la correction a la main.
    """
    matches = list(EPIC_CLAUSE_RE.finditer(text))
    if not matches:
        return None
    refs = [m.group(0).strip() for m in matches]
    numbers = re.findall(r"EPIC\s*#(\d+)", " ".join(refs), re.IGNORECASE)
    new = text
    for start, end in reversed([m.span() for m in matches]):
        new = new[:start] + new[end:]
        new, start = _clean_seam(new, start)
        if start > 0 and start < len(new) and new[start - 1] == "(" and new[start] == ")":
            raise ValueError("parenthese vide apres retrait -- ecriture refusee")
        window = new[max(0, start - SEAM_WINDOW): start + SEAM_WINDOW]
        if SEAM_RESIDUE_RE.search(window):
            raise ValueError("residu de ponctuation apres retrait -- ecriture refusee")
        seam = new[max(0, start - 1): start + 1]
        if len(seam) == 2 and (seam[0], seam[1]) in SEAM_BAD_PAIRS:
            raise ValueError("ponctuation orpheline a la couture -- ecriture refusee")
    # Le vocabulaire de revue qui suivait la reference sans virgule.
    new = PRONG_RE.sub("", new)
    return new, numbers


def _rewrite_source(source) -> tuple[object, list[str]] | None:
    """Retire la clause de coordination de la source d'une cellule.

    La source d'une cellule Jupyter est une **liste de lignes**. Le retrait
    est fait **element par element** : la structure de la liste est donc
    preservee a l'octet, et le diff ne montre que les lignes touchees (une
    re-serialisation de la liste ferait apparaitre un churn de lignes sans
    changement de texte).

    Une clause qui chevauche deux elements serait la seule maniere de
    modifier la structure : elle est **refusee** (une reference d'EPIC
    residuelle dans la cellule trahit ce cas).
    """
    if isinstance(source, str):
        elements = [source]
        is_list = False
    else:
        elements = list(source)
        is_list = True
    joined_before = "".join(elements)
    balance_before = joined_before.count("(") - joined_before.count(")")
    numbers: list[str] = []
    changed = False
    for i, elem in enumerate(elements):
        if not isinstance(elem, str):
            raise ValueError("source non textuelle -- ecriture refusee")
        out = _strip_clause(elem)
        if out is None:
            continue
        elements[i], nums = out
        numbers.extend(nums)
        changed = True
    if not changed:
        return None
    joined = "".join(elements)
    if re.search(r"EPIC\s*#\d+", joined, re.IGNORECASE):
        raise ValueError(
            "reference d'EPIC a cheval sur deux elements de la source -- ecriture refusee"
        )
    # Le retrait ne doit pas desequilibrer les parentheses de la cellule :
    # une parenthese qui dispara sans son pendant signale une forme que
    # l'outil ne sait pas traiter. (La parenthese vide, elle, est detectee
    # **a la couture** par `_strip_clause` -- un « () » legitime du texte
    # d'origine, comme un appel `Solver()`, ne doit pas bloquer.)
    if joined.count("(") - joined.count(")") != balance_before:
        raise ValueError("parentheses non equilibrees apres retrait -- ecriture refusee")
    return (elements if is_list else elements[0]), numbers


def _footer_note(numbers: list[str]) -> str:
    refs = ", ".join(f"#{n}" for n in dict.fromkeys(numbers))
    return f"> Carnet issu de l'EPIC {refs}."


def _append_footer(text: str, note: str) -> str:
    base = text.rstrip()
    return f"{base}\n\n{FOOTER_SEPARATOR}\n\n{note}\n"


def _plan(path: Path) -> dict:
    """Predicat d'eligibilite UNIQUE, partage par le scan et l'application.

    Le scan et l'application doivent repondre de la MEME chose sur un carnet
    donne : sinon le decompte « avant/apres » d'une fournee ne vaut rien (un
    carnet compte « repariable » par le scan mais refuse a l'ecriture). Les
    deux formes mesurees de cette derive :

    - un carnet **non canonique** (round-trip non byte-identique) : le scan
      voyait la reference et n'enregistrait aucun refus, l'application
      repondait « round-trip non byte-identique » ;
    - une reference **citee mais non retirable** (reference a cheval sur deux
      elements de la source) : le scan la voyait, l'application repondait
      « aucune reference d'EPIC en en-tete ».

    L'ordre des controles est donc fixe, et le motif de refus est rendu tel
    quel par les deux portes :

    1. pas de cellule markdown d'en-tete -> rien a citer ;
    2. round-trip non byte-identique -> carnet non canonique, refuse ;
    3. le retrait echoue (residu de ponctuation, parenthese desequilibree) ;
    4. une reference est citee mais aucune clause n'est retirable ;
    5. pas de cellule markdown distincte pour le pied de carnet ;
    6. la note de pied est deja presente.
    """
    raw = path.read_bytes()
    nb = json.loads(raw.decode("utf-8"))
    cells = nb.get("cells", [])
    hidx = _header_index(cells)
    trailing = raw.endswith(b"\n")
    plan = {
        "path": path,
        "nb": nb,
        "cells": cells,
        "header_index": hidx,
        "canonical": False,
        "trailing_newline": trailing,
        "refs": [],
        "removable": [],
        "refused": None,
        "new_header": None,
        "footer_index": None,
        "footer": None,
    }
    if hidx is None:
        plan["refused"] = "sans cellule markdown d'en-tete"
        return plan
    plan["canonical"] = _serialise(nb, trailing) == raw
    header_text = _source_text(cells[hidx])
    plan["refs"] = re.findall(r"EPIC\s*#(\d+)", header_text, re.IGNORECASE)
    if not plan["canonical"]:
        plan["refused"] = ("round-trip non byte-identique (carnet non canonique) "
                           "-- ecriture refusee")
        return plan
    try:
        result = _rewrite_source(cells[hidx].get("source"))
    except ValueError as exc:
        plan["refused"] = f"refus : {exc}"
        return plan
    if not result:
        if plan["refs"]:
            plan["refused"] = ("reference d'EPIC citee mais clause non couverte "
                               "(reference a cheval sur deux elements de la source) "
                               "-- ecriture refusee")
        return plan
    plan["new_header"], plan["removable"] = result[0], result[1]
    # Les controles de DESTINATION sont ici, et non dans `apply_one` : c'est
    # ce qui rend le predicat unique. Mesure du 2026-11-09 (adjoint, PR #25405)
    # : `apply_one` gardait deux refus absents du scan -- une seule cellule
    # markdown, note de pied deja presente -- donc le scan annoncait
    # « repariable » la ou l'application refusait d'ecrire. Le decompte
    # « avant/apres » d'une fournee ne voulait alors rien dire.
    lidx = _last_markdown_index(cells)
    if lidx is None:
        plan["refused"] = "aucune cellule markdown pour le pied de carnet"
        return plan
    if lidx == hidx:
        plan["refused"] = "une seule cellule markdown (pas de pied distinct) -- ecriture refusee"
        return plan
    footer = _footer_note(plan["removable"])
    if footer in _source_text(cells[lidx]):
        plan["refused"] = "note de pied deja presente -- ecriture refusee"
        return plan
    plan["footer_index"] = lidx
    plan["footer"] = footer
    return plan


def analyse(path: Path) -> dict:
    """Mesure le defaut sur un carnet sans ecrire."""
    plan = _plan(path)
    info = {
        "path": path,
        "header_index": plan["header_index"],
        "refs": plan["refs"],
        "removable": plan["removable"],
        "refused": plan["refused"],
        "canonical": plan["canonical"],
        "trailing_newline": plan["trailing_newline"],
    }
    if plan["new_header"] is not None:
        info["new_header"] = plan["new_header"]
    return info


def apply_one(path: Path, dry_run: bool) -> str:
    plan = _plan(path)
    if plan["refused"]:
        return plan["refused"]
    if plan["new_header"] is None:
        return "aucune reference d'EPIC en en-tete"
    new_header, numbers = plan["new_header"], plan["removable"]
    cells = plan["cells"]
    hidx = plan["header_index"]
    lidx = plan["footer_index"]
    footer = plan["footer"]
    if not dry_run:
        cells[hidx]["source"] = new_header
        _set_source_text(cells[lidx], _append_footer(_source_text(cells[lidx]), footer))
        path.write_bytes(_serialise(plan["nb"], plan["trailing_newline"]))
    return f"en-tete nettoye ({', '.join('#' + n for n in numbers)}) -> pied de carnet"


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group(required=True)
    group.add_argument("--scan", action="store_true", help="mesurer, n'ecrire rien")
    group.add_argument("--apply", action="store_true", help="reparer")
    parser.add_argument("target", help="carnet ou repertoire")
    args = parser.parse_args(argv)

    root = Path(args.target)
    candidates = 0
    refused = 0
    for path in _iter_notebooks(root):
        info = analyse(path)
        # Un carnet qui ne cite aucune EPIC n'est ni candidat ni refuse : le
        # decompte annonce « carnets cites mais formes non couvertes ». Le
        # refus « sans cellule markdown d'en-tete » n'entre donc pas la.
        if not info["refs"]:
            continue
        if args.scan:
            if info["refused"]:
                refused += 1
                print(f"{path} : REFUS ({info['refused']})")
            else:
                candidates += 1
                print(f"{path} : en-tete cite {', '.join('#' + n for n in info['refs'])}")
        else:
            outcome = apply_one(path, dry_run=False)
            print(f"{path} : {outcome}")
    if args.scan:
        print(f"\ncarnets dont l'en-tete cite une EPIC, repairables : {candidates}")
        print(f"carnets cites mais formes non couvertes (refuses) : {refused}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
