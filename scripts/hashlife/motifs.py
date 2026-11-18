"""Anatomie declaree des motifs Hashlife -- mesuree, pas affirmee.

#22287 / revue Hermes de #22294. La table `MOTIFS` de `hashlife_speedup.py`
declare une classe anatomique par motif (`periodique-p3`, `immuable`,
`periodique-translatif-p4`, `croissance-reguliere`, `methuselah-chaotique`,
`soupe-chaotique`). Rien ne
confrontait cette declaration a la ligne de base naive : le motif nomme
`pulsar` y a porte **36 cellules** au lieu des 48 canoniques, emis un planeur,
et traverse une revue en etant classe `periodique-p3` avec `alpha_hash = 0,179`.

Le defaut n'est pas l'erreur de saisie, c'est l'**absence d'instrument** : une
anatomie ecrite a la main qui ne se refere a aucune mesure est une affirmation,
et une affirmation fausse se propage dans les verdicts (ici `REDUCIBLE`).

Ce module mesure. Il lit la declaration dans sa source unique
(`hashlife_speedup.MOTIFS`), la confronte au moteur naif, et rend un verdict par
motif. Il ne reimplemente pas l'evolution : `naive_step` vient de la meme source.

Deux precautions de mesure, chacune fermant un faux positif :

- **Le retour doit se repeter.** Un etat qui retombe une fois sur lui-meme par
  coincidence n'est pas periodique : on exige `REPEATS` retours consecutifs.
- **La translation n'est absorbee que si elle est declaree.** Un planeur revient
  *a une translation pres* ; une soupe ne revient pas. Normaliser partout ferait
  passer un objet qui derive pour un oscillateur, donc on normalise uniquement
  les motifs dont la classe l'annonce (`periodique-translatif-pN`).

Ce que l'organe ne couvre pas : il mesure la PERIODE et la croissance, pas
l'identite du motif. Un carre de 2x2 declare `immuable` passe -- et c'est
correct, c'est un bloc. C'est la classe anatomique qui est verifiee, pas le nom.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from hashlife_speedup import MOTIFS, build_motif, naive_step  # noqa: E402

#: Retours consecutifs exiges avant de conclure a une periode.
REPEATS = 2
#: Generations parcourues au plus. Blinker p2 et pulsar p3 sont tres en deca ;
#: une soupe ou un canon ne reviennent pas dans cette fenetre.
BUDGET = 240

_PERIODIC = re.compile(r"periodique(?:-translatif)?-p(\d+)$")
_IMMUABLE = re.compile(r"^immuable$")
#: Classes dont le nom annonce une croissance : la mesure doit la constater.
_GROWTH = re.compile(r"croissance-reguliere|methuselah-chaotique")


def normalize(cells: set[tuple[int, int]]) -> frozenset[tuple[int, int]]:
    """Etat ramene a l'origine -- identite a une translation pres."""
    if not cells:
        return frozenset()
    mx = min(x for x, _ in cells)
    my = min(y for _, y in cells)
    return frozenset((x - mx, y - my) for x, y in cells)


def declared_period(anatomy: str) -> int | None:
    """Periode annoncee par la classe, ou None si la classe annonce l'absence."""
    anatomy = anatomy.strip()
    if _IMMUABLE.match(anatomy):
        return 1
    m = _PERIODIC.match(anatomy)
    return int(m.group(1)) if m else None


def declared_translative(anatomy: str) -> bool:
    return "translatif" in anatomy


def states(cells: set[tuple[int, int]], budget: int = BUDGET) -> list[frozenset]:
    """Les `budget` etats successifs, sous l'identite demandee par l'appelant."""
    out = []
    current = set(cells)
    for _ in range(budget):
        current = naive_step(current)
        out.append(frozenset(current))
    return out


def measure_period(cells: set[tuple[int, int]], translative: bool,
                   budget: int = BUDGET, repeats: int = REPEATS) -> tuple[int | None, int]:
    """Plus petite periode qui se repete `repeats` fois, et le nombre de generations lues.

    `repeats=2` suffit a distinguer un oscillateur d'une coincidence : a la
    generation g on exige `norm(g) == norm(g+p)` **et** `norm(g+p) == norm(g+2p)`.
    """
    seen = [normalize(c) for c in states(cells, budget)] if translative else states(cells, budget)
    for p in range(1, budget // (repeats + 1) + 1):
        for g in range(len(seen) - p * repeats):
            if all(seen[g + k * p] == seen[g + (k + 1) * p] for k in range(repeats)):
                return p, g + p * repeats + 1
    return None, budget


def bbox_growth(cells: set[tuple[int, int]], budget: int = BUDGET) -> tuple[int, int, int]:
    """(etendue initiale, etendue finale, population finale) -- la signature d'un emetteur.

    L'etendue est largeur + hauteur de la boite englobante : un oscillateur la
    garde, un emetteur l'etend.
    """
    current = set(cells)
    first = _bbox(current)
    for _ in range(budget):
        current = naive_step(current)
    return first, _bbox(current), len(current)


def _bbox(cells: set[tuple[int, int]]) -> int:
    """Etendue de la boite englobante : (largeur + hauteur), pas une largeur seule."""
    if not cells:
        return 0
    xs = [x for x, _ in cells]
    ys = [y for _, y in cells]
    return max(xs) - min(xs) + 1 + max(ys) - min(ys) + 1


def audit(name: str) -> dict:
    """Confronte la classe declaree d'un motif a ce que la ligne naive mesure."""
    anatomy = MOTIFS[name][1]
    cells = build_motif(name)
    want = declared_period(anatomy)
    translative = declared_translative(anatomy)
    got, read = measure_period(cells, translative)
    span0, spanN, popN = bbox_growth(cells)

    if want is None:
        # La classe annonce une absence de periode : un motif qui revient la contredit.
        ok = got is None
        detail = "non periodique attendu"
    else:
        ok = got == want
        detail = "periode {} attendue".format(want)

    if ok and _GROWTH.match(anatomy):
        # Le nom de la classe annonce une croissance : la mesure doit la constater,
        # sinon la troisieme classe declaree ne serait pas plus mesuree qu'affirmee.
        ok = spanN > span0
        detail = "croissance annoncee : etendue {} -> {}".format(span0, spanN)

    return {
        "motif": name,
        "anatomy": anatomy,
        "declared_period": want,
        "measured_period": got,
        "translative": translative,
        "cells": len(cells),
        "generations_read": read,
        "bbox_span_initial": span0,
        "bbox_span_final": spanN,
        "population_final": popN,
        "ok": ok,
        "detail": detail,
    }


def audit_all(names: list[str] | None = None) -> list[dict]:
    return [audit(n) for n in (names or sorted(MOTIFS))]


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description="Mesure l'anatomie declaree des motifs Hashlife.")
    ap.add_argument("--motif", action="append", dest="motifs")
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--check", action="store_true", help="exit 1 si une declaration est contredite")
    args = ap.parse_args(argv)

    rows = audit_all(args.motifs)
    if args.json:
        print(json.dumps(rows, indent=2, ensure_ascii=False))
    else:
        for r in rows:
            verdict = "ok" if r["ok"] else "CONTREDIT"
            print("{:<14} {:<28} declare={!s:<5} mesure={!s:<5} {}  ({} cellules, etendue {}->{})".format(
                r["motif"], r["anatomy"], r["declared_period"], r["measured_period"],
                verdict, r["cells"], r["bbox_span_initial"], r["bbox_span_final"]))

    bad = [r for r in rows if not r["ok"]]
    if args.check and bad:
        for r in bad:
            print("CONTREDIT: {} -- {}, mesure {}".format(
                r["motif"], r["detail"], r["measured_period"]), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
