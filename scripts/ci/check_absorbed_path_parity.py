#!/usr/bin/env python3
"""Parite de couverture : les `paths` du registre COUVRENT le declencheur retire.

Programme #12567 (absorption des gardes unitaires dans la voie rapide). Absorber
un garde retire son declencheur `pull_request` du workflow d'origine. Le garde
n'est alors plus selectionne QUE par les `paths` du registre : la voie rapide
**remplace** le workflow, elle ne s'y ajoute pas. Un motif perdu fait donc
cesser le garde en silence sur ce chemin -- le CI devient plus vert, jamais
plus rouge, et rien ne le signale.

Mesure fondatrice (#20166, 2026-10-09) : deux des neuf gardes du lot PILOTE
avaient perdu des motifs au retrait du declencheur. `pip-leak-guard` ne portait
plus que `**/*.ipynb` alors que son declencheur couvrait aussi son detecteur
(`audit_pip_install_cells.py`) et deux outils (`pip_leak_delta.py`) -- et il n'a
**aucun** declencheur `push` de rattrapage, donc une PR ne touchant que le
detecteur n'allumait plus le garde du tout. `readme-ipynb-links-guard` perdait
de meme son fixeur et deux fichiers de tests, un seul etant rattrape.

La reference est la version du workflow sur la BRANCHE DE BASE : au moment du
merge d'une tranche, elle porte encore le declencheur alors que la tete de PR ne
l'a plus. Un workflow dont la base n'a deja plus de `pull_request` est un etat
deja consolide -- rien a comparer, et surtout aucune conclusion a en tirer.

Deux facons d'etre couvert, et deux seulement :

  1. un motif du registre couvre le motif du declencheur ;
  2. un declencheur **residuel** du workflow de base (`push`, `schedule`)
     couvre le meme chemin -- la couverture est alors deplacee, pas perdue.

La couverture se juge sur une forme NORMALISEE (segment `**/` retire en tete,
`/**/` reduit a `/`) : c'est exactement le dialecte que le matcher de la voie
rapide neutralise lui-meme (`fast_lane.py::path_matches`), et le depot n'a aucun
notebook a sa racine. Un motif a joker cherche un homologue normalise ; un motif
**litteral** (sans joker) doit etre present tel quel -- c'est precisement la
classe que la mesure du 2026-10-09 a vue disparaitre.

Fail-closed : un motif dont la couverture n'est pas prouvee est un finding. Le
cout d'un faux rouge est une ligne a ajouter au registre ; le cout d'un faux
vert est un garde eteint en silence, que personne ne rallumera.

Usage:
    python check_absorbed_path_parity.py [--base origin/main] [--json]
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
_CI_DIR = Path(__file__).resolve().parent
if str(_CI_DIR) not in sys.path:
    sys.path.insert(0, str(_CI_DIR))

import fast_lane_registry as reg  # noqa: E402
from check_unique_check_run_names import _parse_workflow, _load_yaml  # noqa: E402
from fast_lane_registry import Guard, FAST_LANE_NATIVE  # noqa: E402

WORKFLOW_PREFIX = ".github/workflows/"
# Declencheurs qui, s'ils subsistent sur la base, peuvent porter la couverture
# perdue par le retrait du `pull_request`.
RESIDUAL_EVENTS = ("push", "schedule", "workflow_dispatch")


def all_guards():
    """Tout `Guard` du registre, decouvert dynamiquement (#19171, TRANCHE17).

    On enumere `vars(registry)` et on garde chaque liste dont chaque item est un
    `Guard`. Une liste ajoutee ulterieurement est couverte d'office ; une liste
    retiree cesse de l'etre.
    """
    seen = set()
    for value in vars(reg).values():
        if isinstance(value, list) and value and all(
                isinstance(item, Guard) for item in value):
            for guard in value:
                if id(guard) not in seen:
                    seen.add(id(guard))
                    yield guard


def _git_show(base: str, path: str) -> str | None:
    """Contenu d'un fichier sur la branche de base (None = illisible/absent)."""
    result = subprocess.run(
        ["git", "show", f"{base}:{path}"],
        cwd=ROOT, capture_output=True, text=True,
        encoding="utf-8", errors="replace",
    )
    return result.stdout if result.returncode == 0 else None


def _normalize(pattern: str) -> str:
    """Forme comparable : dialecte `**/` neutralise (cf `fast_lane.py`).

    Le depot ecrit le meme motif de deux facons : `**.ipynb` et `**/*.ipynb`.
    La voie rapide les traite identiquement (`path_matches` neutralise lui-meme
    le prefixe `**/`), donc l'organe doit les traiter identiquement aussi --
    sinon il fabrique un faux rouge sur chaque garde qui ecrit l'une quand le
    registre ecrit l'autre.
    """
    text = pattern.replace("\\", "/").strip()
    while text.startswith("**/"):
        text = text[3:]
    if text.startswith("**"):
        text = "*" + text[2:]
    return text.replace("/**/", "/")


def _has_wildcard(pattern: str) -> bool:
    return any(ch in pattern for ch in "*?[")


def covered_by(pattern: str, candidates: list[str]) -> str | None:
    """Motif du registre couvrant `pattern`, ou None.

    Egalite modulo dialecte, ou -- pour un motif litteral -- un motif du
    registre qui se termine par ce litteral (un sous-arbre couvre son fichier).
    """
    norm = _normalize(pattern)
    for candidate in candidates:
        cand_norm = _normalize(candidate)
        if cand_norm == norm:
            return candidate
        if not _has_wildcard(pattern):
            # un chemin litteral est couvert par une entree litterale
            # superieure, ou par le sous-arbre qui le contient (`a/**`).
            if cand_norm.endswith("/" + norm) or cand_norm == norm:
                return candidate
            if cand_norm.endswith("/**") and norm.startswith(cand_norm[:-2]):
                return candidate
        # Un motif repo-wide `*.ipynb` matche n'importe quel carnet du depot :
        # il couvre donc un motif de sous-arbre (`Serie/**/*.ipynb`), qui est
        # strictement plus etroit. C'est une subsomption reelle, pas un
        # arrangement de confort -- la verifier ainsi evite un faux rouge sur
        # chaque garde dont le declencheur cible une serie quand le registre
        # couvre le depot entier.
        if cand_norm == "*.ipynb" and norm.endswith(".ipynb"):
            return candidate
    return None


def _event_block(data: dict, event: str):
    """Bloc d'un evenement dans `on:`, ou None s'il est absent."""
    on = data.get("on")
    if on is None:
        on = data.get(True)  # PyYAML lit `on:` nu comme le booleen True
    if isinstance(on, list):
        return {} if event in on else None
    if not isinstance(on, dict):
        return None
    return on.get(event)


def _trigger_paths(block) -> list[str] | None:
    """`paths:` d'un bloc d'evenement.

    None signifie « pas de filtre » -- le declencheur tire sur tous les
    chemins. Un bloc absent est rendu par l'appelant, pas ici.
    """
    if not isinstance(block, dict):
        return None
    paths = block.get("paths")
    if paths is None:
        return None
    if isinstance(paths, list):
        return [str(p) for p in paths]
    return [str(paths)]


def _residual_paths(data: dict) -> list[str] | None:
    """Chemins couverts par un declencheur residuel de la base.

    Retourne None si un declencheur residuel tire sans filtre -- la couverture
    est alors totale, et la perte du `pull_request` est sans consequence.
    """
    collected: list[str] = []
    for event in RESIDUAL_EVENTS:
        block = _event_block(data, event)
        if block is None:
            continue
        paths = _trigger_paths(block)
        if paths is None:
            return None  # declencheur residuel sans filtre : tout est couvert
        collected.extend(paths)
    return collected


def findings(base: str) -> tuple[list[str], list[str], dict]:
    """(problems, skipped, stats)."""
    yaml = _load_yaml()
    if yaml is None:
        return ["INSTRUMENT CASSE: PyYAML indisponible"], [], {"checked": 0}

    problems: list[str] = []
    skipped: list[str] = []
    checked = 0

    for guard in all_guards():
        if guard.source == FAST_LANE_NATIVE or not guard.source:
            continue
        if not guard.source.endswith(".yml"):
            continue
        # Seul un garde ABSORBE a perdu son declencheur. Un garde du registre
        # qui n'est pas absorbe est double par son workflow, lequel declenche
        # toujours sur `pull_request` : rien n'est perdu, et comparer ses
        # `paths` au declencheur produirait un faux rouge sur chaque garde
        # jamais absorbe (mesure : `solution-leak-guard`, non absorbe).
        if not guard.absorbed:
            continue
        rel = WORKFLOW_PREFIX + guard.source
        text = _git_show(base, rel)
        if text is None:
            skipped.append(f"{guard.name!r}: {rel} illisible sur {base}")
            continue
        data = _parse_workflow(text, yaml)
        if data is None:
            skipped.append(f"{guard.name!r}: {rel} non parsable sur {base}")
            continue

        block = _event_block(data, "pull_request")
        if block is None:
            # Etat deja consolide : la base non plus ne declenche plus.
            skipped.append(f"{guard.name!r}: aucun `pull_request` sur {base} "
                           "(deja consolide)")
            continue

        checked += 1
        trigger_paths = _trigger_paths(block)
        if trigger_paths is None:
            # Le declencheur tirait sur TOUS les chemins : le registre doit
            # rester sans filtre pour le reproduire.
            if guard.paths:
                problems.append(
                    f"{guard.name!r}: declencheur `pull_request` sans filtre, "
                    f"mais le registre restreint a {sorted(guard.paths)} -- "
                    "des chemins sont perdus")
            continue

        residual = _residual_paths(data)
        if residual is None:
            continue  # un declencheur residuel non filtre couvre tout

        for path in trigger_paths:
            if covered_by(path, guard.paths):
                continue
            if covered_by(path, residual):
                continue
            problems.append(
                f"{guard.name!r}: motif {path!r} du declencheur n'est couvert "
                f"NI par les `paths` du registre {sorted(guard.paths)} "
                f"NI par un declencheur residuel {sorted(residual)}")

    stats = {"checked": checked, "skipped": len(skipped)}
    return problems, skipped, stats


def _main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--base", default="origin/main",
                        help="branche de reference (defaut: origin/main)")
    parser.add_argument("--json", action="store_true", help="verdict machine")
    parser.add_argument("--verbose", action="store_true",
                        help="detailer les gardes ecartes eux aussi")
    args = parser.parse_args(argv)

    problems, skipped, stats = findings(args.base)

    if args.json:
        print(json.dumps({
            "base": args.base,
            "problems": problems,
            "checked": stats["checked"],
            "skipped": skipped if args.verbose else stats["skipped"],
            "verdict": "PARITY_BROKEN" if problems else "PARITY_OK",
        }, ensure_ascii=False, indent=2))
    else:
        for note in skipped:
            if args.verbose:
                print(f"[absorbed-path-parity] ecarte {note}")
        if problems:
            print(f"[absorbed-path-parity] PARITE ROMPUE -- {len(problems)} "
                  f"motif(s) perdu(s) au retrait du declencheur :")
            for problem in problems:
                print(f"  - {problem}")
            print("  Geste : ajouter le motif manquant aux `paths` du garde "
                  "dans scripts/ci/fast_lane_registry.py.")
        else:
            print(f"[absorbed-path-parity] OK -- {stats['checked']} garde(s) "
                  f"verifie(s) contre {args.base}, "
                  f"{stats['skipped']} ecarte(s) "
                  "(etat deja consolide ou source illisible).")

    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(_main(sys.argv[1:]))
