#!/usr/bin/env python3
"""Sonde d'outil du Pli 5 Grain A — mesure `setreplace-py` et produit le JSON.

Ce script est le GENERATEUR de `setreplace_probe_results.json` : le JSON n'est
jamais ecrit a la main, il est la sortie de ce programme (meme contrat que
`causal_structure.py` -> `causal_structure_results.json`).

Ce qu'il mesure, et qui fonde le verdict SOTA-OK du carnet :

- l'evolution hypergraphe de la regle canonique du Wolfram Physics Project,
  bornee a 1 500 evenements / 12 generations, avec le nombre d'aretes et
  d'atomes finaux, le motif de terminaison et une empreinte de l'etat final ;
- le graphe causal natif (`causal_graph_edges()`), qui est la seule surface
  multiway exposee par la bibliotheque ;
- la canonicalisation des variables par `str(Rule.parse(...))` ;
- la surface d'API reellement exportee (ce que la couche maison doit
  reimplementer, et ce qu'elle n'a pas a reimplementer) ;
- la presence ou l'absence d'un noyau Wolfram sur le siege, et l'etat des
  branches concurrentes (hypernetx, setreplace).

Determinisme : deux evolutions independantes sont jouees et leurs empreintes
comparees. Le seul champ qui varie d'une execution a l'autre est `wall_s`.

Usage :
    python scripts/hashlife/setreplace_probe.py [--out <chemin.json>]

Dependance : `setreplace==0.2.0` (wheel abi3, Python 3.13 sur le siege po-2024).
"""

from __future__ import annotations

import argparse
import hashlib
import json
import platform
import shutil
import socket
import subprocess
import sys
import time
from pathlib import Path

# Regle de l'annonce du Wolfram Physics Project : c'est l'exemple canonique de
# la documentation setreplace-py, et celui que la couche multiway maison doit
# reproduire evenement par evenement.
RULE_TEXT = "{{x, y}, {x, z}} -> {{x, z}, {x, w}, {y, w}, {z, w}}"

# Etat initial : triangle {1,2},{1,3},{2,3} plus une arete pendante {3,4}.
# Quatre aretes, quatre atomes — c'est la forme que le JSON de reference
# reproduit (final_atoms = 1504). L'etat initial est desormais CONSIGNE dans le
# JSON (`evolve.initial_state`) : sans lui, la mesure n'etait pas rejouable.
INITIAL_STATE = [[1, 2], [1, 3], [2, 3], [3, 4]]

MAX_EVENTS = 1500
MAX_GENERATIONS = 12

# Bornes de la detection du noyau Wolfram : un `which` qui traine ne doit pas
# retenir la sonde.
WHICH_TIMEOUT_S = 20


def _canonical_state(state) -> list[tuple[int, ...]]:
    """Forme canonique de l'etat : aretes triees, puis liste triee.

    L'ordre de restitution de la bibliotheque n'est pas un contrat ; la forme
    canonique, elle, en est un — c'est elle qui rend l'empreinte comparable
    d'une execution a l'autre.
    """
    return sorted(tuple(sorted(int(a) for a in edge)) for edge in state)


def _state_sha16(state) -> str:
    """Empreinte courte de l'etat canonique (16 premiers hex de sha256)."""
    payload = json.dumps(_canonical_state(state), separators=(",", ":"))
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()[:16]


def _evolve(sr):
    """Joue l'evolution bornee et rend (systeme, duree murale)."""
    system = sr.HypergraphSystem(sr.Rule.parse(RULE_TEXT), INITIAL_STATE)
    started = time.perf_counter()
    system.evolve(max_events=MAX_EVENTS, max_generations=MAX_GENERATIONS)
    return system, time.perf_counter() - started


def _probe_wolfram_kernels() -> tuple[str, str]:
    """Sonde les deux branches du noyau Wolfram : siege Windows, puis WSL Ubuntu.

    Rend `(windows, wsl_ubuntu)`, chacun etant le chemin trouve ou le motif de
    l'absence. Les deux branches sont consignees separement : un noyau present
    d'un cote seulement change le verdict d'outil.
    """
    local = shutil.which("wolframscript")
    windows = local or "absent (which wolframscript -> rc 2)"
    try:
        probe = subprocess.run(
            ["wsl", "-d", "Ubuntu", "-u", "root", "--", "which", "wolframscript"],
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=WHICH_TIMEOUT_S,
        )
        path = probe.stdout.strip()
        wsl = path if probe.returncode == 0 and path else "absent (wolframscript introuvable dans le WSL Ubuntu)"
    except (OSError, subprocess.TimeoutExpired) as exc:
        wsl = f"absent (sonde WSL inexploitable : {type(exc).__name__})"
    return windows, wsl


def build_report(sr, seat: str) -> dict:
    """Construit le rapport complet a partir de mesures fraiches."""
    system, wall_s = _evolve(sr)

    final_state = [list(edge) for edge in system.final_state]
    atoms = {int(atom) for edge in final_state for atom in edge}
    sha = _state_sha16(final_state)

    # Determinisme : seconde evolution independante, meme empreinte attendue.
    system_b, _ = _evolve(sr)
    sha_b = _state_sha16([list(edge) for edge in system_b.final_state])

    causal_edges = [list(pair) for pair in system.causal_graph_edges()]

    parsed_str = str(sr.Rule.parse(RULE_TEXT))
    reparse_roundtrip = str(sr.Rule.parse(parsed_str)) == parsed_str

    api_surface = sorted(name for name in dir(sr) if not name.startswith("_"))

    # Le multiway est mesure par ABSENCE dans la surface exportee : la
    # bibliotheque ne publie aucun symbole multiway, et `evolve()` ne prend
    # aucun kwarg de branchement. Les deux citations documentaires viennent de
    # la distribution publiee (le wheel n'embarque pas sa documentation) : elles
    # sont declarees comme telles, jamais presentees comme relues ici.
    multiway_symbols = [name for name in api_surface if "multiway" in name.lower()]
    declare = [
        "README.md l.154 : 'Not yet: multiway systems and branchial'",
        "docs/python-api.md l.238 : 'Later, when multiway lands in the engine, evolve() gains kwargs'",
        "surface API : replace_once() deterministe par event_ordering, aucune enumeration des matchs exposee",
    ]
    if multiway_symbols:
        declare.append(f"symboles multiway exportes : {', '.join(multiway_symbols)}")

    wolfram_windows, wolfram_wsl = _probe_wolfram_kernels()

    return {
        "package": "setreplace",
        "version": getattr(sr, "__version__", "inconnue"),
        "probe": "pli5-grainA-outil",
        "date": time.strftime("%Y-%m-%d"),
        "seat": seat,
        "evolve": {
            "rule": RULE_TEXT,
            "rule_origin": "regle de l'annonce du Wolfram Physics Project (exemple canonique de la doc setreplace-py)",
            "initial_edges": len(INITIAL_STATE),
            "initial_state": INITIAL_STATE,
            "events": system.events_count,
            "generations": system.generations_count,
            "final_edges": len(final_state),
            "final_atoms": len(atoms),
            "termination_reason": system.termination_reason,
            "wall_s": round(wall_s, 2),
            "final_state_sha256_16": sha,
        },
        "causal_graph": {
            "edges": len(causal_edges),
            "sample": causal_edges[:5],
        },
        "determinism_same_seed": sha == sha_b,
        "rule_str_canonicalizes": {
            "str_of_parse": parsed_str,
            "reparse_roundtrip": reparse_roundtrip,
            "note": "str() renomme les variables en x1..xn (forme canonique), pas une casse",
        },
        "api_surface": api_surface,
        "multiway_support": {
            "exposed": bool(multiway_symbols),
            "evidence": declare,
        },
        "branches": {
            "wolfram_kernel_windows": wolfram_windows,
            "wolfram_kernel_wsl_ubuntu": wolfram_wsl,
            "hypernetx_2_4_3": "hypergraphes statiques (incidence, dessin), aucune reecriture -- mesure sur la description PyPI",
            "setreplace_py": "installe et invoque (ce JSON est sa vraie sortie, reformatee en JSON par le script de sonde)",
        },
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--out",
        default=str(Path(__file__).with_name("setreplace_probe_results.json")),
        help="chemin du JSON a ecrire",
    )
    parser.add_argument(
        "--seat",
        default=f"{socket.gethostname()} ({platform.system()}, python "
        f"{sys.version_info.major}.{sys.version_info.minor}, wheel abi3)",
        help="libelle du siege consigne dans le rapport",
    )
    args = parser.parse_args(argv)

    try:
        import setreplace as sr
    except ImportError:
        print("setreplace absent : installer setreplace==0.2.0", file=sys.stderr)
        return 2

    report = build_report(sr, args.seat)
    out = Path(args.out)
    out.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(
        f"ecrit {out} — {report['evolve']['final_edges']} aretes, "
        f"{report['evolve']['events']} evenements, sha {report['evolve']['final_state_sha256_16']}, "
        f"determinisme={report['determinism_same_seed']}",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())