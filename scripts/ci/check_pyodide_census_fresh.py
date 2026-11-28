#!/usr/bin/env python3
"""Garde de fraicheur du census Pyodide (issue #27617).

Le rapport ``docs/reference/pyodide-eligibilite.md`` et son fichier de refus
``docs/reference/pyodide-refus.tsv`` portent l'en-tete « genere par ... ne pas
editer a la main », mais rien ne verifiait qu'ils etaient encore a jour : la
prochaine evolution de ``main`` les ferait deriver en silence -- exactement le
motif que #2651 combat pour le catalogue.

La regeneration est **hors reseau et deterministe** depuis #27583 : le lock
Pyodide et le cache des sondes PyPI sont commites, donc l'organe rejoue la
regeneration dans un repertoire temporaire et compare les sorties aux fichiers
commites. Un ecart -> exit 1.

L'organe ne modifie rien du depot : il ecrit dans un temporaire et compare.

Usage :

    python scripts/ci/check_pyodide_census_fresh.py
    python scripts/ci/check_pyodide_census_fresh.py --json
    python scripts/ci/check_pyodide_census_fresh.py --base origin/main

**Attribution (#28841).** Une derive n'est imputable a la PR que si la PR a
touche une entree du census -- un carnet, le generateur, le lock, le cache, ou
les deux fichiers du census eux-memes. Sans `--base`, l'organe garde son
verdict absolu (fail-closed). Avec `--base`, une derive que la PR n'a pas
causee passe en avertissement : elle appartient a `main`, et le geste de
regeneration est nomme au lieu d'etre exige de la PR. La mecanique et ses
bornes : `scripts/ci/freshness_attribution.py`.
"""
from __future__ import annotations

import argparse
import difflib
import json
import subprocess
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from freshness_attribution import attribuer, fichiers_propres, message  # noqa: E402

REPO_ROOT = Path(__file__).resolve().parents[2]

GENERATEUR = Path("scripts") / "notebook_tools" / "pyodide_eligibility.py"
RAPPORT = Path("docs") / "reference" / "pyodide-eligibilite.md"
REFUS = Path("docs") / "reference" / "pyodide-refus.tsv"
LOCK = Path("docs") / "reference" / "pyodide-lock.json"
CACHE = Path("docs") / "reference" / "pyodide-wheel-cache.json"

# Entrees du census : ce dont le generateur derive son contenu, plus la page
# elle-meme (une page reecrite a la main est un geste de la PR, pas un retard
# de la base).
MOTIFS_ENTREE: tuple[str, ...] = (
    "*.ipynb",
    str(GENERATEUR).replace("\\", "/"),
    str(RAPPORT).replace("\\", "/"),
    str(REFUS).replace("\\", "/"),
    str(LOCK).replace("\\", "/"),
    str(CACHE).replace("\\", "/"),
)

GESTE = ("python scripts/notebook_tools/pyodide_eligibility.py --format md "
         "--out docs/reference/pyodide-eligibilite.md "
         "--refus-out docs/reference/pyodide-refus.tsv "
         "--pyodide-lock docs/reference/pyodide-lock.json "
         "--wheel-cache docs/reference/pyodide-wheel-cache.json")



def regenerer(repo: Path, cible: Path) -> tuple[int, str]:
    """Rejoue la generation hors reseau dans ``cible`` (un temporaire).

    Les artefacts de reference (lock, cache des sondes) sont passes
    explicitement : la regeneration ne doit toucher ni au reseau ni au lock
    d'un depot.
    """
    cmd = [
        sys.executable,
        str(repo / GENERATEUR),
        "--format", "md",
        "--out", str(cible / RAPPORT.name),
        "--refus-out", str(cible / REFUS.name),
        "--pyodide-lock", str(repo / LOCK),
        "--wheel-cache", str(repo / CACHE),
    ]
    resultat = subprocess.run(cmd, capture_output=True, text=True, encoding="utf-8",
                               errors="replace", cwd=str(repo))
    return resultat.returncode, (resultat.stderr or "")[-2000:]


def comparer(commite: Path, regenere: Path) -> list[str]:
    """Lignes de diff entre le fichier commite et le fichier regenere."""
    if not regenere.exists():
        return [f"{regenere.name} : le generateur n'a rien produit"]
    a = commite.read_text(encoding="utf-8", errors="replace").splitlines()
    b = regenere.read_text(encoding="utf-8", errors="replace").splitlines()
    return list(difflib.unified_diff(a, b, fromfile=f"commite/{commite.name}",
                                     tofile=f"regenere/{regenere.name}", lineterm=""))


def verifier(repo: Path) -> dict:
    """Verdict : les artefacts commites sont-ils ceux que la regeneration produit ?"""
    manquants = [str(p) for p in (LOCK, CACHE, RAPPORT, REFUS)
                 if not (repo / p).exists()]
    if manquants:
        return {"ok": False, "ecarts": [f"fichier manquant : {p}" for p in manquants],
                "regeneration_rc": None, "sortie": ""}
    with tempfile.TemporaryDirectory(prefix="pyodide-census-") as tmp:
        cible = Path(tmp)
        rc, sortie = regenerer(repo, cible)
        ecarts: list[str] = []
        if rc != 0:
            ecarts.append(f"le generateur a rendu {rc}")
        for fichier in (RAPPORT, REFUS):
            ecarts.extend(comparer(repo / fichier, cible / fichier.name))
        return {"ok": not ecarts, "ecarts": ecarts, "regeneration_rc": rc, "sortie": sortie}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", default=str(REPO_ROOT),
                        help="racine du depot (defaut : auto)")
    parser.add_argument("--base", default=None,
                        help="reference de base : active l'attribution (#28841). "
                             "Absente -> verdict absolu, comme avant.")
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    repo = Path(args.repo).resolve()
    verdict = verifier(repo)

    attribution = None
    if args.base is not None:
        attribution = attribuer(not verdict["ok"],
                                fichiers_propres(repo, args.base),
                                MOTIFS_ENTREE)
        verdict["attribution"] = attribution
        verdict["base"] = args.base

    if args.json:
        print(json.dumps(verdict, indent=1, ensure_ascii=False))
    else:
        if verdict["ok"]:
            print("census Pyodide : a jour (regeneration hors reseau identique aux "
                  "fichiers commites)")
        else:
            print("census Pyodide : PERIME — la regeneration ne reproduit pas les "
                  "fichiers commites", file=sys.stderr)
            for ligne in verdict["ecarts"][:60]:
                print(ligne, file=sys.stderr)
            if len(verdict["ecarts"]) > 60:
                print(f"... ({len(verdict['ecarts']) - 60} lignes de plus)", file=sys.stderr)
            if verdict["sortie"]:
                print(verdict["sortie"], file=sys.stderr)
            if attribution is not None:
                print(message(attribution["verdict"], GESTE), file=sys.stderr)
                if attribution["fichiers_entree"]:
                    print("   entrees touchees : %s"
                          % ", ".join(attribution["fichiers_entree"][:10]),
                          file=sys.stderr)
    if attribution is not None:
        return 0 if not attribution["bloquant"] else 1
    return 0 if verdict["ok"] else 1



if __name__ == "__main__":
    raise SystemExit(main())
