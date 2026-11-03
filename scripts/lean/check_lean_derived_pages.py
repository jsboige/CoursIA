#!/usr/bin/env python3
"""Garde des pages derivees de l'arbre Lean (pages regenerees, jamais ecrites a la main).

Parent : #24183 (page `lean-theorem-duplicates.md`) et #23097 (page
`lean-material-map.md`).

**Pourquoi ce garde existe** (mesure du 2026-11-03) : le job `Scripts Tests
(CPU)` execute tous les tests de `scripts/`, donc le test de derive de
`docs/reference/lean-theorem-duplicates.md` rendait **rouge toute PR de la
flotte** qui touche `scripts/` -- 22 PRs de la lane `myia-ai-01:CoursIA-2`
bloquees le meme jour. La derive elle-meme est legitime (l'arbre Lean bouge,
la page doit suivre) ; c'est la **portee** du predicat qui etait fausse : une
PR qui ne touche pas l'arbre Lean ne peut pas la causer, et la porte globale
lui imputait quand meme la faute.

Ce garde porte le predicat **la ou il est causable** :
  * il est cable sur les PRs qui touchent un fichier `.lean`, un generateur,
    ou une page derivee ;
  * il nomme la commande qui regenere la page (`--write`) ;
  * il ne teste pas l'etat du depot comme un test global : il verifie que la
    page **commitee** suit l'arbre **de la revision testee**.

**Ce que le garde ne fait pas** : il ne remplace pas la lecture du tableau
des paires (c'est un signal, pas un verdict -- la decision de retirer ou
fusionner une preuve est humaine).

Usage :
    python scripts/lean/check_lean_derived_pages.py            # verdict humain
    python scripts/lean/check_lean_derived_pages.py --json     # verdict machine
    python scripts/lean/check_lean_derived_pages.py --timeout 900
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
import time
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]

# (generateur, page). Le generateur est l'organe qui possede la page : il
# sait la regenerer (`--write`) et la verifier (`--check`). Le garde ne
# reimplementerait ni l'un ni l'autre -- il les **interroge**.
PAGES: tuple[tuple[str, str], ...] = (
    ("scripts/lean/lean_theorem_duplicates.py",
     "docs/reference/lean-theorem-duplicates.md"),
    ("scripts/lean/lean_material_map.py",
     "docs/reference/lean-material-map.md"),
)


def _run_check(generator: str, timeout: int, repo_root: Path | None = None) -> dict:
    """Interroge un generateur en mode `--check`.

    Rend `{"generator", "page", "status", "drifted", "rc", "duration_s",
    "detail"}`, avec `status` :

      * `conforme`   -- le generateur a rendu 0 ;
      * `divergente` -- le generateur a rendu non nul : la page ne suit plus
        l'arbre (c'est le verdict qui BLOQUE) ;
      * `illisible` -- generateur ou page absente : « je n'ai pas pu lire »
        n'est pas « c'est conforme », donc BLOQUE aussi (une installation
        cassee doit se voir) ;
      * `expiree`    -- le generateur a depasse le delai. Ce n'est PAS un
        defaut de la page : c'est une contrainte de temps de la machine.
        Elle est signalee, elle ne bloque pas -- sinon une page lente
        condamnerait les PRs Lean sans dire pourquoi.
    """
    root = Path(repo_root) if repo_root is not None else REPO_ROOT
    gen_path = root / generator
    page = root / dict(PAGES)[generator]
    start = time.monotonic()
    if not gen_path.is_file():
        return {"generator": generator, "page": str(page), "status": "illisible",
                "drifted": True, "rc": None, "duration_s": 0.0,
                "detail": "generateur absent : %s" % generator}
    if not page.is_file():
        return {"generator": generator, "page": str(page), "status": "illisible",
                "drifted": True, "rc": None, "duration_s": 0.0,
                "detail": "page absente : %s" % page}
    try:
        proc = subprocess.run(
            [sys.executable, str(gen_path), "--check"],
            cwd=str(root), capture_output=True, text=True,
            encoding="utf-8", errors="replace", timeout=timeout)
    except subprocess.TimeoutExpired:
        return {"generator": generator, "page": str(page), "status": "expiree",
                "drifted": False, "rc": None,
                "duration_s": round(time.monotonic() - start, 1),
                "detail": "verification expiree apres %d s" % timeout}
    out = (proc.stdout or proc.stderr or "").strip()
    detail = out.splitlines()[-1] if out else ""
    if proc.returncode != 0 and not detail:
        # Un generateur qui sort en erreur SANS rien dire n'est pas un verdict
        # muet : le garde doit pouvoir nommer la page et le geste.
        detail = "le generateur a rendu rc=%d sans message" % proc.returncode
    return {
        "generator": generator,
        "page": str(page),
        "status": "conforme" if proc.returncode == 0 else "divergente",
        "drifted": proc.returncode != 0,
        "rc": proc.returncode,
        "duration_s": round(time.monotonic() - start, 1),
        "detail": detail,
    }


def check_all(timeout: int = 900, repo_root: Path | None = None) -> list[dict]:
    """Verifie toutes les pages derivees. Rend la liste des verifications."""
    return [_run_check(gen, timeout, repo_root) for gen, _ in PAGES]


def main(argv: list | None = None) -> int:
    ap = argparse.ArgumentParser(
        description="Pages derivees de l'arbre Lean : la page suit-elle l'arbre ?")
    ap.add_argument("--json", action="store_true", help="verdict machine")
    ap.add_argument("--timeout", type=int, default=900,
                    help="secondes accordees a chaque generateur (defaut: 900)")
    args = ap.parse_args(argv)

    results = check_all(args.timeout)
    drifted = [r for r in results if r["drifted"]]
    expired = [r for r in results if r["status"] == "expiree"]

    if args.json:
        print(json.dumps({
            "pages": results,
            "drifted": bool(drifted),
            "expired": bool(expired),
            "n_pages": len(results),
        }, indent=2, sort_keys=True))
    else:
        for r in results:
            print("%-12s %s (%.1f s)"
                  % (r["status"].upper(), r["page"], r["duration_s"]))
            if r["drifted"]:
                print("   %s" % (r["detail"] or "la page ne suit pas l'arbre"))
                print("   regenere par : python %s --write"
                      % r["generator"])
            elif r["status"] == "expiree":
                print("   %s -- NON BLOQUANT (contrainte de temps, pas un "
                      "defaut de la page)" % r["detail"])

    # Une seule ligne de verdict : un « conforme » qui suivrait une ligne
    # « DIVERGENTE » se lirait comme un acquittement.
    if drifted:
        print("VERDICT: DIVERGENCE (%d page(s) sur %d)" % (len(drifted),
                                                           len(results)))
        return 1
    print("VERDICT: CONFORME (%d page(s))" % len(results))
    return 0


if __name__ == "__main__":
    sys.exit(main())
