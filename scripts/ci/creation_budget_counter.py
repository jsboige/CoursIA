#!/usr/bin/env python3
"""Compteur du budget de creation de carnets (#23174).

Le regime « ralentir la creation » a besoin d'un **compteur** : combien de
carnets neufs la flotte a demarres sur 7 jours glissants, et quel est le
budget qui en decoule. Ce script produit l'etat ; le tapis le lit.

Trois mesures, toutes derivées d'une source primaire :

  A. `carnets_neufs_demarres` — les `.ipynb` AJOUTES sur `origin/main`
     dans la fenetre (`git log --diff-filter=A`). C'est la mesure la plus
     proche de la realite du depot : un carnet neuf demarre est un carnet
     neuf **present sur main**, pas un carnet annonce dans une PR.
  B. `grains_livres_semaine` — les issues fermees dans la fenetre
     (`gh issue list --state closed`) : le nombre de grains que la flotte a
     livres la semaine ecoulee, qui est le multiplicateur du budget.
  C. la part de creation du pool ouvert — mesuree par le module
     `scripts/creation_budget.py` sur le meme pool que le tapis.

Le budget n'est JAMAIS une constante posee a la main :

    part_creation = propositions de creation / pool ouvert
    budget        = max(1, round(part_creation x grains livres))

Le compte etant mesure sur une fenetre glissante, l'etat est une **instantanee**
: le tapis le lit au moment du tirage, et le compteur le reecrit.

Sortie : un JSON d'etat, et un resume lisible sur stdout.

Usage :

    python scripts/ci/creation_budget_counter.py --out <fichier.json>
    COURSIA_CREATION_BUDGET_FILE=<fichier.json> python \\
        scripts/ci/creation_budget_counter.py
"""

from __future__ import annotations

import argparse
import datetime as dt
import json
import os
import pathlib
import subprocess
import sys

SCRIPTS_DIR = pathlib.Path(__file__).resolve().parent.parent
if str(SCRIPTS_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPTS_DIR))

import creation_budget as cb  # noqa: E402

REPO = "jsboige/CoursIA"
DEFAULT_REF = "origin/main"
WINDOW_DAYS = 7


def _run(cmd: list[str], timeout: int = 180) -> str:
    out = subprocess.run(cmd, capture_output=True, text=True, encoding="utf-8",
                         timeout=timeout, check=False)
    if out.returncode != 0:
        raise RuntimeError(f"{cmd[0]} a echoue : {(out.stderr or '').strip()[:300]}")
    return out.stdout


def new_notebooks(repo_root: str, ref: str, since: dt.datetime) -> dict:
    """Les `.ipynb` AJOUTES sur `ref` depuis `since` (mesure A).

    `git log --diff-filter=A` ne liste que les ajouts : un carnet deplace
    ou renumerote n'est pas un carnet neuf. Le decompte separe les jumeaux
    `_en` (la version anglaise d'un carnet deja cree) du total.
    """
    since_iso = since.strftime("%Y-%m-%dT%H:%M:%S")
    out = _run(["git", "-C", repo_root, "log", "--diff-filter=A",
                "--name-only", "--pretty=format:%H", f"--since={since_iso}",
                ref, "--", "*.ipynb"])
    paths = [ln.strip() for ln in out.splitlines() if ln.strip().endswith(".ipynb")]
    uniques = sorted(set(paths))
    jumeaux = [p for p in uniques if p.rsplit("/", 1)[-1].endswith("_en.ipynb")]
    return {
        "carnets_neufs_demarres": len(uniques),
        "carnets_neufs_hors_jumeaux_en": len(uniques) - len(jumeaux),
        "jumeaux_en": len(jumeaux),
        "chemins": uniques,
    }


def closed_issues(since: dt.datetime, until: dt.datetime) -> int:
    """Les issues fermees dans la fenetre (mesure B).

    `gh issue list --state closed` ne liste que des ISSUES (les PRs sont
    exclues par construction de la commande) : c'est l'unite du tapis.
    """
    lo = since.strftime("%Y-%m-%d")
    hi = until.strftime("%Y-%m-%d")
    out = _run(["gh", "issue", "list", "--repo", REPO, "--state", "closed",
                "--search", f"closed:{lo}..{hi}", "--limit", "2000",
                "--json", "number"])
    try:
        return len(json.loads(out))
    except Exception:  # noqa: BLE001 - une reponse illisible = 0 mesure
        return 0


def open_pool() -> list[dict]:
    """Le pool ouvert, lu par le MEME code que le tapis.

    On importe `pick_idle_grain` plutot que de reimplementer la lecture :
    deux lectures du pool divergeraient, et le budget serait mesure sur un
    pool que le tapis ne voit jamais.
    """
    import pick_idle_grain as pig
    pool, read_error = pig.fetch_pool()
    if read_error:
        print(f"[POOL] lecture partielle : {read_error}", file=sys.stderr)
    return pool


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description="Compteur du budget de creation")
    ap.add_argument("--out", default=None,
                    help="fichier d'etat a ecrire (defaut : "
                         "$COURSIA_CREATION_BUDGET_FILE)")
    ap.add_argument("--repo-root", default=".", help="racine du depot")
    ap.add_argument("--ref", default=DEFAULT_REF)
    ap.add_argument("--days", type=int, default=WINDOW_DAYS)
    ap.add_argument("--dry-run", action="store_true",
                    help="mesurer et afficher sans ecrire l'etat")
    args = ap.parse_args(argv)

    out = args.out or os.environ.get(cb.ENV_STATE, "").strip()
    if not out:
        print(f"aucun fichier d'etat : poser --out ou ${cb.ENV_STATE}",
              file=sys.stderr)
        return 2

    now = dt.datetime.now(dt.UTC)
    since = now - dt.timedelta(days=args.days)

    catalog = cb.NotebookCatalog.from_repo(args.repo_root, args.ref)
    mesures = new_notebooks(args.repo_root, args.ref, since)
    livres = closed_issues(since, now)
    pool = open_pool()
    budget, preuve = cb.derive_budget(pool, livres, catalog)

    etat = {
        "mesure_le": now.strftime("%Y-%m-%dT%H:%M:%SZ"),
        "fenetre_jours": args.days,
        "ref": args.ref,
        "carnets_neufs_demarres": mesures["carnets_neufs_demarres"],
        "carnets_neufs_hors_jumeaux_en": mesures["carnets_neufs_hors_jumeaux_en"],
        "jumeaux_en": mesures["jumeaux_en"],
        "grains_livres_semaine": livres,
        "budget": budget,
        "budget_brut": preuve["budget_brut"],
        "plancher_applique": preuve["plancher_applique"],
        "part_creation": preuve["part_creation"],
        "pool_ouvert": preuve["pool_ouvert"],
        "propositions_creation": preuve["propositions_creation"],
        "portes_creation": preuve["portes_creation"],
        "catalogue_connu": catalog.known,
    }
    trop, why = cb.over_budget(etat)
    etat["depassement"] = trop
    etat["raison"] = why

    if not args.dry_run:
        pathlib.Path(out).parent.mkdir(parents=True, exist_ok=True)
        pathlib.Path(out).write_text(
            json.dumps(etat, ensure_ascii=False, indent=2) + "\n",
            encoding="utf-8")

    print(f"carnets neufs demarres ({args.days} j) : "
          f"{etat['carnets_neufs_demarres']} "
          f"(hors jumeaux _en : {etat['carnets_neufs_hors_jumeaux_en']})")
    print(f"grains livres (issues fermees)        : {livres}")
    print(f"pool ouvert / propositions creation  : {preuve['pool_ouvert']} / "
          f"{preuve['propositions_creation']} "
          f"(part {preuve['part_creation']:.3f})")
    print(f"budget derive                        : {budget} "
          f"(brut {preuve['budget_brut']}, plancher "
          f"{'applique' if preuve['plancher_applique'] else 'non applique'})")
    print(f"depassement                          : {why}")
    if not args.dry_run:
        print(f"etat ecrit                           : {out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
