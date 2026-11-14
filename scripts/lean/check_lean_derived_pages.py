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

**Prealable : l'historique doit etre complet.** Un generateur qui lit
`git log` rend une valeur fausse sur un clone **shallow**, et il la rend
plausible : la page et sa verification partagent la troncature, donc
`--check` s'auto-confirme en local pendant que la porte CI (`fetch-depth: 0`)
rougit. Le garde mesure donc l'historique avant de conclure, et rend
`non_mesurable` -- bloquant, sans accuser la page -- quand il est tronque.

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

# Code de sortie conventionnel d'un generateur qui n'a pas pu MESURER (il le
# dit lui-meme : ni `--write` ni `--check` n'ont ete executes, la page sur
# disque n'a pas ete touchee). Distinct de 1 (`divergente`) : la page peut
# etre parfaitement saine, c'est la machine qui n'a pas repondu a l'organe
# amont. Convention posee par `scripts/lean/lean_material_map.py`
# (`UNMEASURABLE_RC`).
GENERATOR_UNMEASURABLE_RC = 2

# (generateur, page). Le generateur est l'organe qui possede la page : il
# sait la regenerer (`--write`) et la verifier (`--check`). Le garde ne
# reimplementerait ni l'un ni l'autre -- il les **interroge**.
PAGES: tuple[tuple[str, str], ...] = (
    ("scripts/lean/lean_theorem_duplicates.py",
     "docs/reference/lean-theorem-duplicates.md"),
    ("scripts/lean/lean_material_map.py",
     "docs/reference/lean-material-map.md"),
)

# Les generateurs qui lisent l'HISTORIQUE (`git log`, `rev-list`, `blame`), par
# opposition a ceux qui ne lisent que l'ARBRE (`git ls-files`). La distinction
# n'est pas cosmetique : un clone **shallow** tronque l'historique, donc ces
# generateurs rendent une valeur fausse -- et ils la rendent **plausible**, ce
# qui est precisement ce qui les rend dangereux.
#
# `lean_material_map.py` calcule sa colonne « Naissance » avec
# `git log -1 --diff-filter=A` : sur un historique tronque, tout lac anterieur a
# la frontiere rend la date de la frontiere (mesure du 2026-11-05 : 35 fois
# `2026-10-17` la ou `main` n'en porte aucune).
# `lean_theorem_duplicates.py` ne lit que `git ls-files` : insensible a la
# troncature, il n'a pas a etre bloque pour elle.
READS_HISTORY: frozenset[str] = frozenset({
    "scripts/lean/lean_material_map.py",
})


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
    if proc.returncode == GENERATOR_UNMEASURABLE_RC:
        # Le generateur a declare sa mesure IMPOSSIBLE : ce n'est pas un
        # verdict sur la page, c'est l'etat de la machine qui interdit de
        # conclure. La page sur disque n'a PAS ete modifiee, donc la regeneree
        # serait un piege : elle y ecrirait une mesure degradee. On bloque
        # (comme le clone shallow) mais en nommant le bon geste.
        return {
            "generator": generator,
            "page": str(page),
            "status": "mesure_impossible",
            "drifted": True,
            "rc": proc.returncode,
            "duration_s": round(time.monotonic() - start, 1),
            "detail": detail or "le generateur n'a pas pu mesurer la page",
        }
    return {
        "generator": generator,
        "page": str(page),
        "status": "conforme" if proc.returncode == 0 else "divergente",
        "drifted": proc.returncode != 0,
        "rc": proc.returncode,
        "duration_s": round(time.monotonic() - start, 1),
        "detail": detail,
    }


def shallow_clone_detail(repo_root: Path | None = None) -> str | None:
    """Rend le motif si l'historique est tronque (clone shallow), sinon `None`.

    **Pourquoi ce prealable existe** (mesure du 2026-11-05). Une page regeneree
    sur un clone shallow a ecrit 35 fois la date de frontiere a la place des
    vraies dates de naissance, et le `--check` **local** rendait CONFORME : le
    generateur et la page partageaient la meme troncature, donc la verification
    se confirmait elle-meme. La porte CI, elle, tourne sur `fetch-depth: 0` et
    a rougi. Un verdict local sur un historique tronque ne mesure donc rien, et
    il se trompe dans les **deux** sens : faux vert sur une page corrompue par
    la troncature, faux rouge sur une page saine regeneree sur un historique
    complet. C'est pourquoi il bloque au lieu de passer.

    Un repertoire qui n'est pas un depot git n'est pas concerne : la mesure
    revient alors aux generateurs, qui diront ce qu'ils ne peuvent pas lire.
    """
    root = Path(repo_root) if repo_root is not None else REPO_ROOT
    try:
        proc = subprocess.run(
            ["git", "-C", str(root), "rev-parse", "--is-shallow-repository"],
            capture_output=True, text=True, encoding="utf-8",
            errors="replace", timeout=30)
    except (OSError, subprocess.SubprocessError):
        return None
    if proc.returncode != 0:
        return None
    if (proc.stdout or "").strip() != "true":
        return None
    boundary = ""
    try:
        shallow_file = root / ".git" / "shallow"
        if shallow_file.is_file():
            head = shallow_file.read_text(encoding="utf-8").split()
            if head:
                boundary = " (frontiere %s)" % head[0][:10]
    except OSError:
        boundary = ""
    return (
        "historique TRONQUE : clone shallow%s -- les generateurs qui lisent "
        "`git log` rendent la date de la frontiere au lieu de la vraie, et le "
        "verdict local s'auto-confirme. Repare par `git fetch --unshallow`, "
        "puis regenere la page." % boundary)


def check_all(timeout: int = 900, repo_root: Path | None = None) -> list[dict]:
    """Verifie toutes les pages derivees. Rend la liste des verifications.

    Le statut `non_mesurable` (clone shallow) est BLOQUANT, mais il se nomme
    pour ce qu'il est : ce n'est pas un verdict sur la page, c'est l'etat du
    depot qui interdit de conclure. Le regenerer ici serait exactement le
    piege -- la page ressortirait avec des dates fabriquees.
    """
    root = Path(repo_root) if repo_root is not None else REPO_ROOT
    truncated = shallow_clone_detail(root)
    results: list[dict] = []
    for gen, page in PAGES:
        if truncated is not None and gen in READS_HISTORY:
            results.append({
                "generator": gen,
                "page": str(root / page),
                "status": "non_mesurable",
                "drifted": True,
                "rc": None,
                "duration_s": 0.0,
                "detail": truncated,
            })
            continue
        results.append(_run_check(gen, timeout, root))
    return results


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
    unmeasurable = [r for r in results if r["status"] == "non_mesurable"]
    impossible = [r for r in results if r["status"] == "mesure_impossible"]

    if args.json:
        print(json.dumps({
            "pages": results,
            "drifted": bool(drifted),
            "expired": bool(expired),
            "non_mesurable": bool(unmeasurable),
            "mesure_impossible": bool(impossible),
            "n_pages": len(results),
        }, indent=2, sort_keys=True))
    else:
        for r in results:
            print("%-12s %s (%.1f s)"
                  % (r["status"].upper(), r["page"], r["duration_s"]))
            if r["drifted"]:
                print("   %s" % (r["detail"] or "la page ne suit pas l'arbre"))
                if r["status"] == "non_mesurable":
                    # Nommer `--write` ici enverrait la lane droit dans le
                    # piege : la page ressortirait avec des dates fabriquees.
                    print("   geste : reparer l'historique, PAS regenerer")
                elif r["status"] == "mesure_impossible":
                    # Meme piege, autre cause : la page n'a pas ete mesuree,
                    # elle n'est pas pour autant fausse. Regenerer ici
                    # ecrirait une mesure degradee (la colonne de couverture
                    # tomberait a `hors matrice` pour tous les lacs).
                    print("   geste : la machine n'a pas repondu -- NE PAS"
                          " regenerer ici ; rejouer ou elargir le budget")
                else:
                    print("   regenere par : python %s --write"
                          % r["generator"])
            elif r["status"] == "expiree":
                print("   %s -- NON BLOQUANT (contrainte de temps, pas un "
                      "defaut de la page)" % r["detail"])

    # Une seule ligne de verdict : un « conforme » qui suivrait une ligne
    # « DIVERGENTE » se lirait comme un acquittement.
    #
    # En mode `--json`, cette ligne part sur **stderr** : stdout doit rester
    # un JSON PARSABLE, sinon le rapport se lit comme un fichier casse. Mesure
    # du 2026-11-03 : la premiere passe de la porte CI a echoue sur un
    # `json.load` alors que le verdict etait « CONFORME (2 pages) » -- les
    # deux pages suivaient l'arbre, mais la sortie melangeait JSON et texte.
    stream = sys.stderr if args.json else sys.stdout
    if drifted:
        if len(unmeasurable) == len(drifted):
            # Rien n'a ete mesure : dire « DIVERGENCE » accuserait la page
            # d'un defaut dont la seule cause mesuree est la troncature.
            print("VERDICT: NON MESURABLE (%d page(s) sur %d -- clone "
                  "shallow)" % (len(drifted), len(results)), file=stream)
        elif len(impossible) == len(drifted):
            # Meme raison, autre cause : la machine n'a pas repondu a l'organe
            # amont. La page n'est pas accusee a tort -- elle n'est pas
            # certifiable ici.
            print("VERDICT: MESURE IMPOSSIBLE (%d page(s) sur %d -- la machine "
                  "n'a pas repondu)" % (len(drifted), len(results)), file=stream)
        else:
            print("VERDICT: DIVERGENCE (%d page(s) sur %d)"
                  % (len(drifted), len(results)), file=stream)
        return 1
    print("VERDICT: CONFORME (%d page(s))" % len(results), file=stream)
    return 0


if __name__ == "__main__":
    sys.exit(main())
