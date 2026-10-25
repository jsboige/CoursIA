#!/usr/bin/env python
"""Lanceur du gateway Z3 Sudoku, avec pre-vol et sonde de demarrage.

Le service Kernel Gateway en mode ``notebook-http`` ne signale pas qu'il est
inutilisable : il publie son OpenAPI et repond 200 sur le descripteur alors que
le pool de kernels est vide, et chaque ``POST`` expire sans reponse (issue
#22439, defaut b). Ce lanceur ferme cet angle mort par deux mesures :

1. **pre-vol**, avant de demarrer quoi que ce soit : le coeur ``z3_sudoku_core``
   est resolu puis le puzzle de demonstration est resolu en local ; s'il manque,
   on sort en 2 sans avoir ouvert de port ;
2. **sonde**, apres demarrage : l'endpoint doit rendre un resultat exploitable
   dans le delai imparti, faute de quoi le processus enfant est arrete et on
   sort en 3.

Le lanceur ne se deplace pas dans le dossier du carnet : il passe un ``seed_uri``
absolu et laisse le repertoire courant tel quel. C'est volontaire — c'est
exactement le cas d'acceptation de #22439 (demarrage depuis la racine du depot),
donc le lanceur sert aussi de test de non-regression du defaut a.

Codes de sortie :

===== ==========================================================
0     service demarre et endpoint joignable (mode ``--check``)
2     pre-vol en echec (coeur introuvable ou import casse)
3     processus demarre mais endpoint muet dans le delai
4     endpoint joignable mais il repond une erreur
===== ==========================================================
"""

import argparse
import json
import os
import subprocess
import sys
import time
import urllib.error
import urllib.request

CORE_MODULE = "z3_sudoku_core.py"
CHEMIN_DEPUIS_RACINE = os.path.join(
    "MyIA.AI.Notebooks", "SymbolicAI", "SMT", "Z3-API", "gateway"
)
CARNET = "z3-sudoku-service.ipynb"

# Puzzle facile du carnet phare Z3-02-Sudoku-Python.ipynb (cellule 3).
DEMO_PUZZLE = (
    "530070000"
    "600195000"
    "098000060"
    "800060003"
    "400803001"
    "700020006"
    "060000280"
    "000419005"
    "000080079"
)

EXIT_OK = 0
EXIT_PREFLIGHT = 2
EXIT_MUET = 3
EXIT_ERREUR_ENDPOINT = 4


def dossiers_candidats(cwd=None):
    """Dossiers ou le coeur peut se trouver, du plus explicite au plus general.

    Meme ordre que la cellule de preparation du carnet : la variable
    d'environnement, puis le repertoire courant, puis le chemin du coeur
    relativement a chaque niveau remonte depuis le repertoire courant.
    """
    explicite = os.environ.get("Z3_SUDOKU_CORE_DIR")
    if explicite:
        yield explicite
    courant = os.path.abspath(cwd or os.getcwd())
    for _ in range(8):
        yield courant
        yield os.path.join(courant, CHEMIN_DEPUIS_RACINE)
        parent = os.path.dirname(courant)
        if parent == courant:
            break
        courant = parent


def resoudre_coeur(cwd=None):
    """Rend le dossier qui porte ``z3_sudoku_core.py``, ou ``None``."""
    for dossier in dossiers_candidats(cwd):
        if os.path.isfile(os.path.join(dossier, CORE_MODULE)):
            return dossier
    return None


def preflight(cwd=None, verbeux=True):
    """Verifie que le coeur se charge et resout le puzzle de demonstration.

    Rend ``(ok, detail)``. Aucun port n'est ouvert a ce stade.
    """
    dossier = resoudre_coeur(cwd)
    if dossier is None:
        return False, "coeur %s introuvable ; dossiers essayes : %s" % (
            CORE_MODULE,
            ", ".join(dict.fromkeys(dossiers_candidats(cwd))),
        )
    sys.path.insert(0, dossier)
    try:
        from z3_sudoku_core import solve_request
    except Exception as exc:
        return False, "import du coeur depuis %s : %s: %s" % (
            dossier,
            type(exc).__name__,
            exc,
        )
    try:
        reponse = solve_request(DEMO_PUZZLE)
    except Exception as exc:
        return False, "resolution du puzzle de demonstration : %s: %s" % (
            type(exc).__name__,
            exc,
        )
    if reponse.get("status") != "sat":
        return False, "puzzle de demonstration non resolu : %s" % (reponse,)
    if verbeux:
        print("[pre-vol] coeur charge depuis %s" % dossier)
        print(
            "[pre-vol] puzzle de demonstration resolu en %.1f ms"
            % float(reponse.get("time_ms", 0.0))
        )
    return True, dossier


def sonder(url, delai):
    """Sonde l'endpoint jusqu'a ``delai`` secondes ; rend (code, corps)."""
    corps = json.dumps({"puzzle": DEMO_PUZZLE}).encode("utf-8")
    echeance = time.monotonic() + delai
    derniere = None
    while time.monotonic() < echeance:
        restant = max(1.0, echeance - time.monotonic())
        requete = urllib.request.Request(
            url, data=corps, headers={"Content-Type": "application/json"}
        )
        try:
            with urllib.request.urlopen(requete, timeout=restant) as flux:
                return EXIT_OK, json.loads(flux.read().decode("utf-8"))
        except urllib.error.HTTPError as exc:
            derniere = "HTTP %s" % exc.code
        except Exception as exc:
            derniere = "%s: %s" % (type(exc).__name__, exc)
        time.sleep(1.0)
    return EXIT_MUET, derniere


def main(argv=None):
    analyseur = argparse.ArgumentParser(
        description="Lance le gateway Z3 Sudoku avec pre-vol et sonde de demarrage."
    )
    analyseur.add_argument("--port", type=int, default=8899)
    analyseur.add_argument("--hote", default="127.0.0.1")
    analyseur.add_argument(
        "--delai-sonde",
        type=float,
        default=30.0,
        help="secondes accordees a l'endpoint pour repondre apres demarrage",
    )
    analyseur.add_argument(
        "--check",
        action="store_true",
        help="pre-vol + demarrage + sonde, puis arret et code de sortie",
    )
    analyseur.add_argument(
        "--preflight-seul",
        action="store_true",
        help="s'arrete apres le pre-vol (aucun port ouvert)",
    )
    options = analyseur.parse_args(argv)

    ok, detail = preflight()
    if not ok:
        print("[pre-vol] ECHEC -- %s" % detail, file=sys.stderr)
        return EXIT_PREFLIGHT
    if options.preflight_seul:
        return EXIT_OK

    dossier_gateway = resoudre_coeur() or os.getcwd()
    carnet = os.path.join(os.path.abspath(dossier_gateway), CARNET)
    commande = [
        sys.executable,
        "-m",
        "kernel_gateway",
        "--KernelGatewayApp.api=kernel_gateway.notebook_http",
        "--KernelGatewayApp.seed_uri=%s" % carnet,
        "--KernelGatewayApp.port=%d" % options.port,
        "--KernelGatewayApp.ip=%s" % options.hote,
        "--JupyterWebsocketPersonality.list_kernels=True",
    ]
    # Le repertoire courant n'est PAS deplace vers le dossier du carnet : le
    # lancement depuis la racine du depot est le cas d'acceptation de #22439.
    print("[demarrage] %s" % " ".join(commande))
    enfant = subprocess.Popen(commande)

    url = "http://%s:%d/sudoku/solve" % (options.hote, options.port)
    code, charge = sonder(url, options.delai_sonde)
    if code == EXIT_MUET:
        enfant.terminate()
        try:
            enfant.wait(timeout=10)
        except subprocess.TimeoutExpired:
            enfant.kill()
        print(
            "[sonde] ECHEC -- aucun resultat en %.0f s (%s). Le service se "
            "declarait pourtant disponible : c'est le defaut b de #22439."
            % (options.delai_sonde, charge),
            file=sys.stderr,
        )
        return EXIT_MUET
    if not isinstance(charge, dict) or charge.get("status") == "error":
        enfant.terminate()
        try:
            enfant.wait(timeout=10)
        except subprocess.TimeoutExpired:
            enfant.kill()
        print(
            "[sonde] ECHEC -- l'endpoint repond une erreur : %s" % (charge,),
            file=sys.stderr,
        )
        return EXIT_ERREUR_ENDPOINT

    print(
        "[sonde] service disponible sur %s (status=%s, %.1f ms)"
        % (url, charge.get("status"), float(charge.get("time_ms", 0.0)))
    )
    if options.check:
        enfant.terminate()
        try:
            enfant.wait(timeout=10)
        except subprocess.TimeoutExpired:
            enfant.kill()
        return EXIT_OK

    try:
        return enfant.wait()
    except KeyboardInterrupt:
        enfant.terminate()
        try:
            enfant.wait(timeout=10)
        except subprocess.TimeoutExpired:
            enfant.kill()
        return EXIT_OK


if __name__ == "__main__":
    sys.exit(main())
