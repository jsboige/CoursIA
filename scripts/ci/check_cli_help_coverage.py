#!/usr/bin/env python3
r"""Mesure la couverture ``--help`` des outils en ligne de commande de ``scripts/``.

Pourquoi cet organe
--------------------
Un agent qui découvre un outil doit pouvoir lire son contrat sans ecrire un
wrapper a la main. La surface d'action du depot, c'est les CLI de ``scripts/`` ;
leur contrat natif est ``--help``. Or la couverture reelle de ``--help`` n'a
jamais ete mesuree : l'inventaire du 17/11 (carnet AgentInterfaces-01, mesure
reprise dans la note de conception de #27071) comptait des **nommages** dans
``docs/reference/scripts-reference.md`` (118/622), ce qui est une autre
grandeur -- un script peut etre nomme dans la reference et n'avoir aucune
description native.

Cet organe mesure donc la grandeur demandee par #28964 : parmi les scripts de
``scripts/`` qui ont un point d'entree, quelle part rend ``--help`` avec un
code de retour nul **et** une description non vide.

Denominateur : le critere de point d'entree du 17/11, inchange pour que la
mesure soit comparable et falsifiable -- un ``*.py`` sous ``scripts/`` (hors
``_archive/``) dont la source contient a la fois ``def main(`` et
``argparse``. Le meme critere, execute, donne une part mesurable et un
temoin : la detection n'est pas un catalogue, elle est rejouable.

Verdicts par outil
------------------
    OK              ``--help`` rend rc=0 avec une description non vide
    NO_DESCRIPTION  rc=0, usage present, mais aucune description
    NO_USAGE        rc=0 mais aucune ligne ``usage:`` -- l'outil n'est pas un
                    parseur argparse en pratique (critere statique trompeur)
    EXIT_NONZERO    ``--help`` sort en erreur
    TIMEOUT         ``--help`` depasse le delai borne

Usage:
    python scripts/ci/check_cli_help_coverage.py                        # Mesure globale
    python scripts/ci/check_cli_help_coverage.py --dir scripts/ci       # Un dossier
    python scripts/ci/check_cli_help_coverage.py --json                 # Verdict machine
    python scripts/ci/check_cli_help_coverage.py --expect-missing 5     # Controle positif

Controle positif
----------------
``--expect-missing N`` arme un controle in-band : la mesure doit trouver AU
MOINS ``N`` outils sans description, sinon la sortie est 2. Sans lui,
"tout est couvert" est indiscernable d'un chemin de detection mort (meme
modele que ``scripts/ci/check_docs_index.py --expect-unreachable``). Il faut
le pointer vers un arbre ou le defaut est present ; sur un arbre entierement
couvert, un organe sain rend rc=2.

Codes de sortie :
    0 = mesure rendue (et controle tenu si arme)
    1 = couverture sous le seuil ``--min-coverage``
    2 = controle positif non tenu, ou erreur d'execution
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path, PurePosixPath

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
SCRIPTS_DIR = REPO_ROOT / "scripts"

# Delai borne par outil. Un script qui se bloque a l'import est un verdict
# (TIMEOUT), jamais une attente indefinite : le temps de mesure doit rester
# fini meme sur un arbre malade.
DEFAULT_TIMEOUT = 20.0

# En-tetes de groupes argparse : la description se situe entre le bloc
# ``usage:`` et le premier de ces en-tetes. Un texte qui se termine par ":"
# mais qui n'est pas l'un de ces en-tetes reste une description.
ARGPARSE_GROUP_HEADERS = {
    "positional arguments:",
    "options:",
    "optional arguments:",
    "commands:",
}

# Codes de sortie unifies, alignes sur les autres organes de ``scripts/ci/``.
EXIT_OK = 0
EXIT_BELOW_THRESHOLD = 1
EXIT_CONTROL_OR_ERROR = 2


def decouvrir_outils(scripts_dir: Path) -> list[Path]:
    """Les scripts de ``scripts/`` qui ont un point d'entree CLI.

    Critere identique a l'inventaire du 17/11 : ``def main(`` **et**
    ``argparse`` dans la source. ``_archive/`` est exclu (stock a vider, pas
    surface d'action).
    """
    outils: list[Path] = []
    if not scripts_dir.is_dir():
        return outils
    for py in sorted(scripts_dir.rglob("*.py")):
        if "_archive" in py.parts:
            continue
        try:
            src = py.read_text(encoding="utf-8", errors="ignore")
        except OSError:
            continue
        if "def main(" in src and "argparse" in src:
            outils.append(py)
    return outils


def extraire_description(texte: str) -> str:
    """La description affichee par argparse, ou la chaine vide.

    argparse imprime dans cet ordre : le bloc ``usage:``, puis la description
    (si elle existe), puis les groupes d'arguments. La description est donc
    le texte situe entre la fin du bloc ``usage:`` et le premier en-tete de
    groupe connu.
    """
    lignes = texte.splitlines()
    index_usage = None
    for i, ligne in enumerate(lignes):
        if ligne.startswith("usage:"):
            index_usage = i
            break
    if index_usage is None:
        return ""

    # Le bloc usage se poursuit sur les lignes indentees (repli de la largeur).
    fin_usage = index_usage + 1
    while fin_usage < len(lignes) and lignes[fin_usage][:1] in (" ", "\t"):
        fin_usage += 1

    description: list[str] = []
    for ligne in lignes[fin_usage:]:
        if ligne.strip() in ARGPARSE_GROUP_HEADERS:
            break
        if ligne.strip():
            description.append(ligne.strip())
    return " ".join(description).strip()


def chemin_relatif(script: Path) -> str:
    """Le chemin de l'outil, relatif a la racine du depot quand c'est possible.

    Un arbre de mesure peut vivre hors du depot (jeu de tests synthetique) :
    le chemin absolu est alors conserve tel quel, sans jamais faire echouer
    la mesure.
    """
    try:
        return script.relative_to(REPO_ROOT).as_posix()
    except ValueError:
        return script.as_posix()


def mesurer_outil(script: Path, timeout: float) -> dict[str, object]:
    """Execute ``python <script> --help`` et rend son verdict.

    Le delai est borne : un script bloque est un verdict TIMEOUT, pas une
    attente. La sortie combine stdout et stderr, car certains outils ecrivent
    leur aide sur stderr.
    """
    cmd = [sys.executable, str(script), "--help"]
    env = dict(os.environ)
    env["PYTHONIOENCODING"] = "utf-8"
    try:
        termine = subprocess.run(
            cmd,
            cwd=str(REPO_ROOT),
            capture_output=True,
            text=True,
            encoding="utf-8",
            errors="replace",
            timeout=timeout,
            env=env,
        )
    except subprocess.TimeoutExpired:
        return {
            "path": chemin_relatif(script),
            "verdict": "TIMEOUT",
            "rc": None,
            "description": "",
        }
    except OSError as exc:
        return {
            "path": chemin_relatif(script),
            "verdict": "EXIT_NONZERO",
            "rc": None,
            "description": "",
            "error": str(exc),
        }

    sortie = (termine.stdout or "") + (termine.stderr or "")
    if termine.returncode != 0:
        verdict = "EXIT_NONZERO"
        description = ""
    else:
        description = extraire_description(sortie)
        if "usage:" not in sortie:
            verdict = "NO_USAGE"
        elif description:
            verdict = "OK"
        else:
            verdict = "NO_DESCRIPTION"
    return {
        "path": chemin_relatif(script),
        "verdict": verdict,
        "rc": termine.returncode,
        "description": description,
    }


def dossier_de(chemin: str) -> str:
    """Le dossier de rattachement d'un outil, deduit de son chemin."""
    parent = PurePosixPath(chemin).parent
    return parent.as_posix() if parent.parts else "."


def agreger(mesures: list[dict[str, object]]) -> list[dict[str, object]]:
    """Agrege les mesures par dossier : total, couverts, part."""
    par_dossier: dict[str, dict[str, object]] = {}
    for mesure in mesures:
        cle = dossier_de(str(mesure["path"]))
        entree = par_dossier.setdefault(cle, {"dossier": cle, "total": 0, "couverts": 0})
        entree["total"] = int(entree["total"]) + 1
        if mesure["verdict"] == "OK":
            entree["couverts"] = int(entree["couverts"]) + 1
    lignes = []
    for cle in sorted(par_dossier):
        entree = par_dossier[cle]
        total = int(entree["total"])
        couverts = int(entree["couverts"])
        entree["part"] = round(100.0 * couverts / total, 1) if total else 0.0
        lignes.append(entree)
    return lignes


def rendre_texte(mesures: list[dict[str, object]], dossiers: list[dict[str, object]]) -> str:
    """Rendu humain : couverture par dossier, puis les manques nommes."""
    total = len(mesures)
    couverts = sum(1 for m in mesures if m["verdict"] == "OK")
    part = round(100.0 * couverts / total, 1) if total else 0.0
    lignes = [
        "COUVERTURE --help DES CLI scripts/ -- %d outil(s), %d couvert(s) (%s %%)"
        % (total, couverts, part),
        "",
        "%-46s %6s %8s %8s" % ("dossier", "total", "couverts", "part %"),
    ]
    for entree in dossiers:
        lignes.append(
            "%-46s %6d %8d %7.1f %%"
            % (
                entree["dossier"],
                int(entree["total"]),
                int(entree["couverts"]),
                float(entree["part"]),
            )
        )

    manquants = [m for m in mesures if m["verdict"] != "OK"]
    lignes.append("")
    lignes.append("SANS DESCRIPTION NATIVE : %d" % len(manquants))
    for mesure in manquants:
        lignes.append("  %-12s %s" % (mesure["verdict"], mesure["path"]))
    return "\n".join(lignes)


def main(argv: list[str] | None = None) -> int:
    # La sortie peut contenir des descriptions d'outils non ASCII : sur une
    # console Windows (cp1252), l'ecriture echoue au lieu de s'afficher. La
    # mesure doit rester lisible partout, donc on force l'UTF-8.
    for flux in (sys.stdout, sys.stderr):
        if hasattr(flux, "reconfigure"):
            try:
                flux.reconfigure(encoding="utf-8", errors="replace")
            except (OSError, ValueError):
                pass

    parser = argparse.ArgumentParser(
        description=(
            "Mesure la part des outils de scripts/ qui decrivent leur contrat "
            "via --help (rc=0 + description non vide), par dossier."
        )
    )
    parser.add_argument(
        "--dir",
        dest="repertoires",
        action="append",
        default=None,
        help="Restreint la mesure a ce sous-dossier de scripts/ (repetable).",
    )
    parser.add_argument(
        "--timeout",
        type=float,
        default=DEFAULT_TIMEOUT,
        help="Delai borne par outil, en secondes (defaut : %d)." % int(DEFAULT_TIMEOUT),
    )
    parser.add_argument(
        "--jobs",
        type=int,
        default=min(8, (os.cpu_count() or 2)),
        help="Parallellisme de mesure (defaut : min(8, cpu)).",
    )
    parser.add_argument(
        "--min-coverage",
        type=float,
        default=None,
        help="Seuil de part en %% ; en dessous, la sortie est 1.",
    )
    parser.add_argument(
        "--expect-missing",
        type=int,
        default=None,
        help=(
            "Controle positif : la mesure doit trouver AU MOINS N outils sans "
            "description, sinon la sortie est 2."
        ),
    )
    parser.add_argument("--json", action="store_true", help="Verdict machine.")
    args = parser.parse_args(argv)

    scripts_dir = SCRIPTS_DIR
    if args.repertoires:
        retenus = []
        for rel in args.repertoires:
            cible = (REPO_ROOT / rel).resolve()
            if not cible.is_dir():
                print("dossier inexistant : %s" % rel, file=sys.stderr)
                return EXIT_CONTROL_OR_ERROR
            retenus.append(cible)
        scripts_dir = retenus[0]
        if len(retenus) > 1:
            outils = []
            for cible in retenus:
                outils.extend(decouvrir_outils(cible))
            outils = sorted(set(outils))
        else:
            outils = decouvrir_outils(scripts_dir)
    else:
        outils = decouvrir_outils(scripts_dir)

    if not outils:
        message = "aucun outil CLI trouve sous %s" % scripts_dir
        if args.json:
            print(json.dumps({"statut": "ERREUR", "message": message}, ensure_ascii=False, indent=2))
        else:
            print(message, file=sys.stderr)
        return EXIT_CONTROL_OR_ERROR

    with ThreadPoolExecutor(max_workers=max(1, args.jobs)) as pool:
        mesures = list(pool.map(lambda s: mesurer_outil(s, args.timeout), outils))

    dossiers = agreger(mesures)
    total = len(mesures)
    couverts = sum(1 for m in mesures if m["verdict"] == "OK")
    part = round(100.0 * couverts / total, 1) if total else 0.0
    sans_description = [m for m in mesures if m["verdict"] != "OK"]

    if args.expect_missing is not None and len(sans_description) < args.expect_missing:
        message = (
            "controle positif non tenu : %d outil(s) sans description trouve(s), "
            "%d attendu(s) au minimum -- le chemin de detection est peut-etre mort."
            % (len(sans_description), args.expect_missing)
        )
        if args.json:
            print(json.dumps({"statut": "CONTROLE_NON_TENU", "message": message}, ensure_ascii=False, indent=2))
        else:
            print(message, file=sys.stderr)
        return EXIT_CONTROL_OR_ERROR

    if args.json:
        print(
            json.dumps(
                {
                    "statut": "OK" if (args.min_coverage is None or part >= args.min_coverage) else "SOUS_SEUIL",
                    "total": total,
                    "couverts": couverts,
                    "part": part,
                    "par_dossier": dossiers,
                    "mesures": mesures,
                },
                ensure_ascii=False,
                indent=2,
            )
        )
    else:
        print(rendre_texte(mesures, dossiers))

    if args.min_coverage is not None and part < args.min_coverage:
        return EXIT_BELOW_THRESHOLD
    return EXIT_OK


if __name__ == "__main__":
    sys.exit(main())
