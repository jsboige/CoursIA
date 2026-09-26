#!/usr/bin/env python3
"""Verifie que les chemins sensibles sont ignores par une regle VERSIONNEE.

Le defaut vise est muet : un `.git/info/exclude` local masque un secret sur la machine
qui l'a ecrit, et `git status` y reste propre. Sur tout autre clone -- une autre machine
de la flotte, un runner, un fork -- la meme regle n'existe pas, et le secret est propose
au commit. Les deux situations sont **indiscernables** a l'oeil : seule la source gagnante
rendue par `git check-ignore -v` les separe.

Instance fondatrice : `.secrets/master.env`, puis -- un mois plus tard, au meme endroit --
les cles privees d'App GitHub sous `.secrets/github-apps/`. Une lecon sans organe ne tient
pas.

Sorties : 0 = tous les chemins couverts par une regle versionnee · 1 = defaut ·
2 = mesure impossible (hors depot, git absent).
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

EXIT_OK = 0
EXIT_DEFECT = 1
EXIT_UNREACHABLE = 2

# Chemins qui NE DOIVENT JAMAIS etre proposes au commit, sur n'importe quel clone.
# Ce sont des sondes : elles n'ont pas besoin d'exister sur le disque, `check-ignore`
# repond sur les motifs.
CHEMINS_SENSIBLES = (
    ".secrets/sonde",
    ".secrets/master.env",
    ".secrets/github-apps/sonde.pem",
    "scripts/.secrets/sonde",
    "docker-configurations/services/comfyui-qwen/.secrets/sonde",
)

# Chemins qui doivent rester VISIBLES. Sans eux, un organe qui declarerait tout
# ignore passerait au vert en ne mesurant rien.
CONTROLES_POSITIFS = ("README.md", "CLAUDE.md")


class MesureImpossible(RuntimeError):
    """L'instrument n'a pas pu rendre de verdict -- jamais confondu avec un vert."""


def _git(args: list[str], cwd: Path) -> subprocess.CompletedProcess:
    try:
        return subprocess.run(
            ["git", *args], cwd=str(cwd), capture_output=True, text=True, encoding="utf-8"
        )
    except OSError as exc:  # git absent du PATH
        raise MesureImpossible(f"git injoignable : {exc}") from exc


def parse_ligne_check_ignore(ligne: str) -> dict | None:
    """Decoupe une ligne `git check-ignore -v` : `<source>:<ligne>:<motif>\t<chemin>`.

    Le nom de fichier source peut contenir des `:` (rare mais legal), donc on
    decoupe par la DROITE sur les deux derniers separateurs, pas par la gauche.
    """
    if "\t" not in ligne:
        return None
    gauche, chemin = ligne.split("\t", 1)
    tete, _, motif = gauche.rpartition(":")
    source, _, numero = tete.rpartition(":")
    if not source or not numero.isdigit():
        return None
    return {"source": source, "ligne": int(numero), "motif": motif, "chemin": chemin}


def source_est_versionnee(source: str, suivis: frozenset[str]) -> bool:
    """Une source ne protege le DEPOT que si elle voyage avec lui.

    `.git/info/exclude` et le `core.excludesFile` de l'utilisateur sont locaux :
    ils rendent le meme `git status` propre, et ne protegent que ce clone.
    """
    return source.replace("\\", "/") in suivis


def fichiers_suivis(cwd: Path) -> frozenset[str]:
    res = _git(["ls-files"], cwd)
    if res.returncode != 0:
        raise MesureImpossible(f"`git ls-files` a echoue : {res.stderr.strip()}")
    return frozenset(res.stdout.replace("\\", "/").splitlines())


def verdict_chemin(chemin: str, cwd: Path, suivis: frozenset[str]) -> dict:
    # `--no-index` mesure les REGLES, pas l'etat de l'index : sans lui, un chemin
    # deja suivi serait rendu « non ignore » et masquerait la vraie question.
    res = _git(["check-ignore", "-v", "--no-index", "--", chemin], cwd)
    if res.returncode == 1 and not res.stdout.strip():
        return {"chemin": chemin, "statut": "NON_IGNORE", "source": None}
    if res.returncode not in (0, 1):
        raise MesureImpossible(f"`check-ignore` a rendu {res.returncode} sur {chemin}")
    parsed = parse_ligne_check_ignore(res.stdout.splitlines()[0])
    if parsed is None:
        raise MesureImpossible(f"sortie illisible de `check-ignore` sur {chemin}")
    # Une negation gagnante (`!motif`) rend rc=0 comme une vraie regle d'exclusion
    # (mesure : `git check-ignore -v --no-index` = 0, sortie `.gitignore:2:!...`),
    # mais elle INCLUT le fichier au lieu de l'exclure : le chemin n'est protege
    # par aucune regle d'ignore. Sans ce tri, un secret designore par `!` serait
    # classe VERSIONNEE -- vert sur un fichier stageable (issue #17708).
    if parsed["motif"].startswith("!"):
        return {"chemin": chemin, "statut": "NON_IGNORE", "source": None,
                "raison": f'negation gagnante : {parsed["source"]}:{parsed["ligne"]}'}
    versionnee = source_est_versionnee(parsed["source"], suivis)
    return {
        "chemin": chemin,
        "statut": "VERSIONNEE" if versionnee else "LOCALE",
        "source": parsed["source"],
        "ligne": parsed["ligne"],
        "motif": parsed["motif"],
    }


def analyser(
    cwd: Path,
    chemins: tuple[str, ...] = CHEMINS_SENSIBLES,
    controles_positifs: tuple[str, ...] = CONTROLES_POSITIFS,
) -> dict:
    # Les sondes sont injectables pour que les tests puissent batir un depot
    # temoin minimal : un organe qu'on ne peut pas faire echouer a volonte
    # n'est pas falsifiable.
    suivis = fichiers_suivis(cwd)
    sensibles = [verdict_chemin(c, cwd, suivis) for c in chemins]
    controles = [verdict_chemin(c, cwd, suivis) for c in controles_positifs]

    defauts = [v for v in sensibles if v["statut"] != "VERSIONNEE"]
    # L'instrument se falsifie lui-meme : si un controle positif ressort ignore,
    # la mesure ne vaut rien -- et un vert serait pire qu'un rouge.
    instrument_casse = [v for v in controles if v["statut"] != "NON_IGNORE"]

    # Un secret deja SUIVI n'est protege par aucune regle : la regle arrive trop tard.
    suivis_sensibles = sorted(f for f in suivis if "/.secrets/" in f or f.startswith(".secrets/"))

    return {
        "sensibles": sensibles,
        "controles_positifs": controles,
        "defauts": defauts,
        "instrument_casse": instrument_casse,
        "chemins_sensibles_deja_suivis": suivis_sensibles,
        "verdict": (
            "INSTRUMENT_CASSE"
            if instrument_casse
            else "SUIVI" if suivis_sensibles else "DEFAUT" if defauts else "CLEAN"
        ),
    }


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--repo", default=".", help="racine du depot a mesurer")
    ap.add_argument("--json", action="store_true", help="verdict machine")
    args = ap.parse_args(argv)

    try:
        rapport = analyser(Path(args.repo).resolve())
    except MesureImpossible as exc:
        if args.json:
            print(json.dumps({"verdict": "UNKNOWN", "raison": str(exc)}, ensure_ascii=False))
        else:
            print(f"UNKNOWN -- {exc}", file=sys.stderr)
        return EXIT_UNREACHABLE

    if args.json:
        print(json.dumps(rapport, ensure_ascii=False, indent=2))
        return EXIT_OK if rapport["verdict"] == "CLEAN" else EXIT_DEFECT

    for v in rapport["sensibles"]:
        marque = "ok  " if v["statut"] == "VERSIONNEE" else "DEFAUT"
        origine = f'{v["source"]}:{v.get("ligne")}' if v["source"] else "aucune regle"
        print(f'  {marque} {v["chemin"]:<58} <- {origine}')
    for v in rapport["controles_positifs"]:
        etat = "visible" if v["statut"] == "NON_IGNORE" else "IGNORE (!)"
        print(f'  ctl  {v["chemin"]:<58} -> {etat}')

    if rapport["instrument_casse"]:
        print("\nINSTRUMENT_CASSE -- un controle positif ressort ignore : mesure sans valeur.")
        return EXIT_DEFECT
    if rapport["chemins_sensibles_deja_suivis"]:
        print("\nSUIVI -- ces fichiers sont deja dans l'index, aucune regle ne les retire :")
        for f in rapport["chemins_sensibles_deja_suivis"]:
            print(f"    {f}")
        return EXIT_DEFECT
    if rapport["defauts"]:
        print("\nDEFAUT -- couverts par une regle LOCALE, donc sur ce clone seulement :")
        for v in rapport["defauts"]:
            print(f'    {v["chemin"]}  <- {v["source"] or "aucune regle"}')
        print("  Remede : poser la regle dans le .gitignore VERSIONNE.")
        return EXIT_DEFECT

    print("\nCLEAN -- tous les chemins sensibles sont couverts par une regle versionnee.")
    return EXIT_OK


if __name__ == "__main__":
    sys.exit(main())
