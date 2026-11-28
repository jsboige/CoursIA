#!/usr/bin/env python3
"""Verifie que les chemins qui ne doivent jamais etre proposes au commit sont
ignores par une regle VERSIONNEE.

Deux familles, un seul mecanisme :

1. **Les secrets** (`.secrets/`, `master.env`, cles d'App GitHub). Le defaut vise
   est muet : un `.git/info/exclude` local masque un secret sur la machine qui
   l'a ecrit, et `git status` y reste propre. Sur tout autre clone -- une autre
   machine de la flotte, un runner, un fork -- la meme regle n'existe pas, et le
   secret est propose au commit. Les deux situations sont **indiscernables** a
   l'oeil : seule la source gagnante rendue par `git check-ignore -v` les separe.

   Instance fondatrice : `.secrets/master.env`, puis -- un mois plus tard, au meme
   endroit -- les cles privees d'App GitHub sous `.secrets/github-apps/`. Une lecon
   sans organe ne tient pas.

2. **Les artefacts de scratch a la racine du depot** (`scratchpad_*`, chemins
   absolus aplatis). Meme famille de defaut : un `git add -A` les embarque dans
   une PR, et le plafond CI de 512 Ko ne porte que sur `scripts/results/`.
   Mesure du 2026-10-09 dans le clone `D:/Dev/CoursIA-3` : 23 fichiers non
   suivis a la racine, 29 286 258 octets -- dont `pool_c422.json` a 28 888 916
   octets, qu'aucun garde ne(attrapait. Regle : ce qui protege d'un commit
   accidentel est une regle VERSIONNEE, pas une consigne d'agent.

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

# Artefacts de scratch a la racine du depot. Deux familles mesurees :
#   * `scratchpad_*` -- dossiers de cycle ecrits dans le CWD faute de variable ;
#   * un chemin ABSOLU aplati en nom de fichier -- les separateurs ont disparu et
#     le `:` a ete remplace par U+F03A (usage prive), de sorte que le nom commence
#     par la lettre de lecteur. Le marqueur conserve est le segment de chemin
#     temporaire Windows (`AppDataLocalTemp`), present dans les 8 noms mesures.
# Le motif du `.gitignore` est `/[A-Z]*AppDataLocalTemp*` : la lettre de lecteur
# ouvre, le segment temp ferme -- `AppDataLocalTemp` ne peut apparaitre qu'au
# milieu d'un chemin aplati.
_SEPARATEUR_APLATI = "\uf03a"

CHEMINS_SCRATCH_RACINE = (
    "scratchpad_sonde.txt",
    "C" + _SEPARATEUR_APLATI + "UsersjsboiAppDataLocalTempclaude-sonde.txt",
    "D" + _SEPARATEUR_APLATI + "UsersjsboiAppDataLocalTempclaude-sonde.txt",
)

# Chemins qui doivent rester VISIBLES. Sans eux, un organe qui declarerait tout
# ignore passerait au vert en ne mesurant rien.
CONTROLES_POSITIFS = ("README.md", "CLAUDE.md")

# Controles positifs de la famille scratch : `scratchpad.md` ne doit pas tomber
# sous `/scratchpad_*` (le tiret bas fait partie du motif), et
# `COURSE_CATALOG.generated.json` ne doit pas tomber sous un motif trop large
# qui court-circuiterait la lettre de lecteur (mesure : `/C*` le couvre a tort).
CONTROLES_POSITIFS_SCRATCH = ("scratchpad.md", "COURSE_CATALOG.generated.json")

# Marqueurs de la famille scratch, vus sur un nom de fichier a la racine.
MARQUEURS_SCRATCH = ("AppDataLocalTemp",)


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
    ils rendent le meme `git status` propre, et ne protègent que ce clone.
    """
    return source.replace("\\", "/") in suivis


def fichiers_suivis(cwd: Path) -> frozenset[str]:
    res = _git(["ls-files"], cwd)
    if res.returncode != 0:
        raise MesureImpossible(f"`git ls-files` a echoue : {res.stderr.strip()}")
    return frozenset(res.stdout.replace("\\", "/").splitlines())


def est_nom_scratch_racine(nom: str) -> bool:
    """Vrai pour un nom de fichier a la RACINE qui porte un marqueur de scratch.

    La profondeur est discriminante : `scratchpad_*` a la racine est un artefact
    de cycle ; le meme prefixe plus profond peut legitimement designer un
    livrable. Les chemins absolus aplatis, eux, sont toujours a la racine.
    """
    if "/" in nom:
        return False
    if nom.startswith("scratchpad_"):
        return True
    return any(marqueur in nom for marqueur in MARQUEURS_SCRATCH)


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
    chemins_scratch: tuple[str, ...] = CHEMINS_SCRATCH_RACINE,
    controles_positifs_scratch: tuple[str, ...] = CONTROLES_POSITIFS_SCRATCH,
) -> dict:
    # Les sondes sont injectables pour que les tests puissent batir un depot
    # temoin minimal : un organe qu'on ne peut pas faire echouer a volonte
    # n'est pas falsifiable.
    suivis = fichiers_suivis(cwd)
    sensibles = [verdict_chemin(c, cwd, suivis) for c in chemins]
    controles = [verdict_chemin(c, cwd, suivis) for c in controles_positifs]
    scratch = [verdict_chemin(c, cwd, suivis) for c in chemins_scratch]
    controles_scratch = [verdict_chemin(c, cwd, suivis) for c in controles_positifs_scratch]

    defauts = [v for v in sensibles if v["statut"] != "VERSIONNEE"]
    defauts_scratch = [v for v in scratch if v["statut"] != "VERSIONNEE"]
    # L'instrument se falsifie lui-meme : si un controle positif ressort ignore,
    # la mesure ne vaut rien -- et un vert serait pire qu'un rouge.
    instrument_casse = [v for v in controles if v["statut"] != "NON_IGNORE"]
    instrument_casse += [v for v in controles_scratch if v["statut"] != "NON_IGNORE"]

    # Un secret deja SUIVI n'est protege par aucune regle : la regle arrive trop tard.
    suivis_sensibles = sorted(f for f in suivis if "/.secrets/" in f or f.startswith(".secrets/"))
    # Idem pour le scratch : un artefact deja dans l'index ne sortira pas par une
    # regle d'ignore, il faut un `git rm --cached`.
    suivis_scratch = sorted(f for f in suivis if est_nom_scratch_racine(f))

    return {
        "sensibles": sensibles,
        "controles_positifs": controles,
        "scratch": scratch,
        "controles_positifs_scratch": controles_scratch,
        "defauts": defauts,
        "defauts_scratch": defauts_scratch,
        "instrument_casse": instrument_casse,
        "chemins_sensibles_deja_suivis": suivis_sensibles,
        "chemins_scratch_deja_suivis": suivis_scratch,
        "verdict": (
            "INSTRUMENT_CASSE"
            if instrument_casse
            else "SUIVI"
            if (suivis_sensibles or suivis_scratch)
            else "DEFAUT"
            if (defauts or defauts_scratch)
            else "CLEAN"
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
    for v in rapport["scratch"]:
        marque = "ok  " if v["statut"] == "VERSIONNEE" else "DEFAUT"
        origine = f'{v["source"]}:{v.get("ligne")}' if v["source"] else "aucune regle"
        print(f'  {marque} {v["chemin"]:<58} <- {origine}')
    for v in rapport["controles_positifs"] + rapport["controles_positifs_scratch"]:
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
    if rapport["chemins_scratch_deja_suivis"]:
        print("\nSUIVI -- ces artefacts de scratch sont deja dans l'index :")
        for f in rapport["chemins_scratch_deja_suivis"]:
            print(f"    {f}")
        return EXIT_DEFECT
    if rapport["defauts"] or rapport["defauts_scratch"]:
        print("\nDEFAUT -- couverts par une regle LOCALE, donc sur ce clone seulement :")
        for v in rapport["defauts"] + rapport["defauts_scratch"]:
            print(f'    {v["chemin"]}  <- {v["source"] or "aucune regle"}')
        print("  Remede : poser la regle dans le .gitignore VERSIONNE.")
        return EXIT_DEFECT

    print("\nCLEAN -- tous les chemins sensibles sont couverts par une regle versionnee.")
    return EXIT_OK


if __name__ == "__main__":
    sys.exit(main())
