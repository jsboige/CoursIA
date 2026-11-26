#!/usr/bin/env python3
"""Enregistre et VERIFIE le kernelspec `python3` du job (#28501).

CE QUE CE SCRIPT GARDEIT
------------------------
Le job `Scripts Tests (CPU)` tourne sur un parc auto-heberge, ou plusieurs
jobs partagent le meme `HOME`. Le kernelspec `python3` enregistre par
l'utilisateur est donc ecrit dans un repertoire PARTAGE : deux jobs
concurrents y ecrivent deux `python3` differents, et la legende papermill
peut demarrer l'interpreteur de l'autre.

L'isolation (#28501) decale l'ecriture ET la lecture vers un repertoire
PROPRE au job (`JUPYTER_DATA_DIR` / `JUPYTER_PATH`). Ce script est le
**troisieme** morceau, celui qui manque : constater que l'isolation a ete
declaree ne prouve pas que le noyau que Jupyter RESOUT est celui du job.

QUATRE CONTROLES, dont deux NEGATIFS
------------------------------------
1. **L'enregistrement est fatal.** Le geste precedent etait un
   `if python -c "import ipykernel" ; then ... ; else echo "ipykernel
   absent" ; fi` : quand l'import echouait, le step **imprimait un message
   et rendait succes**. Le job continuait, sans noyau enregistre, et
   l'echec n'apparaitrait que plus loin -- sur un noyau que Jupyter
   resout ailleurs. Ici, `ipykernel` absent de l'interpreteur du job est un
   echec du job.
2. **Le kernelspec RESOLU est celui du job.** `get_kernel_spec("python3")`
   rend le spec que Jupyter utilise reellement ; son repertoire de
   ressources doit etre SOUS le repertoire du job. Un spec resolu hors de
   ce repertoire signifie que la lecture a echappe a l'isolation -- c'est
   le defaut que l'isolation pretend corriger.
3. **L'argv[0] est l'interpreteur du job.** Le noyau doit demarrer le
   Python du job, pas un autre `python3` trouve ailleurs. C'est le controle
   qui rattrape #28500 (l'interpreteur resolu n'etait pas celui du job).
4. **L'ENVIRONNEMENT du lanceur est celui du job.** Deux virtualenvs
   distincts peuvent pointer sur le MEME binaire : leurs lanceurs ont le
   meme `realpath`, mais pas le meme `sys.prefix`. Comparer les chemins
   seule ne les distingue pas -- et le mauvais virtualenv demarre SANS
   ERREUR (il importe `ipykernel` tres bien), si bien que le job rend un
   SUCCES SILENCIEUX sur un environnement qui n'est pas le sien. Le
   controle compare donc l'IDENTITE de l'interpreteur : son binaire
   resolu ET le prefixe qu'il annonce lui-meme.

   Un prefixe NON MESURABLE (timeout, sortie vide, code non nul) n'est pas
   un prefixe identique : il dit qu'on ne sait pas. Le controle le rend
   alors INCIDENT (code 2) -- un vert sur une mesure ABSENTE serait un
   succes SILENCIEUX, precisement ce que ce script existe pour attraper.

Le noyau absent est un ECHEC, pas un incident : un job sans noyau ne peut
pas lancer la legende papermill.

Usage :

    python scripts/ci/verify_job_kernelspec.py --register   # job CI
    python scripts/ci/verify_job_kernelspec.py              # controle seul

Codes de sortie : 0 conforme, 1 violation, 2 incident (environnement
inconnu -- ni l'un ni l'autre n'est un vert).
"""

from __future__ import annotations

import argparse
import json
import os
import shutil
import subprocess
import sys
from collections.abc import Callable
from pathlib import Path

RC_OK = 0
RC_VIOLATION = 1
RC_INCIDENT = 2

KERNEL_NAME = "python3"
JOB_DIR_VAR = "JUPYTER_DATA_DIR"


class KernelAbsent(Exception):
    """Le kernelspec demande n'est resolu par Jupyter."""


class EnvironmentInconnu(Exception):
    """L'environnement de mesure n'est pas celui du job."""


class IncidentViolation(str):
    """Une violation ou l'ENVIRONNEMENT n'a pas pu etre MESURE.

    Un prefixe non mesurable (timeout, sortie vide, code non nul) ne dit pas
    que les deux environnements sont identiques : il dit qu'on ne le SAIT
    pas. Rendre cela non vert est la seule lecture honnete -- un vert sur une
    mesure ABSENTE est un succes SILENCIEUX, precisement le defaut que ce
    script existe pour attraper.
    """


def verdict_de(violations: list[str]) -> tuple[str, int]:
    """Le verdict et le code de sortie correspondants aux violations.

    `INCIDENT` prime sur `VIOLATION` : un incident (environnement non mesure)
    n'est pas un controle rate -- et le dit plus fort.
    """
    if any(isinstance(v, IncidentViolation) for v in violations):
        return "INCIDENT", RC_INCIDENT
    if violations:
        return "VIOLATION", RC_VIOLATION
    return "OK", RC_OK


def _normalise(path: str) -> str:
    """Chemin comparable : resolu (symlinks inclus), casse et separateurs unis.

    `realpath` degrade proprement sur un chemin absent ; `normcase` applique
    ensuite la casse de la plateforme (Windows) et unifie les separateurs.
    """
    return os.path.normcase(os.path.realpath(os.path.normpath(path)))


def _est_sous(enfant: str, parent: str) -> bool:
    """`enfant` est-il `parent` lui-meme, ou l'un de ses descendants ?"""
    enfant, parent = _normalise(enfant), _normalise(parent)
    return enfant == parent or enfant.startswith(parent + os.sep)


def prefixe_de(interpreteur: str) -> str | None:
    """Le `sys.prefix` que l'interpreteur annonce LUI-MEME.

    Deux virtualenvs distincts peuvent pointer sur le meme binaire : leurs
    lanceurs ont le meme `realpath` et des `sys.prefix` differents. Le
    prefixe est donc ce qui distingue les ENVIRONNEMENTS la ou les chemins
    ne distinguent plus rien.

    Rend `None` quand l'interpreteur ne peut pas etre lance -- un prefixe
    non mesurable n'est pas un prefixe different, et n'est pas non plus un
    prefixe identique : le controleur en fait un INCIDENT.
    """
    try:
        fait = subprocess.run(
            [interpreteur, "-c", "import sys; print(sys.prefix)"],
            capture_output=True, text=True, encoding="utf-8",
            errors="replace", timeout=120, check=False,
        )
    except (OSError, subprocess.TimeoutExpired):
        return None
    if fait.returncode != 0:
        return None
    return (fait.stdout or "").strip() or None


def resoudre_le_noyau(nom: str = KERNEL_NAME) -> tuple[list[str], str]:
    """Resout le kernelspec comme Jupyter le fait.

    Rend `(argv, repertoire_des_ressources)`. Lève `KernelAbsent` si le
    kernelspec n'est pas resolu.
    """
    try:
        from jupyter_client.kernelspec import KernelSpecManager
    except ImportError as exc:  # pragma: no cover - incident d'environnement
        raise EnvironmentInconnu(
            f"jupyter_client est injoignable : {exc}") from exc

    manager = KernelSpecManager()
    try:
        spec = manager.get_kernel_spec(nom)
    except Exception as exc:  # NoSuchKernel et ses parents
        raise KernelAbsent(
            f"le kernelspec `{nom}` n'est pas resolu : {exc}") from exc
    return list(spec.argv), str(spec.resource_dir)


def controler(
    argv: list[str] | None,
    repertoire_du_spec: str | None,
    interpreteur_attendu: str,
    repertoire_du_job: str,
    prefixes: Callable[[str], str | None] = prefixe_de,
) -> list[str]:
    """Rend la liste des violations (vide = conforme).

    Les quatre controles sont passes separement, pour que les tests
    puissent en exercer un seul a la fois. `prefixes` est injectable pour
    que les tests puissent simuler deux environnements distincts sans
    construire deux virtualenvs.
    """
    violations: list[str] = []

    if argv is None or repertoire_du_spec is None:
        violations.append(
            f"noyau absent : le kernelspec `{KERNEL_NAME}` n'est pas resolu "
            f"-- le job ne peut pas lancer de noyau"
        )
        return violations

    if not _est_sous(repertoire_du_spec, repertoire_du_job):
        violations.append(
            f"noyau resolu hors du job : le spec est dans "
            f"`{repertoire_du_spec}`, hors du repertoire du job "
            f"`{repertoire_du_job}` -- l'isolation n'a pas ete respectee"
        )

    if not argv:
        violations.append("argv vide : le noyau ne dit pas quel interpreteur lancer")
    else:
        argv0 = argv[0]
        if os.path.isabs(argv0):
            lanceur = argv0
        else:
            lanceur = shutil.which(argv0) or argv0
        resolu = _normalise(lanceur)
        attendu = _normalise(interpreteur_attendu)
        if resolu != attendu:
            violations.append(
                f"interpreteur different : le noyau lance `{argv0}`, le job "
                f"utilise `{interpreteur_attendu}` -- le noyau ne demarre pas "
                f"le Python du job"
            )
        elif os.path.normcase(lanceur) != os.path.normcase(interpreteur_attendu):
            # Meme binaire, deux LANCEURS : le cas des virtualenvs distincts,
            # dont les `realpath` coincident. Les chemins ne distinguent plus
            # rien ; l'ENVIRONNEMENT (le prefixe annonce par l'interpreteur)
            # est ce qui les distingue encore.
            prefixe_lanceur = prefixes(lanceur)
            prefixe_job = prefixes(interpreteur_attendu)
            if prefixe_lanceur is None:
                violations.append(IncidentViolation(
                    f"prefixe du noyau non mesurable : le lanceur "
                    f"`{lanceur}` n'annonce aucun `sys.prefix` (timeout, "
                    f"sortie vide ou code non nul) -- l'identite du noyau "
                    f"n'est pas verifiee"
                ))
            elif prefixe_job is None:
                violations.append(IncidentViolation(
                    f"prefixe du job non mesurable : l'interpreteur "
                    f"`{interpreteur_attendu}` n'annonce aucun `sys.prefix` "
                    f"(timeout, sortie vide ou code non nul) -- l'identite "
                    f"du noyau n'est pas verifiee"
                ))
            elif prefixe_lanceur != prefixe_job:
                violations.append(
                    f"environnement different : le noyau lance `{lanceur}` "
                    f"(prefixe `{prefixe_lanceur}`), le job utilise "
                    f"`{interpreteur_attendu}` (prefixe `{prefixe_job}`) -- "
                    f"le noyau ne demarre pas le Python du job"
                )

    return violations


def ipykernel_importable(interpreteur: str) -> tuple[bool, str]:
    """`ipykernel` est-il importable par l'interpreteur du job ?

    Rend `(importable, sortie)`. La sortie est vide quand l'import reussit.
    """
    try:
        fait = subprocess.run(
            [interpreteur, "-c", "import ipykernel"],
            capture_output=True, text=True, encoding="utf-8",
            errors="replace", timeout=300, check=False,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        return False, f"l'import n'a pas pu etre lance : {exc}"
    if fait.returncode != 0:
        return False, (fait.stderr or fait.stdout or "").strip()[:400]
    return True, ""


def enregistrer(interpreteur: str) -> tuple[bool, str]:
    """Enregistre le kernelspec avec l'interpreteur du job.

    Rend `(reussi, sortie)`. L'enregistrement est idempotent.
    """
    commande = [
        interpreteur, "-m", "ipykernel", "install", "--user",
        "--name", KERNEL_NAME, "--display-name", KERNEL_NAME,
    ]
    try:
        fait = subprocess.run(
            commande, capture_output=True, text=True, encoding="utf-8",
            errors="replace", timeout=600, check=False,
        )
    except (OSError, subprocess.TimeoutExpired) as exc:
        return False, f"l'enregistrement n'a pas pu etre lance : {exc}"
    if fait.returncode != 0:
        return False, (fait.stderr or fait.stdout or "").strip()[:400]
    return True, (fait.stdout or "").strip()


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Verifie que le kernelspec resolu par Jupyter est celui "
                    "du job (#28501).")
    parser.add_argument(
        "--register", action="store_true",
        help="Enregistre le noyau avant de controler (etape de CI).")
    parser.add_argument("--json", action="store_true", help="Sortie machine.")
    args = parser.parse_args(argv)

    repertoire_du_job = os.environ.get(JOB_DIR_VAR)
    interpreteur = sys.executable

    if not repertoire_du_job:
        message = (f"{JOB_DIR_VAR} absent -- le job n'est pas isole ; sans "
                   f"repertoire propre, le kernelspec est partage par tous "
                   f"les jobs de l'hote")
        if args.json:
            print(json.dumps({"verdict": "INCIDENT", "violations": [message]},
                             indent=2, ensure_ascii=False))
        else:
            print(f"INCIDENT : {message}", file=sys.stderr)
        return RC_INCIDENT

    violations: list[str] = []

    if args.register:
        importable, sortie = ipykernel_importable(interpreteur)
        if not importable:
            violations.append(
                f"ipykernel absent de l'interpreteur du job "
                f"(`{interpreteur}`) : {sortie or 'import impossible'} -- "
                f"l'enregistrement ne peut pas se faire"
            )
        else:
            reussi, sortie = enregistrer(interpreteur)
            if not reussi:
                violations.append(
                    f"l'enregistrement du noyau a echoue : {sortie}")

    try:
        argv_noyau, repertoire_du_spec = resoudre_le_noyau()
    except KernelAbsent as exc:
        violations.append(str(exc))
        argv_noyau, repertoire_du_spec = None, None
    except EnvironmentInconnu as exc:
        message = f"environnement de mesure inconnu : {exc}"
        if args.json:
            print(json.dumps({"verdict": "INCIDENT", "violations": [message]},
                             indent=2, ensure_ascii=False))
        else:
            print(f"INCIDENT : {message}", file=sys.stderr)
        return RC_INCIDENT

    violations.extend(controler(
        argv_noyau, repertoire_du_spec, interpreteur, repertoire_du_job))

    verdict, code = verdict_de(violations)
    if args.json:
        print(json.dumps({
            "verdict": verdict,
            "kernel": KERNEL_NAME,
            "job_dir": repertoire_du_job,
            "interpreter": interpreteur,
            "prefix": prefixe_de(interpreteur),
            "spec_dir": repertoire_du_spec,
            "argv": argv_noyau,
            "violations": violations,
        }, indent=2, ensure_ascii=False))
        return code

    if not violations:
        print(f"OK : noyau `{KERNEL_NAME}` resolu dans `{repertoire_du_spec}`, "
              f"interpreteur `{argv_noyau[0]}` (job : `{repertoire_du_job}`)")
        return RC_OK

    if verdict == "INCIDENT":
        print("INCIDENT : l'identite du noyau n'a pas pu etre verifiee :",
              file=sys.stderr)
    else:
        print(f"{len(violations)} violation(s) sur le kernelspec du job :",
              file=sys.stderr)
    for violation in violations:
        print(f"  - {violation}", file=sys.stderr)
    return code


if __name__ == "__main__":
    sys.exit(main())
