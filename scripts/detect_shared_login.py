"""Detecteur de lane tournant sous le login GitHub partage (#17418 Phase A).

Un detecteur muet se lit comme « tout va bien » : le controle positif est la
moitie du livrable. Ce detecteur fait l'inverse d'un auto-bilan — il sonde ce
qu'une lane SANS epinglage ferait reellement (``gh api user`` dans un env ou
``GH_TOKEN`` est retire), puis nomme la lane et le login qu'elle utiliserait.

Verdicts :

- ``SHARED`` (rc=1) : la sonde non-epinglee sort sous un login qui n'est pas
  le compte machine — le seau commun se vide, remediation affichee ;
- ``MACHINE-EVEN-UNPINNED`` (rc=0) : meme sans epinglage, le compte actif du
  trousseau est deja le compte machine (etag de session) ;
- ``UNRESOLVABLE`` (rc=2) : la machine n'a pas de compte machine connu —
  exactement l'etat que la Phase B/C de #17418 doit fermer ;
- ``PINNED-OK`` avec ``--self`` : le chemin epingle rend le compte machine.

Le test ``scripts/tests/test_detect_shared_login.py`` porte le controle
positif : il declenche volontairement un appel non epingle et ECHOUE si la
detection ne le voit pas.
"""

from __future__ import annotations

import argparse
import os
import subprocess
import sys

import gh_identity


def probe_unpinned_login() -> str | None:
    """Login qu'un appel GH volontairement NON epingle utiliserait.

    Simule la lane sans discipline : ``GH_TOKEN``/``GITHUB_TOKEN`` retires,
    gh resout alors le compte actif du trousseau — typiquement le login
    partage sur les machines de la flotte.
    """
    env = {
        k: v for k, v in os.environ.items()
        if k not in ("GH_TOKEN", "GITHUB_TOKEN")
    }
    try:
        proc = subprocess.run(
            ["gh", "api", "user", "--jq", ".login"],
            capture_output=True, text=True, encoding="utf-8",
            env=env, timeout=30,
        )
    except FileNotFoundError:
        return None
    if proc.returncode != 0:
        return None
    return proc.stdout.strip() or None


def lane_label() -> str:
    workspace = os.environ.get("COURSIA_WORKSPACE", "CoursIA")
    return f"{gh_identity.machine_hostname()}:{workspace}"


def _self_check() -> int:
    try:
        gh_identity.pin_gh_token()
    except gh_identity.GhIdentityError as exc:
        print(f"UNRESOLVABLE lane {lane_label()} — {exc}")
        return 2
    proc = subprocess.run(
        ["gh", "api", "user", "--jq", ".login"],
        capture_output=True, text=True, encoding="utf-8", timeout=30,
    )
    if proc.returncode != 0:
        print(f"PROBE-ERROR lane {lane_label()} — gh api user (epingle) : "
              f"{proc.stderr.strip()[:200]}")
        return 2
    login = proc.stdout.strip()
    account = gh_identity.machine_account()
    if login.lower() != account.lower():
        print(f"SHARED lane {lane_label()} — chemin epingle sort sous "
              f"'{login}' != compte machine '{account}'")
        return 1
    print(f"PINNED-OK lane {lane_label()} — login epingle = {login}")
    return 0


def classify(probe_login: str | None, account: str) -> tuple[str, int]:
    """Verdict (label, rc) d'une sonde non-epinglee contre le compte machine.

    Pure — le controle positif des tests (#17418 Phase A) la consomme : la
    sonde live doit rendre SHARED sur une machine ou le compte actif du
    trousseau n'est pas le compte machine, sinon la detection est cassee.
    """
    if probe_login is None:
        return ("PROBE-ERROR", 2)
    if probe_login.lower() == account.lower():
        return ("MACHINE-EVEN-UNPINNED", 0)
    return ("SHARED", 1)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument(
        "--self", action="store_true",
        help="verifie le chemin EPINGLE (complement de la sonde non-epinglee)",
    )
    args = parser.parse_args(argv)
    if args.self:
        return _self_check()

    account = gh_identity.machine_account()
    unpinned = probe_unpinned_login()
    label, rc = classify(unpinned, account)
    if label == "PROBE-ERROR":
        print(f"PROBE-ERROR lane {lane_label()} — sonde non-epinglee "
              "(gh absent, non authentifie ou reseau)")
    elif label == "MACHINE-EVEN-UNPINNED":
        print(f"MACHINE-EVEN-UNPINNED lane {lane_label()} — compte actif du "
              f"trousseau deja '{unpinned}'")
    else:
        print(
            f"SHARED lane {lane_label()} — un appel NON epingle sortirait sous "
            f"'{unpinned}' (partage) au lieu du compte machine '{account}'. "
            "Chaque organe non epingle vide le seau 5000/h commun. Remediation : "
            "les organes epinglent via gh_identity.pin_gh_token() ; verifier que "
            "COURSIA_GH_PINNING n'est pas a 'off'."
        )
    return rc


if __name__ == "__main__":  # pragma: no cover
    sys.exit(main())
