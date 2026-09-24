"""Resolution du jeton GitHub par compte machine — epinglage par organe, pas par discipline.

#17418 Phase A. Le bucket GraphQL GitHub est 5000/h par UTILISATEUR : toutes
les lanes qui sortent sous le login partage (``jsboige``) vident le meme seau.
Mesure du 2026-09-22 : seau a sec -> ``check_adjoint_prevalidation.py`` rend
rc=2 UNKNOWN sur 10/10 PRs, indiscernable de « pas de dossier », ~3 h sans
merge pendant que 10 dossiers READY existaient.

Ce module est l'implementation UNIQUE de la resolution :

- ``GH_TOKEN`` deja pose (epinglage explicite, CI runner, session debug) ->
  respecte tel quel ;
- sinon -> ``gh auth token --user <compte-machine-local>`` et pose
  ``os.environ["GH_TOKEN"]``. Jamais ``gh auth switch`` : c'est un etat global
  du process ``gh`` qui corrompt les autres lanes du meme trousseau ;
- compte machine non resolvable -> echec BRUYANT avec la remediation. Un repli
  muet sur le compte actif reconstituerait exactement le seau unique qu'on
  corrige.

Transition Phase B/C (#17418) : les lanes dont le compte machine n'existe pas
encore (``myia-po-2024``..``2027``) posent ``COURSIA_GH_PINNING=off`` — le
helper renonce ALORS en imprimant un avertissement fort sur stderr (jamais en
silence), et ``detect_shared_login.py`` continue de les nommer comme tournant
sous le login partage. La Creation des comptes (Phase B) et le provisionnement
des jetons (Phase C) ferment cette echappatoire.
"""

from __future__ import annotations

import argparse
import os
import re
import socket
import subprocess
import sys

SHARED_LOGIN = "jsboige"

# Comptes machine meses le 2026-09-22 (#17418) : ai-01, po-2023 et Web1
# existent ; po-2024..2027 sont 404 jusqu'a la Phase B. Ils figurent deja ici
# pour que la Phase C ne demande AUCUN changement de code : des que le jeton
# est dans le trousseau, les organes l'epinglent.
HOST_ACCOUNTS = {
    "myia-ai-01": "myia-ai-01",
    "myia-po-2023": "myia-po-2023",
    "myia-po-2024": "myia-po-2024",
    "myia-po-2025": "myia-po-2025",
    "myia-po-2026": "myia-po-2026",
    "myia-po-2027": "myia-po-2027",
    "myia-web1": "MyIA-Web1",
}

RATE_LIMIT_RE = re.compile(r"rate limit", re.IGNORECASE)


class GhIdentityError(RuntimeError):
    """Aucun jeton machine resolvable — le repli sur le compte actif est interdit."""


def machine_hostname() -> str:
    """Hostname normalise — ``COMPUTERNAME`` prime sur Windows (cf #17418)."""
    name = os.environ.get("COMPUTERNAME") or socket.gethostname()
    return name.split(".")[0].strip().lower()


def machine_account(hostname: str | None = None) -> str:
    """Compte GitHub de la machine locale.

    ``COURSIA_GH_ACCOUNT`` est une configuration EXPLICITE (tests, machines au
    nom hors convention) — pas un repli : elle ne masque rien, elle designe.
    """
    explicit = os.environ.get("COURSIA_GH_ACCOUNT")
    if explicit:
        return explicit
    host = (hostname if hostname is not None else machine_hostname()).lower()
    try:
        return HOST_ACCOUNTS[host]
    except KeyError:
        raise GhIdentityError(
            f"hostname '{host}' n'a pas de compte machine connu. "
            f"Comptes mappees : {', '.join(sorted(HOST_ACCOUNTS))}. "
            "Poser COURSIA_GH_ACCOUNT=<compte> si cette machine doit en "
            "utiliser un, ou COURSIA_GH_PINNING=off pendant la transition "
            "#17418 Phase B/C."
        ) from None


def pinning_disabled() -> bool:
    return os.environ.get("COURSIA_GH_PINNING", "").lower() == "off"


def resolve_gh_token() -> str:
    """Jeton a epingler : GH_TOKEN existant, sinon trousseau du compte machine.

    N'imprime JAMAIS la valeur du jeton.
    """
    existing = os.environ.get("GH_TOKEN")
    if existing:
        return existing
    account = machine_account()
    try:
        proc = subprocess.run(
            ["gh", "auth", "token", "--user", account],
            capture_output=True, text=True, encoding="utf-8", timeout=30,
        )
    except FileNotFoundError as exc:
        raise GhIdentityError(f"gh CLI introuvable : {exc}") from exc
    if proc.returncode != 0 or not proc.stdout.strip():
        detail = (proc.stderr or proc.stdout).strip()[:300]
        raise GhIdentityError(
            f"gh auth token --user {account} a echoue (rc={proc.returncode}) : "
            f"{detail or 'sortie vide'}. Provisionner le jeton machine "
            f"(#17418 Phase C : master.env + trousseau), ou poser GH_TOKEN "
            "explicitement."
        )
    return proc.stdout.strip()


def pin_gh_token() -> str:
    """Epingle le jeton machine dans ``os.environ`` — idempotent, loud en echec.

    Transition : ``COURSIA_GH_PINNING=off`` renonce en preventif avec un
    avertissement fort (lanes sans compte machine jusqu'a la Phase C).
    """
    if os.environ.get("GH_TOKEN"):
        return os.environ["GH_TOKEN"]
    if pinning_disabled():
        print(
            "GH-IDENTITY (WARN): COURSIA_GH_PINNING=off — appel(s) GitHub sous "
            f"le compte actif (potentiellement le login partage '{SHARED_LOGIN}', "
            "seau commun). Dettes visibles par detect_shared_login.py. #17418 Phase C.",
            file=sys.stderr,
        )
        return ""
    token = resolve_gh_token()
    os.environ["GH_TOKEN"] = token
    return token


def gh_env(base: dict | None = None) -> dict:
    """Env de subprocess avec le jeton epingle (pour les env construits a la main)."""
    env = dict(base if base is not None else os.environ)
    if not env.get("GH_TOKEN"):
        if not pinning_disabled():
            env["GH_TOKEN"] = resolve_gh_token()
    return env


def is_rate_limit_error(text: str) -> bool:
    return bool(RATE_LIMIT_RE.search(text or ""))


def rate_limit_banner(exc_text: str) -> str:
    """Ligne que l'appelant lit SANS --json : rc=2 rate-limit != rc=1 dossier absent.

    C'est la confusion des deux qui a coute ~3 h de merge le 2026-09-22, plus
    que le quota lui-meme.
    """
    detail = (exc_text or "").strip().splitlines()
    first = detail[0][:200] if detail else ""
    return (
        "[RATE-LIMIT] refus GitHub par epuisement de quota — ce n'est PAS un "
        "dossier absent (rc=1). Reessayer avec le jeton machine epingle : "
        "GH_TOKEN=$(gh auth token --user <compte-machine>). Motif : " + first
    )


def _cli(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument(
        "--whoami", action="store_true",
        help="identite + quota GraphQL obtenus par le MEME chemin de resolution que les organes",
    )
    parser.add_argument(
        "--account", action="store_true",
        help="affiche uniquement le compte machine resolu (sans appel reseau)",
    )
    args = parser.parse_args(argv)
    if args.account:
        print(machine_account())
        return 0
    if args.whoami:
        try:
            pin_gh_token()
        except GhIdentityError as exc:
            print(f"GH-IDENTITY (FAIL): {exc}", file=sys.stderr)
            return 1
        proc = subprocess.run(
            ["gh", "api", "user", "--jq", ".login"],
            capture_output=True, text=True, encoding="utf-8",
        )
        if proc.returncode != 0:
            print(f"gh api user a echoue : {proc.stderr.strip()[:300]}", file=sys.stderr)
            return 1
        login = proc.stdout.strip()
        quota = subprocess.run(
            ["gh", "api", "rate_limit", "--jq", ".resources.graphql.remaining"],
            capture_output=True, text=True, encoding="utf-8",
        )
        print(f"login={login} graphql_remaining={quota.stdout.strip()}")
        return 0
    parser.print_help()
    return 0


if __name__ == "__main__":  # pragma: no cover
    sys.exit(_cli())
