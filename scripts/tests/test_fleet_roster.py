"""Test croise des rosters de la flotte (#21687).

Le roster de reference vit dans ``scripts/secrets/agent_keyring.py``
(``FLEET_ROSTER``, le meme que ROO_FLEET_ROSTER propage le 2026-10-20).
``scripts/gh_identity.py`` (``HOST_ACCOUNTS``) et ``agent_keyring``
(``FLEET_MACHINES``) le partagent : une liste elargie sans l'autre derougit
ici, au lieu de se decouvrir a la premiere observation refusee
(``GhIdentityError`` sur un hostname absent, ou absence d'empreinte de
reference pour `doctor`).

Le test s'execute en CI comme n'importe quel test : les deux modules sont
charges depuis l'arbre du repo, jamais depuis le stockage partage.
"""

from __future__ import annotations

import importlib.util
from pathlib import Path

_SCRIPTS = Path(__file__).resolve().parents[1]


def _load(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(mod)
    return mod


gh_identity = _load("gh_identity_roster_under_test", _SCRIPTS / "gh_identity.py")
agent_keyring = _load(
    "agent_keyring_roster_under_test", _SCRIPTS / "secrets" / "agent_keyring.py"
)

ROSTER = set(agent_keyring.FLEET_ROSTER)


def test_fleet_machines_covers_reference_roster():
    """FLEET_MACHINES porte exactement le roster de reference."""
    assert set(agent_keyring.FLEET_MACHINES) == ROSTER


def test_host_accounts_covers_only_roster_machines():
    """HOST_ACCOUNTS ne mappe que des machines du roster, dans les deux sens
    ou c'est possible : une cle hors roster est un hostname invente, une
    valeur hors roster est un login mappe sur une machine inconnue."""
    hosts = set(gh_identity.HOST_ACCOUNTS)
    assert hosts <= ROSTER, f"hostnames hors roster : {sorted(hosts - ROSTER)}"
    mapped_hosts = {h for h in ROSTER if h in hosts}
    assert mapped_hosts == hosts  # forme explicite : rien de perdu en route


def test_host_accounts_covers_every_roster_machine_with_account():
    """Chaque machine du roster a un compte, ou est declaree en attente.

    Une machine sans entree dans HOST_ACCOUNTS est soit nouvelle (compte
    GitHub pas encore cree -- ``myia-po-2028`` et ``myia-web2`` au
    2026-10-20), soit un oubli. Le test n'exige pas que le compte existe :
    il exige que l'ecart soit FINI, nomme et borne -- il rougit des qu'un
    troisieme hostname manque, et des qu'un compte cree n'est pas mappe
    (l'ensemble d'attente se reduit alors, et ce test passe a condition de
    le retirer).
    """
    hosts = set(gh_identity.HOST_ACCOUNTS)
    missing = ROSTER - hosts
    assert missing <= {"myia-po-2028", "myia-web2"}, (
        f"machines du roster sans compte mappe : {sorted(missing)} -- "
        "ajouter le login a HOST_ACCOUNTS des sa creation"
    )


def test_expected_gh_only_maps_roster_machines():
    """EXPECTED_GH (verifications `gh login` du coffre) ne cite que des
    machines du roster : il ne peut pas attendre un jeton d'une machine
    inconnue."""
    expected_hosts = set(agent_keyring.EXPECTED_GH)
    normalised = {h.lower() for h in expected_hosts}
    assert normalised <= ROSTER, (
        f"EXPECTED_GH hors roster : {sorted(normalised - ROSTER)}"
    )
