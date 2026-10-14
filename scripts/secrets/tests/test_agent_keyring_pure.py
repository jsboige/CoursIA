"""Invariants purs de `agent_keyring` : `secret_kind`, `entry_key`, `fingerprint`.

Revue Hermes du 24/09 sur #17425, point 2 : seul `cmd_get` etait teste. Ces trois
fonctions portent pourtant les contrats dont depend le reste :

- `secret_kind` tranche jeton / mot de passe sur la FORME, jamais sur le titre ;
- `entry_key` rend les deux noms sous lesquels une entree se demande ;
- `fingerprint` est l'empreinte comparee d'une machine a l'autre pour le critere
  des 7/7 : si son sel ou son nombre de tours change, les empreintes deja
  publiees deviennent incomparables, en silence.
"""

from __future__ import annotations

import hashlib
import importlib.util
import re
from pathlib import Path
from types import SimpleNamespace

import pytest

_MODULE_PATH = Path(__file__).resolve().parents[1] / "agent_keyring.py"


def _load_module():
    spec = importlib.util.spec_from_file_location("agent_keyring_pure_under_test", _MODULE_PATH)
    mod = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(mod)
    return mod


mod = _load_module()


# --- secret_kind -------------------------------------------------------------

@pytest.mark.parametrize("value", [None, ""])
def test_secret_kind_empty(value):
    assert mod.secret_kind(value) == "vide"


@pytest.mark.parametrize(
    "value",
    [
        "ghp_" + "A1b2C3d4E5" * 4,
        "gho_" + "x" * 30,
        "github_pat_" + "a1_B2" * 10,
        "  ghp_" + "Z9" * 20 + "\n",  # espaces autour : la forme est lue apres strip
    ],
)
def test_secret_kind_token_shapes(value):
    assert mod.secret_kind(value) == "jeton"


@pytest.mark.parametrize(
    "value",
    [
        "Xk7#pQ2!mW9&rT4$zL1a",  # mot de passe genere de 20 caracteres (mesure du 22/09)
        "ghp_trop_court",  # prefixe de jeton, forme incomplete
        "github_pat_court",
        "le titre dit github mais la valeur est un mot de passe",
    ],
)
def test_secret_kind_password_shapes(value):
    assert mod.secret_kind(value) == "mot de passe"


# --- entry_key ---------------------------------------------------------------

def test_entry_key_normalises_title_and_username():
    entry = SimpleNamespace(title="  GitHub AI-01 ", username=" MYIA-AI-01")
    assert mod.entry_key(entry) == ("github ai-01", "myia-ai-01")


def test_entry_key_tolerates_missing_fields():
    assert mod.entry_key(SimpleNamespace(title=None, username=None)) == ("", "")


# --- fingerprint -------------------------------------------------------------

_FP_RE = re.compile(r"^<(\d+) car\.> pbkdf2:([0-9a-f]{12})$")


def test_fingerprint_empty():
    assert mod.fingerprint("") == "<vide>"


def test_fingerprint_contract_constants_are_pinned():
    # Changer l'un ou l'autre rend incomparables les empreintes deja publiees.
    assert mod._FP_SALT == b"MyIA-Keys/agent_keyring/fingerprint/v1"
    assert mod._FP_ROUNDS == 600_000


def test_fingerprint_known_vector():
    # Vecteur fige : la comparaison cross-machine repose sur ce calcul exact.
    assert mod.fingerprint("correct horse battery staple") == "<28 car.> pbkdf2:bc8fb4a2ffdd"


def test_fingerprint_matches_reference_pbkdf2():
    value = "une passphrase de test"
    expected = hashlib.pbkdf2_hmac(
        "sha256", value.encode("utf-8"), mod._FP_SALT, mod._FP_ROUNDS
    ).hex()[:12]
    match = _FP_RE.match(mod.fingerprint(value))
    assert match is not None
    assert int(match.group(1)) == len(value)
    assert match.group(2) == expected


def test_fingerprint_is_deterministic_and_discriminating():
    a1 = mod.fingerprint("passphrase-A")
    a2 = mod.fingerprint("passphrase-A")
    b = mod.fingerprint("passphrase-B")
    assert a1 == a2
    assert a1 != b


def test_fingerprint_leaks_no_part_of_the_value():
    value = "queue-reconnaissable-XYZW"
    out = mod.fingerprint(value)
    assert "XYZW" not in out
    assert value not in out
