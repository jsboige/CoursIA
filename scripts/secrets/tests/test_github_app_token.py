"""Falsification of the installation-token forge (#17437).

Two of these tests pass on ANY implementation -- they are the positive
controls. Without them a suite that refuses everything would look green and
prove nothing (lesson of #17425).
"""
from __future__ import annotations

import ast
import importlib.util
import pathlib
import sys

import pytest

_MODULE_PATH = (pathlib.Path(__file__).resolve().parents[1] / "github_app_token.py")


@pytest.fixture(scope="module")
def mod():
    spec = importlib.util.spec_from_file_location("github_app_token", _MODULE_PATH)
    m = importlib.util.module_from_spec(spec)
    sys.modules["github_app_token"] = m
    spec.loader.exec_module(m)
    return m


@pytest.fixture(scope="module")
def keypair():
    from cryptography.hazmat.primitives import serialization
    from cryptography.hazmat.primitives.asymmetric import rsa

    key = rsa.generate_private_key(public_exponent=65537, key_size=2048)
    pem = key.private_bytes(
        encoding=serialization.Encoding.PEM,
        format=serialization.PrivateFormat.PKCS8,
        encryption_algorithm=serialization.NoEncryption(),
    ).decode()
    pub = key.public_key().public_bytes(
        encoding=serialization.Encoding.PEM,
        format=serialization.PublicFormat.SubjectPublicKeyInfo,
    ).decode()
    return pem, pub


# --- controles positifs -----------------------------------------------------

def test_le_jwt_se_verifie_avec_la_cle_publique(mod, keypair):
    """CONTROLE POSITIF : une signature valide DOIT etre acceptee."""
    import jwt

    pem, pub = keypair
    token = mod.build_jwt("123456", pem, now=1_000_000)
    claims = jwt.decode(token, pub, algorithms=["RS256"],
                        options={"verify_exp": False})
    assert claims["iss"] == "123456"


def test_une_cle_pem_valide_est_acceptee(mod, keypair, tmp_path):
    """CONTROLE POSITIF : un PEM legitime ne doit pas etre refuse."""
    pem, _ = keypair
    p = tmp_path / "ok.pem"
    p.write_text(pem, encoding="utf-8")
    assert "PRIVATE KEY" in mod._read_private_key(p)


# --- ce que le correctif doit empecher --------------------------------------

def test_le_jwt_ne_depasse_pas_dix_minutes(mod, keypair):
    """GitHub refuse un JWT dont exp est a plus de 10 min : marge obligatoire."""
    import jwt

    pem, pub = keypair
    now = 1_000_000
    claims = jwt.decode(mod.build_jwt("1", pem, now=now), pub,
                        algorithms=["RS256"], options={"verify_exp": False})
    assert claims["exp"] - now <= 600, "exp au-dela de la fenetre GitHub"
    assert claims["iat"] <= now, "iat dans le futur : rejet pour derive d'horloge"


def test_un_fichier_non_pem_est_refuse(mod, tmp_path):
    p = tmp_path / "pas-une-cle.txt"
    p.write_text("ghp_unPATquelconqueQuiNestPasUnePEM", encoding="utf-8")
    with pytest.raises(mod.ForgeError):
        mod._read_private_key(p)


def test_le_refus_ne_recopie_pas_le_contenu_du_fichier(mod, tmp_path):
    """Un mauvais fichier est souvent un secret d'un AUTRE type.

    L'imprimer transforme une erreur de chemin en seconde fuite.
    """
    secret = "ghp_ceciEstUnSecretQuiNeDoitPasFuir"
    p = tmp_path / "mauvais.txt"
    p.write_text(secret, encoding="utf-8")
    with pytest.raises(mod.ForgeError) as err:
        mod._read_private_key(p)
    assert secret not in str(err.value)


def test_un_fichier_absent_est_refuse(mod, tmp_path):
    with pytest.raises(mod.ForgeError):
        mod._read_private_key(tmp_path / "jamais-cree.pem")


def test_sans_installation_ni_repo_ni_owner_c_est_un_refus(mod):
    with pytest.raises(mod.ForgeError):
        mod.resolve_installation("jwt", None, None)


# --- gardes structurelles ---------------------------------------------------

def test_le_module_n_appelle_jamais_gh_auth_login():
    """`gh auth login` ecrit dans une config partagee par TOUTES les lanes.

    Un jeton d'App y installerait une identite que les sessions voisines
    heriteraient sans le savoir. Le jeton passe par l'environnement, point.
    """
    source = _MODULE_PATH.read_text(encoding="utf-8")
    tree = ast.parse(source)
    for node in ast.walk(tree):
        if isinstance(node, ast.Constant) and isinstance(node.value, str):
            assert node.value != "login", "argument 'login' passe a gh"
    assert "auth" not in [
        n.value for n in ast.walk(tree)
        if isinstance(n, ast.Constant) and isinstance(n.value, str)
    ], "le module ne doit pas toucher `gh auth`"


def test_le_jeton_passe_par_l_environnement(mod, monkeypatch):
    """Preuve positive : GH_TOKEN est pose dans env, pas ecrit ailleurs."""
    vu = {}

    class Faux:
        returncode = 0
        stdout = '{"id": 42}'
        stderr = ""

    def faux_run(cmd, **kw):
        vu["cmd"] = cmd
        vu["env"] = kw.get("env", {})
        return Faux()

    monkeypatch.setattr(mod.subprocess, "run", faux_run)
    mod._api("repos/o/r/installation", "le-jwt")
    assert vu["env"]["GH_TOKEN"] == "le-jwt"
    assert "login" not in vu["cmd"]
