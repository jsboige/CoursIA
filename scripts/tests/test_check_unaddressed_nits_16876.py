"""Regression #16876 : un identifiant host hexagonal n'est pas un SHA de levée.

Sur #16685, le trailer de review `[Hermes ..., host c92df397a786]` était lu
comme la preuve citée par la phrase de levée, alors que la review était
attachée au commit_id exact 31ac6b89... L'organe gardait la réserve ouverte
avec « cite c92df397a786 (absent des commits) ».

Remède : `_cited_shas()` ignore un token hex immédiatement qualifié par
`host`. La protection #13639 (vrais SHAs libres/rembobinés détectés) est
couverte par les contrôles positifs ci-dessous.
"""
import importlib.util
import sys
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "check_unaddressed_nits.py"
spec = importlib.util.spec_from_file_location("check_unaddressed_nits", SCRIPT)
mod = importlib.util.module_from_spec(spec)
sys.modules["check_unaddressed_nits"] = mod
spec.loader.exec_module(mod)


def test_trailer_hermes_host_hex_nest_pas_un_sha():
    # Trailer exact de la fondation #16685
    body = "[Hermes review rendue 2026-09-18T22:05Z, host c92df397a786]"
    assert "c92df397a786" not in mod._cited_shas(body)


def test_host_avec_deux_points_aussi_exclu():
    body = "verdict rendu (host: c92df397a786) le matin"
    assert "c92df397a786" not in mod._cited_shas(body)


def test_sha_reel_hors_qualifiant_host_conserve():
    # Protection #13639 : un vrai SHA cite librement reste détecté
    body = "levée : preuve au commit 31ac6b89 rembobinée par la suite"
    assert "31ac6b89" in mod._cited_shas(body)


def test_sha_reel_dans_meme_corps_que_trailer_host():
    # Les deux tokens dans le même corps : seul le qualifié par host saute
    body = ("[Hermes review rendue, host c92df397a786] — levée car le commit "
            "31ac6b89 porte le fix complet")
    cited = mod._cited_shas(body)
    assert "31ac6b89" in cited
    assert "c92df397a786" not in cited


def test_mot_host_non_qualifiant_ne_masque_pas():
    # `host` suivi d'un autre mot PUIS du SHA : le SHA n'est PAS
    # immédiatement qualifié — il reste un SHA cité
    body = "l'hôte du run (host siege abc12de) comme empreinte"
    assert "abc12de" in mod._cited_shas(body)


def test_host_seul_devant_hex_numerique_deja_filtre():
    # Un token 100% numérique derrière host : déjà exclu par la règle
    # lettre+chiffre de #16103 — l'exclusion host est un second rang
    body = "host 20260918 rien à résoudre"
    assert mod._cited_shas(body) == set()
