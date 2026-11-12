"""Tests #17437 — la levée B.0 sous identité GitHub App du coordinateur.

Mesure ai-01 du 2026-11-04 sur l'issue : les portes encore câblées sur le
seul login humain ``myia-ai-01`` sont (a) la détection de l'APPROVE dans
``merge_ready`` (testée dans test_merge_ready.py) et (b) la trappe de levée
``[OVERRIDE] lane`` de B.0, testée ici via ``LIFT_OVERRIDE_LOGINS``.

La mesure API qui fonde la sonde (2026-11-12) : ``gh pr view --json
comments,reviews`` rend l'auteur SANS champ de type (``{"login": ...}``
seul) — pour une App, le login est NU. La doctrine gh_identity interdit
d'accepter la forme nue telle quelle (un compte UTILISATEUR nommé comme le
slug de l'App passerait la borne d'auteur) : la preuve se prend à la source
REST ``users/<login>[bot]`` (``type: Bot`` = App ; 404 = utilisateur).

Les tests couvrent les trois orthographes réelles (REST suffixée, GraphQL
typée, gh-json nue résolue par sonde), les deux échecs fail-closed (sonde
muette, sonde rendant un type User), l'App d'une autre lane (jamais la voix
du siège), et l'invariant BOT_LOGINS (les deux orthographes d'un même bot
restent du bruit après normalisation).
"""

import importlib.util
import sys
from datetime import datetime, timezone
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
CHECK_PATH = HERE.parent / "check_unaddressed_nits.py"

spec = importlib.util.spec_from_file_location(
    "check_unaddressed_nits_17437", CHECK_PATH
)
mod = importlib.util.module_from_spec(spec)
sys.modules["check_unaddressed_nits_17437"] = mod
spec.loader.exec_module(mod)

APP_LOGIN_BARE = "coursia-lane-ai-01"
APP_LOGIN_REST = "coursia-lane-ai-01[bot]"


@pytest.fixture(autouse=True)
def _cache_app_vide():
    """Le cache de sonde est un etat module : chaque test part vierge."""
    mod._APP_BARE_LOGIN_CACHE.clear()
    yield
    mod._APP_BARE_LOGIN_CACHE.clear()


def at(hour: int) -> str:
    return f"2026-08-14T{hour:02d}:00:00Z"


MERGED = datetime(2026, 8, 14, 20, 0, tzinfo=timezone.utc)

# Un nit user CRLF, posterieur au reserve d'Hermes ci-dessous : le substrat
# du test de levée est celui de la section #11479 du fichier principal.
USER_NIT = {
    "author": {"login": "jsboige"},
    "createdAt": at(9),
    "body": "Attention 2 nits:\r\n- il va falloir splitter\r\n- l'attribution est fausse",
}

HERMES_REVIEW = {
    "author": {"login": "clusterManager-Myia"},
    "state": "COMMENTED", "submittedAt": at(10),
    "body": "[Hermes] COMMENT_WITH_CONCERNS — tests exécutés en local : 44/44 "
            "pass, mais 2 edge cases non couverts.",
}

OVERRIDE_BODY = (
    "[OVERRIDE] lane myia-ai-01:CoursIA — Levée de la réserve Hermes "
    "du 2026-08-17, en nommant chacun de ses points : gap 1 retiré par "
    "Hermes lui-même, gaps 2-3 reportés sur #11058."
)


def run_lift(lift_author: dict, comments=(), monkeypatch=None, gh_json_fake=None):
    """PR d'un worker, réserve posée par un tiers — la trappe OVERRIDE est
    le seul chemin de levée, et l'auteur de la levée est paramétrable."""
    if gh_json_fake is not None and monkeypatch is not None:
        monkeypatch.setattr(mod, "gh_json", gh_json_fake)
    lift = {"author": lift_author, "createdAt": at(12), "body": OVERRIDE_BODY}
    data = {
        "number": 0, "title": "t", "author": {"login": "myia-po-2026"},
        "comments": [lift, *comments], "reviews": [HERMES_REVIEW],
        "commits": [{"committedDate": at(19)}],
    }
    return mod.analyse(data, [], MERGED)


# --- la voix App du coordinateur lève, dans ses orthographes réelles ----------


def test_17437_levee_app_login_rest_leve():
    """Orthographe REST (suffixée, sans champ type) : l'App du coordinateur
    lève la réserve d'un tiers par la trappe OVERRIDE."""
    assert run_lift({"login": APP_LOGIN_REST})["blocked"] is False


def test_17437_levee_app_typbot_graphql_leve():
    """Orthographe GraphQL (login nu + ``__typename: Bot``) : la
    normalisation gh_identity reconstruit le suffixe, sans sonde."""
    assert run_lift({"login": APP_LOGIN_BARE, "__typename": "Bot"})["blocked"] is False


def test_17437_levee_app_nue_resolue_par_sonde_leve(monkeypatch):
    """Orthographe gh-json (login nu, sans type) : la sonde REST prouve le
    type Bot et la levée compte — l'angle mort mesuré par ai-01."""
    def fake_gh_json(args):
        assert args[:2] == ["api", f"users/{APP_LOGIN_BARE}[bot]"], args
        return {"type": "Bot"}
    res = run_lift({"login": APP_LOGIN_BARE}, monkeypatch=monkeypatch,
                   gh_json_fake=fake_gh_json)
    assert res["blocked"] is False


# --- fail-closed : la forme nue sans preuve ne passe jamais -------------------


def test_17437_levee_app_nue_sonde_muette_fail_closed(monkeypatch):
    """Sonde muette (crash gh / réseau) : la forme nue est conservée, donc
    refusée par la borne d'auteur — la réserve reste debout."""
    def fake_gh_json(args):
        raise RuntimeError("gh indisponible")
    res = run_lift({"login": APP_LOGIN_BARE}, monkeypatch=monkeypatch,
                   gh_json_fake=fake_gh_json)
    assert res["blocked"] is True


def test_17437_levee_app_nue_sonde_rend_user_fail_closed(monkeypatch):
    """La sonde rend un type User : un compte UTILISATEUR nommé comme le
    slug de l'App n'est pas l'App — la doctrine gh_identity tient."""
    def fake_gh_json(args):
        return {"type": "User"}
    res = run_lift({"login": APP_LOGIN_BARE}, monkeypatch=monkeypatch,
                   gh_json_fake=fake_gh_json)
    assert res["blocked"] is True


def test_17437_app_d_une_lane_worker_ne_leve_pas():
    """L'App d'une lane worker, même suffixée REST, n'est pas la voix du
    siège : la trappe OVERRIDE reste coordinateur-only."""
    res = run_lift({"login": "coursia-lane-po-2026[bot]"})
    assert res["blocked"] is True


# --- invariants du balayage : la normalisation ne change pas les filtres ------


def test_17437_bot_rest_suffixe_reste_du_bruit():
    """BOT_LOGINS couvre les DEUX orthographes : un bot rendu suffixé par la
    normalisation reste filtré comme bruit (il ne lève pas le nit user)."""
    noise = {"author": {"login": "codecov[bot]"}, "createdAt": at(12),
             "body": "Coverage: 91.2% (+0.1%)"}
    data = {
        "number": 0, "title": "t", "author": {"login": "jsboige"},
        "comments": [USER_NIT, noise], "reviews": [],
        "commits": [{"committedDate": at(19)}],
    }
    assert mod.analyse(data, [], MERGED)["blocked"] is True


def test_17437_bot_type_dans_payload_reste_du_bruit():
    """Même témoin avec la preuve de type dans le payload (REST ``type``) :
    github-actions suffixé par normalisation reste dans BOT_LOGINS."""
    noise = {"author": {"login": "github-actions", "type": "Bot"},
             "createdAt": at(12),
             "body": "Golden set: 0 diff. Variation cap: OK."}
    data = {
        "number": 0, "title": "t", "author": {"login": "jsboige"},
        "comments": [USER_NIT, noise], "reviews": [],
        "commits": [{"committedDate": at(19)}],
    }
    assert mod.analyse(data, [], MERGED)["blocked"] is True


# --- potence : le litre et la derivation ne doivent pas diverger --------------


def test_17437_litteral_app_epingle_a_la_derivation():
    """Le littéral ``coursia-lane-ai-01[bot]`` de LIFT_OVERRIDE_LOGINS vit
    sans import gh_identity (convention #22567 du gate adjoint) : ce test
    épingle le littéral à la derivation — une divergence devient un rouge,
    pas une porte silencieusement fermée."""
    assert "myia-ai-01" in mod.LIFT_OVERRIDE_LOGINS
    assert mod.gh_identity.APP_LOGIN_PREFIX + "ai-01[bot]" in (
        mod.LIFT_OVERRIDE_LOGINS
    )
    assert mod.LIFT_OVERRIDE_LOGINS == {
        "myia-ai-01", APP_LOGIN_REST,
    }
