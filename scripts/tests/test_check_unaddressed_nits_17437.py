"""Tests #17437 — la levée B.0 sous identité GitHub App du coordinateur.

Mesure ai-01 du 2026-11-04 sur l'issue : les portes encore câblées sur le
seul login humain ``myia-ai-01`` sont (a) la détection de l'APPROVE dans
``merge_ready`` (testée dans test_merge_ready.py) et (b) la trappe de levée
``[OVERRIDE] lane`` de B.0, testée ici via ``LIFT_OVERRIDE_LOGINS``.

Relecture ai-01 du 2026-11-12 : la preuve d'identité est le TYPE PORTÉ PAR
LA LIGNE elle-même (REST ``user.type``, GraphQL ``author.__typename`` —
l'overlay ``_typed_author_surfaces``), JAMAIS une sonde
``users/<login>[bot]`` : la sonde prouve que l'App EXISTE, pas que
l'AUTEUR de la ligne est l'App. Une ligne nue sans type est refusée ; le
suffixe ``[bot]`` résisté par GitHub aux Apps reste une preuve structurelle
en soi. Les tests couvrent : l'orthographe suffixée (CLI), l'orthographe
GraphQL typée, la forme nue refusée même quand l'App existe, l'homonyme
UTILISATEUR typé ``User`` refusé, l'App d'une autre lane (point Hermes),
et les invariants BOT_LOGINS.
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
    probe_calls: list[list[str]] = []

    if gh_json_fake is not None and monkeypatch is not None:
        def fake_gh_json(args):
            probe_calls.append(list(args))
            return gh_json_fake(args)
        monkeypatch.setattr(mod, "gh_json", fake_gh_json)
    lift = {"author": lift_author, "createdAt": at(12), "body": OVERRIDE_BODY}
    data = {
        "number": 0, "title": "t", "author": {"login": "myia-po-2026"},
        "comments": [lift, *comments], "reviews": [HERMES_REVIEW],
        "commits": [{"committedDate": at(19)}],
    }
    res = mod.analyse(data, [], MERGED)
    res["_probe_calls"] = probe_calls
    return res


# --- la voix App du coordinateur lève, dans ses orthographes réelles ----------


def test_17437_levee_app_login_rest_leve():
    """Orthographe suffixée (celle du suffixe ``[bot]`` réservé par GitHub
    aux Apps — preuve structurelle, aucun utilisateur ne le porte) : l'App
    du coordinateur lève la réserve d'un tiers par la trappe OVERRIDE."""
    assert run_lift({"login": APP_LOGIN_REST})["blocked"] is False


def test_17437_levee_app_typbot_graphql_leve():
    """Orthographe GraphQL de l'overlay typé (login nu +
    ``__typename: Bot``) : la normalisation gh_identity reconstruit le
    suffixe — la preuve de type vient de la ligne."""
    assert run_lift({"login": APP_LOGIN_BARE, "__typename": "Bot"})["blocked"] is False


# --- fail-closed : la forme nue sans TYPE SUR LA LIGNE ne passe jamais -------


def test_17437_levee_app_nue_sans_type_refuse_meme_sonde_scriptable(monkeypatch):
    """LE test manquant de la relecture ai-01 : une ligne
    ``{"login": "coursia-lane-ai-01"}`` sans type, la sonde étant scriptée
    à ``Bot`` (l'App existe). Elle ne doit NI lever NI compter — et la
    sonde n'est même plus appelée : la preuve est le type de la ligne, pas
    l'existence de l'App."""
    res = run_lift(
        {"login": APP_LOGIN_BARE},
        monkeypatch=monkeypatch,
        gh_json_fake=lambda args: {"type": "Bot"},
    )
    assert res["blocked"] is True
    # la sonde a disparu : aucun appel users/ n'a été tenté
    assert res["_probe_calls"] == []


def test_17437_levee_homonyme_utilisateur_type_user_ne_leve_pas():
    """L'homonyme UTILISATEUR du slug, typé ``User`` par l'overlay GraphQL
    (le vrai visage de l'attaque mesurée) : la normalisation laisse le
    login nu, il échoue la borne suffixée — la doctrine tient, preuve de
    type à l'appui."""
    res = run_lift({"login": APP_LOGIN_BARE, "__typename": "User"})
    assert res["blocked"] is True


def test_17437_app_d_une_lane_worker_ne_leve_pas():
    """Point Hermes : l'App d'une autre lane, même TYPÉE ``Bot`` par
    l'overlay, n'est pas la voix du siège — la trappe OVERRIDE reste
    coordinateur-only."""
    res = run_lift({"login": "coursia-lane-po-2026", "__typename": "Bot"})
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
