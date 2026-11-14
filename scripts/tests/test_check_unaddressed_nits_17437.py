"""Tests #17437 — les portes d'identité App et la voix du coordinateur.

Mesure ai-01 du 2026-11-04 sur l'issue : les portes encore câblées sur le
seul login humain ``myia-ai-01`` sont (a) la détection de l'APPROVE dans
``merge_ready`` (testée dans test_merge_ready.py) et (b) la trappe de levée
``[OVERRIDE] lane`` de B.0, testée ici via ``LIFT_OVERRIDE_LOGINS``.

Arbitrage ai-01 du 2026-11-13 : ``coursia-lane-ai-01`` est nommée par
MACHINE, et ai-01 porte deux lanes. Sa clé privée vit dans le clone
(``.secrets/github-apps/coursia-lane-ai-01.pem``) : la lane worker sœur
``myia-ai-01:CoursIA-2`` la lit et forge le même jeton. L'App ne peut donc
pas porter la voix du coordinateur — les tests de levée par l'App sont
inversés en conséquence ; une App propre à la lane coordinatrice est le
préalable.

Relecture ai-01 du 2026-11-12 : la preuve d'identité est le TYPE PORTÉ PAR
LA LIGNE elle-même (REST ``user.type``, GraphQL ``author.__typename`` —
l'overlay ``_typed_author_surfaces``), JAMAIS une sonde
``users/<login>[bot]`` : la sonde prouve que l'App EXISTE, pas que
l'AUTEUR de la ligne est l'App. Une ligne nue sans type est refusée ; le
suffixe ``[bot]`` résisté par GitHub aux Apps reste une preuve structurelle
en soi. Les tests couvrent : l'orthographe suffixée (CLI), l'orthographe
GraphQL typée, la forme nue refusée même quand l'App existe, l'homonyme
UTILISATEUR typé ``User`` refusé, l'App d'une autre lane (point Hermes),
l'auteur de PR typé pour la trappe #13495, et les invariants BOT_LOGINS.
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


def run_lift(lift_author: dict, comments=(), monkeypatch=None,
             gh_json_fake=None, pr_author=None):
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
        "number": 0, "title": "t",
        "author": pr_author or {"login": "myia-po-2026"},
        "comments": [lift, *comments], "reviews": [HERMES_REVIEW],
        "commits": [{"committedDate": at(19)}],
    }
    res = mod.analyse(data, [], MERGED)
    res["_probe_calls"] = probe_calls
    return res


# --- la voix App du coordinateur lève, dans ses orthographes réelles ----------


def test_17437_levee_app_machine_ne_leve_pas():
    """Arbitrage ai-01 du 2026-11-13 : l'App ``coursia-lane-ai-01`` est
    nommée par MACHINE, et ai-01 porte deux lanes. Sa clé privée vit dans le
    clone (``.secrets/github-apps/coursia-lane-ai-01.pem``) : la lane worker
    sœur ``myia-ai-01:CoursIA-2`` lit le même fichier et forge le même jeton
    d'installation. L'App ne peut donc pas porter la voix du coordinateur —
    un ``[OVERRIDE]`` de CoursIA-2 vaudrait celui du coordinateur, ce que la
    borne #12737/#12836 interdit. Une App PROPRE à la lane coordinateur est
    le préalable."""
    res = run_lift({"login": APP_LOGIN_REST})
    assert res["blocked"] is True
    assert any("n'est pas un compte de levée" in o["why"]
               for o in res.get("ignored_overrides", ()))


def test_17437_levee_app_typbot_graphql_ne_leve_pas():
    """Même arbitrage, orthographe GraphQL typée : la normalisation ``Bot``
    du préfixe de machine ne suffit pas — une forme typée juste ne fait pas
    une voix coordinatrice."""
    res = run_lift({"login": APP_LOGIN_BARE, "__typename": "Bot"})
    assert res["blocked"] is True


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


def test_17437_litteral_app_epingle_au_retrait():
    """La potence change de sens avec l'arbitrage du 2026-11-13 : le test
    épingle désormais l'ABSENCE de l'App de machine dans la trappe. Si une
    édition future y ajoute ``coursia-lane-ai-01[bot]`` sans App propre à la
    lane coordinateur, ce rouge le dit au lieu de laisser la porte s'ouvrir
    en silence."""
    assert mod.LIFT_OVERRIDE_LOGINS == {"myia-ai-01"}
    assert mod.gh_identity.APP_LOGIN_PREFIX + "ai-01[bot]" not in (
        mod.LIFT_OVERRIDE_LOGINS
    )


def test_17437_auteur_pr_type_app_normalise_rest():
    """L'auteur de la PR, typé à la source (``pullRequest.author`` de
    l'overlay), prend l'orthographe REST : une App sans suffixe côté CLI
    devient ``coursia-lane-ai-01[bot]``. Sans cette normalisation, la trappe
    #13495 (``lift_author == pr_author``) ne voit jamais l'égalité quand la
    PR et la levée sont émises par la même App."""
    assert mod._author_login(
        {"author": {"login": APP_LOGIN_BARE, "__typename": "Bot"}}
    ) == APP_LOGIN_REST


def test_17437_pr_sous_app_levee_meme_app_bloquee():
    """Scénario exact de la relecture ai-01 du 2026-11-13 : PR ouverte sous
    ``coursia-lane-ai-01`` (auteur CLI non typé, donc nu), remarque Hermes,
    ``[OVERRIDE]`` de la même App typée par la ligne. Le gate reste fermé.

    Sous l'arbitrage courant deux barrières le ferment : l'App n'est pas un
    compte de levée, et l'auteur de la PR se lit typé (l'overlay écrase la
    forme CLI) — la trappe #13495 voit l'égalité si l'App entrait un jour
    dans ``LIFT_OVERRIDE_LOGINS``."""
    res = run_lift(
        {"login": APP_LOGIN_BARE, "__typename": "Bot"},
        pr_author={"login": APP_LOGIN_BARE},  # forme CLI nue, écrasée ailleurs
    )
    assert res["blocked"] is True


def test_17437_trappe_13495_mord_avec_auteur_pr_type(monkeypatch):
    """Mécanisme isolé, pour le jour où une App de lane coordinateur existe :
    l'auteur de la PR se lit TYPÉ, ``lift_author == pr_author`` voit
    l'égalité, et la note #13495 part au lieu de laisser l'override
    s'appliquer en silence."""
    monkeypatch.setattr(
        mod, "LIFT_OVERRIDE_LOGINS",
        {"myia-ai-01", APP_LOGIN_REST},
    )
    res = run_lift(
        {"login": APP_LOGIN_BARE, "__typename": "Bot"},
        pr_author={"login": APP_LOGIN_BARE, "__typename": "Bot"},
    )
    assert res["blocked"] is True
    assert any("est l'auteur de la PR" in o["why"]
               for o in res.get("ignored_overrides", ()))


# --- pagination de la surface typee (#17437 relecture 2026-11-13) ------------
#
# Le defaut mesure par ai-01 : ``first:100`` rend les 100 lignes les PLUS
# ANCIENNES, et ``data.update`` remplace la surface CLI COMPLETE. Sur une PR
# de plus de 100 commentaires, une reserve RECENTE sortait de l'analyse et
# B.0 rendait rc=0 — la porte s'ouvrait. Ces tests epinglent la pagination.


def _page(nodes: list[dict], has_next: bool, cursor: str | None) -> dict:
    return {"pageInfo": {"hasNextPage": has_next, "endCursor": cursor},
            "nodes": nodes}


def _graphql_page(comments: dict, reviews: dict) -> dict:
    return {"data": {"repository": {"pullRequest": {
        "comments": comments, "reviews": reviews}}}}


def _user_line(login: str, body: str, hour: int) -> dict:
    return {"author": {"login": login, "__typename": "User"},
            "body": body, "createdAt": at(hour)}


RESERVE_PAGE_2 = (
    "Attention 2 nits:\r\n- il va falloir splitter\r\n"
    "- l'attribution est fausse"
)


def _pages_avec_reserve_page_2() -> list[dict]:
    """Page 1 : 100 commentaires anodins (hasNextPage). Page 2 : la reserve."""
    benin = _user_line("jsboige", "note anodine", 1)
    reserve = _user_line("jsboige", RESERVE_PAGE_2, 9)
    return [
        _graphql_page(_page([benin] * 100, True, "c1"),
                      _page([], False, None)),
        _graphql_page(_page([reserve], False, "c2"),
                      _page([], False, None)),
    ]


def test_17437_surface_typee_pagine_page_2(monkeypatch):
    """La page 2 est reellement demandee (curseur ``cAfter=c1``) et ses
    lignes sont rendues : 101 commentaires, pas 100."""
    pages = _pages_avec_reserve_page_2()
    calls: list[list[str]] = []

    def fake(args):
        calls.append(list(args))
        return pages[len(calls) - 1]

    monkeypatch.setattr(mod, "gh_json", fake)
    out = mod._typed_author_surfaces(1)

    assert len(out["comments"]) == 101
    assert out["comments"][-1]["body"] == RESERVE_PAGE_2
    assert len(calls) == 2
    assert "cAfter=c1" in calls[1]
    assert "cAfter=c1" not in calls[0]


def test_17437_reserve_en_page_2_bloque(monkeypatch):
    """LE test exige par la relecture : la reserve postee APRES la page 1
    est analysee. Sans pagination, la surface remplacee s'arretait a la
    page 1 et B.0 rendait rc=0 — la porte s'ouvrait."""
    pages = _pages_avec_reserve_page_2()
    calls: list[list[str]] = []

    def fake(args):
        calls.append(list(args))
        return pages[len(calls) - 1]

    monkeypatch.setattr(mod, "gh_json", fake)
    data = {
        "number": 1, "title": "t", "author": {"login": "jsboige"},
        "comments": [], "reviews": [],
        "commits": [{"committedDate": at(19)}],
    }
    data.update(mod._typed_author_surfaces(1))
    assert mod.analyse(data, [], MERGED)["blocked"] is True


def test_17437_surface_typee_echec_page_2_rend_vide(monkeypatch):
    """Echec en page 2 : la surface rend un dict VIDE (jamais une surface
    partielle qui remplacerait la surface CLI complete). Fail-closed."""
    pages = _pages_avec_reserve_page_2()
    state = {"n": 0}

    def fake(args):
        state["n"] += 1
        if state["n"] == 1:
            return pages[0]
        raise RuntimeError("gh muet en page 2")

    monkeypatch.setattr(mod, "gh_json", fake)
    assert mod._typed_author_surfaces(1) == {}


def test_17437_surface_typee_curseur_fige_rend_vide(monkeypatch):
    """``hasNextPage`` vrai mais curseur qui n'avance pas : on s'arrete au
    lieu de boucler, et on rend vide (fail-closed)."""
    benin = _user_line("jsboige", "note", 1)

    def fake(args):
        return _graphql_page(_page([benin], True, "c1"),
                             _page([], False, None))

    monkeypatch.setattr(mod, "gh_json", fake)
    assert mod._typed_author_surfaces(1) == {}


# --- review_threads : la 3e surface pagine aussi (relecture 2026-11-13) ------


def _thread(resolved: bool, body: str) -> dict:
    return {"isResolved": resolved, "isOutdated": False,
            "path": "a.py", "line": 1,
            "comments": {"nodes": [
                {"author": {"login": "clusterManager-Myia",
                            "__typename": "Bot"},
                 "body": body, "createdAt": at(9)}]}}


def _threads_page(nodes: list[dict], has_next: bool, cursor: str | None) -> dict:
    return {"data": {"repository": {"pullRequest": {"reviewThreads": {
        "pageInfo": {"hasNextPage": has_next, "endCursor": cursor},
        "nodes": nodes}}}}}


def test_17437_review_threads_pagine_au_dela_de_100(monkeypatch):
    """Meme classe de troncature que le point du 13/11, sur la 3e surface :
    la page 2 est demandee (curseur ``tAfter``) et son thread non resolu
    apparait. Sans pagination, les 100 threads les plus anciens seulement
    etaient lus et le non-resolu posterieur sortait de l'analyse."""
    pages = [
        _threads_page([_thread(True, "ok")] * 100, True, "t1"),
        _threads_page([_thread(False, "reste a faire")], False, "t2"),
    ]
    calls: list[list[str]] = []

    def fake(args):
        calls.append(list(args))
        return pages[len(calls) - 1]

    monkeypatch.setattr(mod, "gh_json", fake)
    out = mod.review_threads(1)

    assert len(out) == 101
    assert out[-1]["resolved"] is False
    assert out[-1]["body"] == "reste a faire"
    assert "tAfter=t1" in calls[1]
    assert "tAfter=t1" not in calls[0]


def test_17437_review_threads_curseur_fige_rend_le_collecte(monkeypatch):
    """Curseur qui n'avance pas : on s'arrete (pas de boucle) et on rend ce
    qui a ete collecte, avec un avertissement — un thread deja lu ne se perd
    pas parce que la page suivante est inatteignable. La page figee est lue
    deux fois (le gel n'est detectable qu'apres la seconde lecture), donc
    deux entrees identiques : le contrat est « ca termine et ca rend »,
    jamais « ca boucle »."""
    page = _threads_page([_thread(False, "x")], True, "t1")

    monkeypatch.setattr(mod, "gh_json", lambda args: page)
    out = mod.review_threads(1)
    assert len(out) == 2
    assert all(not t["resolved"] for t in out)
