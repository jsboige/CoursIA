"""Tests du repli REST de la sonde de claims (#17038, residu du 2026-10-09).

Contexte : sous panne du bucket GraphQL du compte partage (403 secondary
rate-limit), la lecture de claim -- `_gh_issue_comments` dans
`check_lane_claim.py`, appelee par le picker via subprocess -- mourait sans
bascule, et le champ ``cache.claims`` du tirage rendait ``N/N en ERROR``
tout en servant les candidats sous le vocabulaire du libre.

Acceptance visee (residu mesure, c. 2026-10-09T15:19:55Z) :
1. quand ``gh issue view`` (GraphQL) echoue, la lecture bascule sur
   ``gh api repos/...`` (REST, quota distinct) et rend le MEME verdict ;
2. quand les deux transports tombent, l'erreur nomme les DEUX et porte le
   vocabulaire ``NON MESURABLE`` -- jamais celui d'un verdict libre ;
3. le mapping REST -> forme ``gh issue view --json`` est exact pour les
   champs que le parser lit (``body``, ``author.login``, ``createdAt``) ;
4. la sonde unitaire de tete du picker (``latest_claim_stamp``) herite du
   meme repli.
"""

import subprocess
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import check_lane_claim as clc  # noqa: E402

# Capture AVANT le fixture autouse : le vrai corps, pour les tests du slug.
_REAL_REPO_SLUG = clc._repo_slug

SLUG = "jsboige/CoursIA"

REST_ISSUE = {
    "number": 17038,
    "title": "tooling(picker,#16765): fallback REST",
    "labels": [{"id": 1, "name": "EPIC", "color": "3E4B9E"}],
}

# Champs REST natifs (created_at, user.login, html_url) : le mapping doit
# les traduire vers la forme gh (createdAt, author.login).
REST_COMMENTS = [
    {
        "body": "[CLAIMED] lane myia-po-2024:CoursIA -- initial",
        "created_at": "2026-10-01T10:00:00Z",
        "user": {"login": "jsboige"},
        "html_url": f"https://github.com/{SLUG}/issues/17038#comment-1",
    },
    {
        "body": "[RELEASED] lane myia-po-2024:CoursIA -- rendu",
        "created_at": "2026-10-02T10:00:00Z",
        "user": {"login": "jsboige"},
        "html_url": f"https://github.com/{SLUG}/issues/17038#comment-2",
    },
]


class _Proc:
    """Stand-in de subprocess.CompletedProcess."""

    def __init__(self, returncode=0, stdout="", stderr=""):
        self.returncode = returncode
        self.stdout = stdout
        self.stderr = stderr


def _fake_run(routing):
    """subprocess.run factice : route sur argv[0:2] et le chemin d'API."""
    def run(cmd, *a, **kw):
        argv = list(cmd)
        if argv[:2] == ["gh", "issue"] and "view" in argv:
            return routing.get("issue_view")()
        if argv[:2] == ["gh", "api"]:
            path = argv[-1]
            if "/comments" in path:
                return routing.get("comments")()
            return routing.get("issue")()
        return _Proc(returncode=1, stderr=f"unexpected call {argv}")
    return run


def _ok(payload):
    import json as _json
    return lambda: _Proc(stdout=_json.dumps(payload))


def _graphql_dead():
    return _Proc(returncode=1,
                 stderr="GraphQL: API rate limit exceeded for installation.")


@pytest.fixture(autouse=True)
def _pin_slug(monkeypatch):
    monkeypatch.setattr(clc, "_repo_slug", lambda: SLUG)


def test_fallback_rest_sert_le_meme_contenu(monkeypatch, capsys):
    """GraphQL mort -> REST sert la charge ; banniere NOMME le transport."""
    monkeypatch.setattr(
        clc.subprocess, "run",
        _fake_run({"issue_view": _graphql_dead,
                   "issue": _ok(REST_ISSUE),
                   "comments": _ok(REST_COMMENTS)}))
    payload = clc._gh_issue_comments("17038")
    assert payload["number"] == 17038
    assert payload["title"] == REST_ISSUE["title"]
    assert [lb["name"] for lb in payload["labels"]] == ["EPIC"]
    assert [c["createdAt"] for c in payload["comments"]] == [
        "2026-10-01T10:00:00Z", "2026-10-02T10:00:00Z"]
    assert payload["comments"][0]["author"] == {"login": "jsboige"}
    err = capsys.readouterr().err
    assert "bascule REST" in err
    assert "GraphQL" in err


def test_deux_transports_morts_message_non_mesurable(monkeypatch):
    """Les deux morts -> l'erreur porte NON MESURABLE, jamais 'libre'."""
    rest_dead = _Proc(returncode=1, stderr="gh api: connection refused")
    monkeypatch.setattr(
        clc.subprocess, "run",
        _fake_run({"issue_view": _graphql_dead,
                   "issue": lambda: rest_dead,
                   "comments": lambda: rest_dead}))
    with pytest.raises(RuntimeError) as excinfo:
        clc._gh_issue_comments("17038")
    msg = str(excinfo.value)
    assert "GraphQL puis REST" in msg
    assert "NON MESURABLE" in msg


def test_mapping_rend_un_verdict_reel_depuis_rest(monkeypatch):
    """Controle positif de bout en bout : le payload REST reduit en events.

    C'est la preuve que le repli n'est pas une lecture morte : la grammaire
    de l'organe (open puis close du meme lane) s'applique telle quelle sur
    le payload mappe, et le verdict final est un etat actif VIDE (claim
    ouvert puis rendu).
    """
    monkeypatch.setattr(
        clc.subprocess, "run",
        _fake_run({"issue_view": _graphql_dead,
                   "issue": _ok(REST_ISSUE),
                   "comments": _ok(REST_COMMENTS)}))
    payload = clc._gh_issue_comments("17038")
    events = clc._sort_events(payload)
    lanes = [ev.lane for ev in events if ev.lane]
    assert lanes == ["myia-po-2024:CoursIA", "myia-po-2024:CoursIA"]
    active, unattributed = clc.compute_active_claims(events)
    assert active == {} or "myia-po-2024:CoursIA" not in active
    assert not unattributed


def test_reste_en_forme_quand_graphql_vit(monkeypatch):
    """Chemin nominal inchange : le repli ne perturbe pas la voie GraphQL."""
    gh_shape = {
        "number": 17038, "title": "t", "labels": [{"name": "EPIC"}],
        "comments": [{"body": "prose", "createdAt": "2026-10-01T10:00:00Z",
                      "author": {"login": "x"}, "url": "u"}],
    }
    monkeypatch.setattr(
        clc.subprocess, "run",
        _fake_run({"issue_view": _ok(gh_shape)}))
    assert clc._gh_issue_comments("17038") == gh_shape


def _real_slug_from(url, monkeypatch):
    """Restaure le vrai _repo_slug et stub l'appel git sous-jacent."""
    import check_lane_claim as _clc
    real = _REAL_REPO_SLUG
    monkeypatch.setattr(_clc, "_repo_slug", real)
    monkeypatch.setattr(
        _clc.subprocess, "run",
        lambda *a, **kw: _Proc(stdout=url))
    return real()


def test_repo_slug_formes_d_url(monkeypatch):
    """ssh, https, .git, slash final : le slug est owner/repo dans tous les cas."""
    nl = chr(10)
    for url, expected in [
        ("git@github.com:jsboige/CoursIA.git" + nl, "jsboige/CoursIA"),
        ("https://github.com/jsboige/CoursIA.git" + nl, "jsboige/CoursIA"),
        ("https://github.com/jsboige/CoursIA/" + nl, "jsboige/CoursIA"),
        ("git@github.com:jsboige/CoursIA" + nl, "jsboige/CoursIA"),
    ]:
        assert _real_slug_from(url, monkeypatch) == expected, url


def test_repo_slug_illisible_leve(monkeypatch):
    with pytest.raises(RuntimeError):
        _real_slug_from("pas-un-slug" + chr(10), monkeypatch)


def test_sonde_de_tete_du_picker_herite_du_repli(monkeypatch, capsys):
    """`latest_claim_stamp` (repli unitaire du bulk GraphQL) bascule aussi.

    #17038 -- sous panne, le bulk meurt et la sonde unitaire EST le repli
    designe ; si elle mourait aussi, la tete de tapis perdrait ses stamps
    et les issues livrees resteraient collees en tete.
    """
    import pick_idle_grain as pig

    monkeypatch.setattr(
        clc.subprocess, "run",
        _fake_run({"issue_view": _graphql_dead,
                   "issue": _ok(REST_ISSUE),
                   "comments": _ok(REST_COMMENTS)}))
    # La sonde du picker appelle `gh issue view --repo ...` (sa propre
    # signature) : le meme routing s'applique, puis le repli importe
    # `_rest_issue_payload` de l'organe -- les appels REST passent par le
    # module de l'organe, donc par le stub ci-dessus.
    stamp = pig.latest_claim_stamp(17038)
    assert stamp == "2026-10-02T10:00:00Z"
    assert "sonde de tete" in capsys.readouterr().err


def _boom(*_a, **_k):
    """`_repo_slug` rendu MORT : le repli ne doit pas le consulter."""
    raise AssertionError(
        "_repo_slug consulte alors que la cible etait epinglee (repo=)")


def test_rest_issue_payload_epargne_repo_du_cwd(monkeypatch):
    """`repo=` court-circuite `_repo_slug` : la cible REST est celle demandee.

    Reserve NanoClaw (2026-10-10) : un appelant qui epingle sa cible cote
    GraphQL ne doit pas la perdre cote REST.
    """
    seen = []

    def _run(cmd, *a, **kw):
        argv = list(cmd)
        seen.append(argv)
        return _ok(REST_COMMENTS)() if "/comments" in argv[-1] else _ok(REST_ISSUE)()

    monkeypatch.setattr(clc, "_repo_slug", _boom)
    monkeypatch.setattr(clc.subprocess, "run", _run)
    payload = clc._rest_issue_payload("17038", repo="autre/depot")
    assert payload["number"] == 17038
    assert seen, "aucun appel REST emis"
    assert all(a[-1].startswith("repos/autre/depot/") for a in seen), seen


def test_sonde_de_tete_du_picker_epingle_le_repo_sur_le_repli(
        monkeypatch, capsys):
    """Les deux transports du picker visent le MEME depot.

    Reserve NanoClaw (2026-10-10) sur #20248 : la voie GraphQL passe
    `--repo REPO`, independante du cwd ; si le repli REST inferait le slug du
    remote `origin` du cwd, un picker lance depuis un worktree ou un clone
    etranger servirait les claims de cet autre depot -- silencieusement, et
    sans mourir. `_repo_slug` est rendu MORT : le repli ne doit pas le lire.
    """
    import pick_idle_grain as pig

    seen = []

    def _run(cmd, *a, **kw):
        argv = list(cmd)
        if argv[:2] == ["gh", "issue"]:
            return _graphql_dead()
        seen.append(argv)
        return _ok(REST_COMMENTS)() if "/comments" in argv[-1] else _ok(REST_ISSUE)()

    monkeypatch.setattr(clc, "_repo_slug", _boom)
    monkeypatch.setattr(clc.subprocess, "run", _run)
    stamp = pig.latest_claim_stamp(17038)
    assert stamp == "2026-10-02T10:00:00Z"
    assert seen, "le repli REST n'a pas ete appele"
    assert all(a[-1].startswith(f"repos/{SLUG}/") for a in seen), seen
    assert "sonde de tete" in capsys.readouterr().err
