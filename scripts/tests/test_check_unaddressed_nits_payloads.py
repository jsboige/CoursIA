"""Projections du transport de B.0 (#22757)."""
import importlib.util
import json
import sys
from datetime import datetime, timezone
from pathlib import Path


SCRIPT = Path(__file__).resolve().parents[1] / "check_unaddressed_nits.py"
spec = importlib.util.spec_from_file_location("check_unaddressed_nits_payloads", SCRIPT)
mod = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = mod
spec.loader.exec_module(mod)


def test_pr_view_projection_preserve_le_verdict_et_reduit_le_payload():
    raw = {
        "number": 41,
        "title": "PR de test",
        "body": "",
        "mergedAt": "2026-08-14T20:00:00Z",
        "author": {"login": "jsboige", "avatarUrl": "large"},
        "comments": [{
            "author": {"login": "jsboige", "avatarUrl": "large"},
            "createdAt": "2026-08-14T09:00:00Z",
            "body": "Attention 2 nits:\r\n- splitter\r\n- attribution",
            "reactions": {"totalCount": 12, "nodes": ["bruit"] * 30},
        }, {
            "author": {"login": "jsboige", "avatarUrl": "large"},
            "createdAt": "2026-08-14T12:00:00Z",
            "body": "Les 2 nits sont adresses.",
            "reactions": {"totalCount": 12, "nodes": ["bruit"] * 30},
        }],
        "reviews": [{
            "author": {"login": "jsboige", "avatarUrl": "large"},
            "submittedAt": "2026-08-14T13:00:00Z",
            "body": "Approved",
            "state": "APPROVED",
            "id": "PRR_opaque",
            "commit": {"oid": "a" * 40},
        }],
        "commits": [{
            "oid": "a" * 40,
            "committedDate": "2026-08-14T19:00:00Z",
            "messageBody": "large body" * 500,
            "authors": [{"login": "jsboige"}] * 30,
        }],
        "url": "https://example.invalid/pull/41",
        "state": "MERGED",
        "headRefOid": "a" * 40,
    }
    args = ["pr", "view", "41", "--json", "fields"]
    projected = mod._project_gh_payload(args, raw)

    before = mod.analyse(raw, [], datetime(2026, 8, 14, 20, tzinfo=timezone.utc))
    after = mod.analyse(projected, [], datetime(2026, 8, 14, 20, tzinfo=timezone.utc))
    assert after == before
    assert before["blocked"] is False
    assert len(json.dumps(projected)) < len(json.dumps(raw))
    assert projected["comments"][0]["body"] == raw["comments"][0]["body"]
    assert projected["commits"] == [{"oid": "a" * 40,
                                     "committedDate": "2026-08-14T19:00:00Z"}]

    unresolved = dict(raw, comments=raw["comments"][:1])
    unresolved_projection = mod._project_gh_payload(args, unresolved)
    unresolved_before = mod.analyse(
        unresolved, [], datetime(2026, 8, 14, 20, tzinfo=timezone.utc))
    unresolved_after = mod.analyse(
        unresolved_projection, [], datetime(2026, 8, 14, 20, tzinfo=timezone.utc))
    assert unresolved_before["blocked"] is True
    assert unresolved_after == unresolved_before


def test_gh_json_projette_avant_retour_au_cache(monkeypatch):
    raw = {
        "number": 41,
        "comments": [{"author": {"login": "user", "name": "long"},
                      "body": "nit", "createdAt": "date", "reactions": [1]}],
        "reviews": [], "commits": [],
    }

    class Completed:
        stdout = json.dumps(raw)

    monkeypatch.setattr(mod.subprocess, "run", lambda *a, **k: Completed())
    result = mod.gh_json(["pr", "view", "41", "--json", "comments,reviews,commits"])
    assert result["comments"] == [{
        "author": {"login": "user"}, "body": "nit", "createdAt": "date"}]


def test_projections_rest_conservent_les_preuves_utilisees():
    commit = {
        "commit": {"message": "titre\ncorps", "tree": {"sha": "tree"},
                   "author": {"name": "bruit"}},
        "files": [{"filename": "x.py", "sha": "blob", "status": "modified",
                   "previous_filename": "old.py",
                   "patch": "@@ -1,0 +1,3 @@\n+" + "bruit " * 100
                           + "\n+def preuve():\n+" + "bruit " * 100
                           + "\n+++ autre/fichier.py\n+class Exemple:",
                   "additions": 1, "changes": 2}],
        "stats": {"total": 2},
    }
    projected_commit = mod._project_gh_payload(
        ["api", "repos/jsboige/CoursIA/commits/sha"], commit)
    assert projected_commit == {
        "commit": {"message": "titre", "tree": {"sha": "tree"}},
        "files": [{"filename": "x.py", "sha": "blob", "status": "modified",
                   "previous_filename": "old.py",
                   "patch": "+def preuve():\n+class Exemple:"}],
    }
    assert mod._introduced_symbols({
        "x.py": commit["files"][0]["patch"]}) == mod._introduced_symbols({
            "x.py": projected_commit["files"][0]["patch"]})

    tree = {"truncated": False, "tree": [{"path": "x.py", "sha": "blob",
                                           "type": "blob", "mode": "100644"}]}
    assert mod._project_gh_payload(
        ["api", "repos/jsboige/CoursIA/git/trees/tree?recursive=1"], tree) == {
            "truncated": False,
            "tree": [{"path": "x.py", "sha": "blob", "type": "blob"}],
        }

    reviews = [{"id": 7, "user": {"login": "reviewer", "name": "long"},
                "body": "ignored"}]
    assert mod._project_gh_payload(
        ["api", "repos/jsboige/CoursIA/pulls/41/reviews", "--paginate"], reviews) == [
            {"id": 7, "user": {"login": "reviewer"}}]
    timeline = [{"event": "review_dismissed",
                 "actor": {"login": "other", "avatar_url": "long"},
                 "dismissed_review": {"review_id": 7, "state": "COMMENTED"},
                 "created_at": "date"}]
    assert mod._project_gh_payload(
        ["api", "repos/jsboige/CoursIA/issues/41/timeline", "--paginate"],
        timeline) == [{"event": "review_dismissed", "actor": {"login": "other"},
                       "dismissed_review": {"review_id": 7}}]


def test_projection_pulls_commits_conserve_sha_et_les_deux_dates():
    # #17315 : _pr_commits_rest ne lit que sha, commit.author.date et
    # commit.committer.date. La projection doit reproduire EXACTEMENT
    # cette normalisation, sur la forme slurp (liste de pages) comme sur
    # la page unique.
    raw_pages = [
        [{
            "sha": "a" * 40,
            "commit": {
                "message": "message long " * 50,
                "author": {"name": "bruit", "email": "x", "date": "2026-11-01T10:00:00Z"},
                "committer": {"name": "bruit", "email": "x", "date": "2026-11-01T11:00:00Z"},
                "tree": {"sha": "t" * 40}, "verification": {"verified": False},
            },
            "parents": [{"sha": "b" * 40}], "html_url": "bruit",
        }, {
            "sha": "c" * 40,
            "commit": {
                "author": {"date": None},
                "committer": {"date": "2026-11-02T09:00:00Z"},
            },
        }],
    ]

    def normalize(pages):
        flat = []
        for page in pages:
            flat.extend(page if isinstance(page, list) else [page])
        return [{"oid": c.get("sha") or "",
                 "committedDate": (c.get("commit") or {}).get("committer", {}).get("date"),
                 "authoredDate": (c.get("commit") or {}).get("author", {}).get("date")}
                for c in flat]

    projected = mod._project_gh_payload(
        ["api", "repos/jsboige/CoursIA/pulls/41/commits", "--paginate", "--slurp"],
        raw_pages)
    assert projected == [[
        {"sha": "a" * 40,
         "commit": {"author": {"date": "2026-11-01T10:00:00Z"},
                    "committer": {"date": "2026-11-01T11:00:00Z"}}},
        {"sha": "c" * 40,
         "commit": {"author": {"date": None},
                    "committer": {"date": "2026-11-02T09:00:00Z"}}},
    ]]
    assert normalize(projected) == normalize(raw_pages)


def test_projection_issue_unique_conserve_le_contrat_issueinfo():
    # #13725 : le discriminant PR-vs-issue est la PRESENCE de la cle
    # `pull_request`. #14218 : voie 3 lit title et body. Tout le reste
    # (~40 champs de presentation REST) est du transport mort.
    raw = {
        "number": 19742, "state": "open",
        "created_at": "2026-10-07T08:00:00Z",
        "title": "Epic Origami", "body": "corps " + "long " * 4000,
        "labels": [{"name": "l%d" % i} for i in range(10)],
        "assignees": [{"login": "a"}] * 5, "reactions": {"total_count": 99},
        "milestone": {"title": "M"}, "comments": 42, "locked": False,
    }
    projected = mod._project_gh_payload(
        ["api", "repos/jsboige/CoursIA/issues/19742"], raw)
    assert set(projected) == {"state", "created_at", "title", "body"}
    assert projected["body"] == raw["body"]
    info_raw = mod.IssueInfo(raw)
    info_proj = mod.IssueInfo(projected)
    assert (info_proj.state, info_proj.created_at, info_proj.title,
            info_proj.body) == (info_raw.state, info_raw.created_at,
                                info_raw.title, info_raw.body)

    pr_payload = dict(raw, pull_request={"url": "https://example.invalid/x",
                                         "html_url": "bruit"})
    projected_pr = mod._project_gh_payload(
        ["api", "repos/jsboige/CoursIA/issues/19742"], pr_payload)
    assert "pull_request" in projected_pr  # le discriminant survit
    assert projected_pr["pull_request"] == {"url": "https://example.invalid/x"}
    assert mod._gh_fetch_issue.__doc__  # symbole vivant, garde de typo

    # les endpoints voisins ne sont PAS captures par la branche issue seule :
    # /timeline reste servi par SA branche (event/actor/dismissed_review),
    # jamais par la projection issue (aucune cle state/body n'apparait).
    timeline = [{"event": "cross-referenced", "created_at": "date"}]
    assert mod._project_gh_payload(
        ["api", "repos/jsboige/CoursIA/issues/19742/timeline"], timeline) == [
            {"event": "cross-referenced"}]


def test_projection_blob_garde_le_content():
    # #22757 : seul `content` (base64) est decode par fetch ; le reste est
    # du transport mort pour l'organe.
    blob = {"sha": "b" * 40, "node_id": "B__x", "size": 512,
            "content": "ZGVmIGZvbygpOgogICAgcGFzcw==",
            "url": "https://example.invalid/blob"}
    projected = mod._project_gh_payload(
        ["api", "repos/jsboige/CoursIA/git/blobs/" + "b" * 40], blob)
    assert projected == {"content": blob["content"]}
    import base64
    assert base64.b64decode(projected["content"]).decode() == "def foo():\n    pass"


# --- #22757 (tranche appels) : bundle des surfaces typees + threads ---------

def _bundle_page(next_page=False, cursor=None):
    return {
        "data": {"repository": {"pullRequest": {
            "author": {"__typename": "User", "login": "jsboige"},
            "comments": {
                "pageInfo": {"hasNextPage": next_page, "endCursor": cursor},
                "nodes": [{"author": {"__typename": "User", "login": "jsboige"},
                           "body": "nit: splitter", "createdAt": "2026-11-19T10:00:00Z"}]},
            "reviews": {
                "pageInfo": {"hasNextPage": next_page, "endCursor": cursor},
                "nodes": [{"author": {"__typename": "User", "login": "reviewer"},
                           "body": "reserve", "submittedAt": "2026-11-19T11:00:00Z",
                           "state": "COMMENTED", "databaseId": 77}]},
            "reviewThreads": {
                "pageInfo": {"hasNextPage": next_page, "endCursor": cursor},
                "nodes": [{"isResolved": False, "isOutdated": False,
                           "path": "x.py", "line": 3,
                           "comments": {"nodes": [
                               {"author": {"login": "reviewer", "__typename": "User"},
                                "body": "inline nit", "createdAt": "2026-11-19T11:30:00Z"}]}}]},
        }}}
    }


def test_bundle_rend_les_formes_des_deux_fonctions_originales(monkeypatch):
    """Témoin anti-divergence : le bundle produit EXACTEMENT les formes de
    `_typed_author_surfaces` et de `review_threads` sur le même PR."""
    seen: list[list[str]] = []

    def fake_gh_json(args):
        seen.append(args)
        return _bundle_page()

    monkeypatch.setattr(mod, "gh_json", fake_gh_json)
    bundle = mod._pr_review_bundle(41)
    # typed : forme de _typed_author_surfaces (SANS databaseId)
    assert bundle["typed"]["author"] == {"__typename": "User", "login": "jsboige"}
    assert bundle["typed"]["comments"] == [
        {"author": {"__typename": "User", "login": "jsboige"},
         "body": "nit: splitter", "createdAt": "2026-11-19T10:00:00Z"}]
    assert bundle["typed"]["reviews"] == [
        {"author": {"__typename": "User", "login": "reviewer"},
         "body": "reserve", "submittedAt": "2026-11-19T11:00:00Z",
         "state": "COMMENTED"}]
    # threads : forme de review_threads
    assert bundle["threads"] == [{
        "resolved": False, "outdated": False, "path": "x.py", "line": 3,
        "author": "reviewer", "body": "inline nit",
        "createdAt": "2026-11-19T11:30:00Z"}]
    # join numerique des dismissals
    assert bundle["author_of"] == {77: "reviewer"}
    # UNE seule requete GraphQL (la fusion des deux surfaces)
    graphql_calls = [a for a in seen if a[:2] == ["api", "graphql"]]
    assert len(graphql_calls) == 1


def test_bundle_fail_closed_par_surface(monkeypatch):
    """Payload inattendu -> typed vide (repli CLI).

    Review 5967281532 point 2 : le vide n'est PAS une preuve de fermeture
    sûre -- les témoins suivants couvrent relire-complète et refus explicite.
    Ici : comments.nodes non-list -> surface incomplète -> relecture
    `_typed_author_surfaces`, qui rend {} sur le même payload malformé
    (fail-closed, repli surfaces CLI complètes de pr view).

    Relecture du 2026-11-19 : threads et reviews portent désormais un
    `hasNextPage: False` explicite — une `pageInfo` sans booléen n'est plus
    acceptée comme une fin de connexion (le témoin de CE changement vit
    dans `test_bundle_pageinfo_sans_hasnextpage_rend_la_surface_incomplete`
    et `test_bundle_repli_incomplet_refuse_de_conclure`).
    """
    broken = {"data": {"repository": {"pullRequest": {
        "comments": {"pageInfo": {}, "nodes": "pas une liste"},
        "reviews": {"pageInfo": {"hasNextPage": False}, "nodes": []},
        "reviewThreads": {"pageInfo": {"hasNextPage": False}, "nodes": []},
    }}}}
    calls: list[str] = []

    def fake_gh_json(args):
        calls.append(" ".join(str(a) for a in args[:2]))
        return broken

    monkeypatch.setattr(mod, "gh_json", fake_gh_json)
    bundle = mod._pr_review_bundle(41)
    assert bundle["typed"] == {}
    assert bundle["threads"] == []
    # la relecture typed est bien passee (1 bundle + 1 _typed_author_surfaces)
    graphql_calls = [c for c in calls if "api graphql" in c]
    assert len(graphql_calls) == 2


def test_bundle_asymetrie_pas_de_redemande_ni_reaccumulation(monkeypatch):
    """Review 5967281532 point 1 : comments sur 2 pages, threads sur 1 --
    la connexion threads TERMINEE n'est plus demandee ni re-accumulee, et
    les listes restent EGALES aux lectures separees sur longueurs
    asymetriques."""
    pages_bundle = [
        # page 1 : comments continue, reviews et threads termines
        {"data": {"repository": {"pullRequest": {
            "author": {"__typename": "User", "login": "jsboige"},
            "comments": {"pageInfo": {"hasNextPage": True, "endCursor": "c1"},
                         "nodes": [{"author": {"__typename": "User", "login": "jsboige"},
                                    "body": "nit page 1", "createdAt": "d1"}]},
            "reviews": {"pageInfo": {"hasNextPage": False, "endCursor": "r1"},
                        "nodes": [{"author": {"__typename": "User", "login": "reviewer"},
                                   "body": "reserve", "submittedAt": "d2",
                                   "state": "COMMENTED", "databaseId": 77}]},
            "reviewThreads": {"pageInfo": {"hasNextPage": False, "endCursor": "t1"},
                              "nodes": [{"isResolved": False, "isOutdated": False,
                                         "path": "x.py", "line": 3,
                                         "comments": {"nodes": [
                                             {"author": {"login": "reviewer", "__typename": "User"},
                                              "body": "inline nit", "createdAt": "d3"}]}}]},
        }}}},
        # page 2 : comments termine ; SI threads etait redemande, le mock
        # re-servirait le meme thread (curseur t1) -- la re-accumulation
        # doublerait la liste.
        {"data": {"repository": {"pullRequest": {
            "comments": {"pageInfo": {"hasNextPage": False, "endCursor": "c2"},
                         "nodes": [{"author": {"__typename": "User", "login": "jsboige"},
                                    "body": "nit page 2", "createdAt": "d4"}]},
        }}}},
    ]
    seen: list[dict] = []

    def fake_gh_json(args):
        if args[:2] == ["api", "graphql"]:
            query = args[3]
            if "$cInc" in query:
                seen.append({"cInc": _flag(args, "cInc"), "rInc": _flag(args, "rInc"),
                             "tInc": _flag(args, "tInc")})
                return pages_bundle[min(len(seen) - 1, len(pages_bundle) - 1)]
            # lecture separee _typed_author_surfaces : meme scenario,
            # servie par le jeu _sep_pages (connexions toujours presentes)
            idx = getattr(fake_gh_json, "_sep", 0)
            setattr(fake_gh_json, "_sep", idx + 1)
            return getattr(fake_gh_json, "_sep_pages", pages_bundle)[idx]
        return {}

    def _flag(args, name):
        for i, a in enumerate(args):
            if a == f"-F" and i + 1 < len(args) and args[i + 1].startswith(f"{name}="):
                return args[i + 1].split("=", 1)[1]
        return None

    monkeypatch.setattr(mod, "gh_json", fake_gh_json)
    bundle = mod._pr_review_bundle(41)
    # exactement 2 appels bundle, et le 2e n'inclut NI reviews NI threads
    assert len(seen) == 2
    assert seen[0] == {"cInc": "true", "rInc": "true", "tInc": "true"}
    assert seen[1] == {"cInc": "true", "rInc": "false", "tInc": "false"}
    # pas de re-accumulation : chaque surface apparait UNE fois
    assert [c["body"] for c in bundle["typed"]["comments"]] == [
        "nit page 1", "nit page 2"]
    assert len(bundle["threads"]) == 1
    assert bundle["author_of"] == {77: "reviewer"}
    # egalite avec la lecture separee sur le meme scenario asymetrique :
    # la query separee lit TOUJOURS les deux connexions -- la page 2
    # separee porte reviews vide+termine (pas de duplication).
    pages_sep = [
        pages_bundle[0],
        {"data": {"repository": {"pullRequest": {
            "comments": pages_bundle[1]["data"]["repository"]["pullRequest"]["comments"],
            "reviews": {"pageInfo": {"hasNextPage": False, "endCursor": "r1"},
                        "nodes": []},
        }}}},
    ]
    fake_gh_json._sep_pages = pages_sep
    fake_gh_json._sep = 0
    separate = mod._typed_author_surfaces(41)
    assert separate["comments"] == bundle["typed"]["comments"]
    assert separate["reviews"] == bundle["typed"]["reviews"]


def test_bundle_reviews_incomplet_relit_le_join_et_conserve_la_reserve(monkeypatch):
    """Review 5967281532 point 2 : curseur reviews FIGE apres la page 1 ->
    le join ne doit JAMAIS rester un prefixe valide. La relecture REST
    complete le join (databaseId 88 de la page 2), le dismissal par un
    tiers reste attribue -- reserve conservee."""
    page1 = {"data": {"repository": {"pullRequest": {
        "author": {"__typename": "User", "login": "jsboige"},
        "comments": {"pageInfo": {"hasNextPage": False, "endCursor": "c1"},
                     "nodes": []},
        "reviews": {"pageInfo": {"hasNextPage": True, "endCursor": None},
                    "nodes": [{"author": {"__typename": "User", "login": "reviewer"},
                               "body": "reserve p1", "submittedAt": "d1",
                               "state": "CHANGES_REQUESTED", "databaseId": 77}]},
        "reviewThreads": {"pageInfo": {"hasNextPage": False, "endCursor": "t1"},
                          "nodes": []},
    }}}}

    def fake_gh_json(args):
        if args[:2] == ["api", "graphql"]:
            return page1  # curseur fige : endCursor None == r_after None
        if len(args) > 1 and args[1] == "repos/jsboige/CoursIA/pulls/41/reviews":
            return [{"id": 77, "user": {"login": "reviewer"}},
                    {"id": 88, "user": {"login": "tiers"}}]
        if len(args) > 1 and args[1] == "repos/jsboige/CoursIA/issues/41/timeline":
            return [{"event": "review_dismissed",
                     "actor": {"login": "quelquunautre"},
                     "dismissed_review": {"review_id": 88}}]
        return {}

    monkeypatch.setattr(mod, "gh_json", fake_gh_json)
    bundle = mod._pr_review_bundle(41)
    # le join relu est COMPLET : 88 (page 2) est present, pas seulement 77
    assert bundle["author_of"] == {77: "reviewer", 88: "tiers"}
    # la reserve est conservee : le dismissal de 88 par un tiers est improper
    improper = mod.improper_dismissals(41, author_of=bundle["author_of"])
    assert improper == {"tiers"}
    # la panne reviews n'a pas coupe les autres surfaces : threads complet
    assert bundle["threads"] == []


def test_bundle_structure_invalide_refus_explicite(monkeypatch):
    """Review 5967281532 point 2 (refus explicite) : structure GraphQL
    globalement invalide -> la relecture `review_threads` leve sur les
    memes donnees -> le bundle PROPAGE (PR illisible), jamais un prefixe
    analyse comme complet."""
    broken = {"data": {}}

    def fake_gh_json(args):
        return broken

    monkeypatch.setattr(mod, "gh_json", fake_gh_json)
    import pytest
    with pytest.raises(KeyError):
        mod._pr_review_bundle(41)


def test_bundle_propage_l_echec_d_appel(monkeypatch):
    """L'échec de l'appel GraphQL propage (contrat de review_threads)."""
    def fake_gh_json(args):
        raise mod.subprocess.CalledProcessError(1, ["gh", *args])

    monkeypatch.setattr(mod, "gh_json", fake_gh_json)
    try:
        mod._pr_review_bundle(41)
    except mod.subprocess.CalledProcessError:
        pass
    else:
        raise AssertionError("l'echec d'appel doit propager")


def test_bundle_repli_threads_preserve_les_enregistrements_normalises(monkeypatch):
    """Relecture ai-01 du 2026-11-19 : `review_threads` rend des
    enregistrements DÉJÀ normalisés (resolved/outdated/author/body/
    createdAt) — le bundle ne doit PAS les repasser dans le convertisseur
    des nœuds GraphQL bruts. Témoin exigé par la review : un thread RÉSOLU
    et un thread OUVERT traversent le repli à l'identique. Sans correctif,
    le thread résolu ressortait resolved=False, auteur « ? », corps vide —
    et bloquait la PR comme INLINE-UNRESOLVED."""
    broken_threads = {"data": {"repository": {"pullRequest": {
        "author": {"__typename": "User", "login": "jsboige"},
        "comments": {"pageInfo": {"hasNextPage": False, "endCursor": "c1"},
                     "nodes": []},
        "reviews": {"pageInfo": {"hasNextPage": False, "endCursor": "r1"},
                    "nodes": []},
        "reviewThreads": {"pageInfo": {}, "nodes": "pas une liste"},
    }}}}
    normalized = [
        {"resolved": True, "outdated": False, "path": "a.py", "line": 1,
         "author": "reviewer", "body": "leve par le fix cite",
         "createdAt": "2026-11-19T12:00:00Z"},
        {"resolved": False, "outdated": False, "path": "b.py", "line": 2,
         "author": "tiers", "body": "reste a faire",
         "createdAt": "2026-11-19T12:30:00Z"},
    ]
    seen: dict = {}

    def fake_review_threads(pr, strict=False):
        seen["strict"] = strict
        return [dict(t) for t in normalized]

    monkeypatch.setattr(mod, "gh_json", lambda args: broken_threads)
    monkeypatch.setattr(mod, "review_threads", fake_review_threads)
    bundle = mod._pr_review_bundle(41)
    # le repli est appele en mode STRICT : un repli incomplet doit refuser
    assert seen["strict"] is True
    # le resultat du repli est rendu TEL QUEL — resolu reste resolu,
    # auteur et corps conserves ; l'ouvert reste ouvert.
    assert bundle["threads"] == normalized
    assert bundle["threads"][0]["resolved"] is True
    assert bundle["threads"][0]["author"] == "reviewer"
    assert bundle["threads"][0]["body"] == "leve par le fix cite"
    assert bundle["threads"][1]["resolved"] is False
    # la panne threads n'a pas coupe les surfaces saines : typed du bundle
    assert bundle["typed"]["author"] == {"__typename": "User",
                                         "login": "jsboige"}


def _raw_thread(is_resolved: bool, path: str, body: str) -> dict:
    return {"isResolved": is_resolved, "isOutdated": False,
            "path": path, "line": 1,
            "comments": {"nodes": [
                {"author": {"login": "tiers", "__typename": "User"},
                 "body": body, "createdAt": "2026-11-19T12:00:00Z"}]}}


def test_bundle_pageinfo_sans_hasnextpage_rend_la_surface_incomplete(monkeypatch):
    """Relecture ai-01 du 2026-11-19 : une connexion avec `nodes` valide
    mais `pageInfo` sans booléen `hasNextPage` n'est PAS acceptée comme
    complète — la surface threads est relue via son chemin existant. Témoin
    : le préfixe contient un thread A (« prefix.py ») que le résultat final
    ne contient PAS ; le rendu vient tout entier de la relecture (leve.py +
    ouvert.py)."""
    bundle_page = {"data": {"repository": {"pullRequest": {
        "author": {"__typename": "User", "login": "jsboige"},
        "comments": {"pageInfo": {"hasNextPage": False, "endCursor": "c1"},
                     "nodes": []},
        "reviews": {"pageInfo": {"hasNextPage": False, "endCursor": "r1"},
                    "nodes": []},
        "reviewThreads": {"pageInfo": {"endCursor": "t1"},  # PAS de booléen
                          "nodes": [_raw_thread(True, "prefix.py", "prefix")]},
    }}}}
    relue = {"data": {"repository": {"pullRequest": {"reviewThreads": {
        "pageInfo": {"hasNextPage": False, "endCursor": "t9"},
        "nodes": [_raw_thread(True, "leve.py", "leve"),
                  _raw_thread(False, "ouvert.py", "ouvert")]}}}}}

    def fake_gh_json(args):
        if args[:2] == ["api", "graphql"]:
            # bundle = query multi-curseurs ($cInc) ; relecture = query
            # review_threads seule (pas de $cInc).
            return bundle_page if "$cInc" in args[3] else relue
        return {}

    monkeypatch.setattr(mod, "gh_json", fake_gh_json)
    bundle = mod._pr_review_bundle(41)
    assert [t["path"] for t in bundle["threads"]] == ["leve.py", "ouvert.py"]
    assert "prefix.py" not in [t["path"] for t in bundle["threads"]]
    assert bundle["threads"][0]["resolved"] is True
    assert bundle["threads"][1]["resolved"] is False


def test_bundle_repli_incomplet_refuse_de_conclure(monkeypatch):
    """Relecture ai-01 du 2026-11-19 : le repli LUI-MÊME encore incomplet
    (curseur figé sur la relecture review_threads) PROPAGE — jamais un
    verdict B.0 rendu sur le préfixe."""
    broken_threads = {"data": {"repository": {"pullRequest": {
        "author": {"__typename": "User", "login": "jsboige"},
        "comments": {"pageInfo": {"hasNextPage": False, "endCursor": "c1"},
                     "nodes": []},
        "reviews": {"pageInfo": {"hasNextPage": False, "endCursor": "r1"},
                    "nodes": []},
        "reviewThreads": {"pageInfo": {}, "nodes": "pas une liste"},
    }}}}
    frozen = {"data": {"repository": {"pullRequest": {"reviewThreads": {
        "pageInfo": {"hasNextPage": True, "endCursor": "t1"},
        "nodes": [_raw_thread(False, "x.py", "prefixe non concluable")]}}}}}

    def fake_gh_json(args):
        if args[:2] == ["api", "graphql"]:
            return broken_threads if "$cInc" in args[3] else frozen
        return {}

    monkeypatch.setattr(mod, "gh_json", fake_gh_json)
    import pytest
    with pytest.raises(mod.ThreadsIncomplete):
        mod._pr_review_bundle(41)


def test_improper_dismissals_author_of_epargne_lappel_reviews(monkeypatch):
    """author_of fourni -> seul l'appel timeline part (le REST reviews
    disparait du chemin gate, #22757)."""
    calls: list[str] = []

    def fake_gh_json(args):
        calls.append(args[1])
        return [{"event": "review_dismissed",
                 "actor": {"login": "someoneelse"},
                 "dismissed_review": {"review_id": 77}}]

    monkeypatch.setattr(mod, "gh_json", fake_gh_json)
    improper = mod.improper_dismissals(41, author_of={77: "reviewer"})
    assert improper == {"reviewer"}  # actor != emitter -> improper
    assert calls == ["repos/jsboige/CoursIA/issues/41/timeline"]


def test_head_tree_inerte_sans_sha_resolu(monkeypatch):
    """#22757 : sans SHA absent resolu, `commits/<head_oid>` ne part pas --
    `analyse` ne lit `_head_tree` que derriere ses gates SHA."""
    data = {
        "headRefOid": "a" * 40,
        "commits": [{"oid": "a" * 40}],
        "comments": [{"author": {"login": "jsboige"}, "body": "sans sha cite",
                      "createdAt": "2026-11-19T10:00:00Z"}],
        "reviews": [],
    }
    calls: list[str] = []

    def fake_gh_json(args):
        calls.append(args[1] if len(args) > 1 else str(args))
        raise AssertionError(
            "aucun appel gh n'est attendu sans SHA cite absent: " + str(args))

    monkeypatch.setattr(mod, "gh_json", fake_gh_json)
    mod._attach_absent_sha_context(data)
    assert data["_head_tree"] == ""
    assert data["_absent_sha_messages"] == {}
    assert calls == []
