"""Tests de `scripts/ci/pool_review_verdicts.py` (#16926).

Aucun appel reseau : `fetch_pool` passe par la couture `run_gh`. La
classification (`classify_pr`, `_voice`) est pure -- fixtures de corps de
review/commentaire.

Le contrat verrouille :

  * le verdict se lit dans les CORPS (prefixe ligne-debut ``VERDICT:``), sur
    les DEUX surfaces (reviews[] + commentaires), latest-wins ;
  * ``reviewDecision`` n'est JAMAIS lu comme un verdict -- il est rendu
    comme colonne DECISION pour la distinction « sans review » vs « sans
    decision » ;
  * le marqueur de persona est celui du canon nits (en-tete gras compte,
    citation backtick exclue) -- importe, pas copie ;
  * un etat de review REEL (CHANGES_REQUESTED/APPROVED) gouverne ;
  * un token VERDICT cite en milieu de phrase n'est PAS une emission.
"""

import importlib.util
import json
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
SCRIPT = HERE.parent / "ci" / "pool_review_verdicts.py"
spec = importlib.util.spec_from_file_location("pool_review_verdicts", SCRIPT)
mod = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mod)


def pr_node(number=1, *, reviews=None, comments=None, decision=None, created="2026-09-01T00:00:00Z"):
    return {
        "number": number,
        "title": f"PR #{number}",
        "createdAt": created,
        "mergeStateStatus": "CLEAN",
        "reviewDecision": decision,
        "reviews": {"nodes": reviews or []},
        "comments": {"nodes": comments or []},
    }


def review(body, at="2026-09-10T00:00:00Z", state="COMMENTED", login="clusterManager-Myia"):
    return {"author": {"login": login}, "state": state, "body": body, "submittedAt": at}


def comment(body, at="2026-09-11T00:00:00Z", login="clusterManager-Myia"):
    return {"author": {"login": login}, "body": body, "createdAt": at}


def test_verdict_prefix_in_review_body_wins_over_null_decision():
    node = pr_node(31, decision=None, reviews=[
        review("**[Hermes]** — VERDICT: CONCERNS (contrainte token CoursIA : COMMENT only, #15511)")
    ])
    row = mod.classify_pr(node)
    assert row["verdict"] == "CONCERNS"
    assert row["decision"] is None
    assert row["verdict_surface"] == "review-body"


def test_lgtm_prefix_bare_form_counts():
    node = pr_node(32, reviews=[review("VERDICT: LGTM\n\nPreuves : ...")])
    assert mod.classify_pr(node)["verdict"] == "LGTM"


def test_no_voice_at_all_is_sans_review():
    node = pr_node(33, reviews=[review("sortie verifiee, rien a signaler")],
                   comments=[comment("[DONE] livraison")])
    row = mod.classify_pr(node)
    assert row["verdict"] == "SANS-REVIEW"


def test_persona_tag_without_typed_verdict_is_a_voice_not_a_review():
    node = pr_node(34, comments=[comment("**[Hermes]** — releve a la tete exacte 5cd5664")])
    row = mod.classify_pr(node)
    assert row["verdict"] == "VOIX-SANS-VERDICT"


def test_comment_surface_verdict_latest_wins_over_older_review():
    node = pr_node(35, reviews=[
        review("VERDICT: CONCERNS\n\nreserve sur la cellule 12", at="2026-09-10T00:00:00Z")
    ], comments=[
        comment("VERDICT: LGTM\n\nreserve levee, re-exec verifiee", at="2026-09-12T00:00:00Z")
    ])
    row = mod.classify_pr(node)
    assert row["verdict"] == "LGTM"
    assert row["verdict_surface"] == "comment"


def test_real_changes_requested_state_governs():
    node = pr_node(36, reviews=[
        review("ok pour moi", at="2026-09-13T00:00:00Z", state="CHANGES_REQUESTED", login="myia-ai-01")
    ], comments=[
        comment("VERDICT: LGTM", at="2026-09-12T00:00:00Z")
    ])
    row = mod.classify_pr(node)
    assert row["verdict"] == "CHANGES_REQUESTED"
    assert row["verdict_surface"] == "review-state"


def test_mid_sentence_verdict_token_is_a_mention_not_an_emission():
    node = pr_node(37, comments=[
        comment("La review precedente portait un VERDICT: CONCERNS desormais leve.")
    ])
    row = mod.classify_pr(node)
    # Le token en milieu de phrase ne compte pas ; la phrase n'est pas non
    # plus une voix de persona -> SANS-REVIEW, pas un faux CONCERNS.
    assert row["verdict"] == "SANS-REVIEW"


def test_backticked_verdict_citation_does_not_count():
    node = pr_node(38, comments=[
        comment("cf `VERDICT: LGTM` poste hier par la lane X")
    ])
    assert mod.classify_pr(node)["verdict"] == "SANS-REVIEW"


def test_fetch_pool_paginates_and_merges(monkeypatch, capsys):
    pages = [
        {"data": {"repository": {"pullRequests": {
            "pageInfo": {"hasNextPage": True, "endCursor": "c1"},
            "nodes": [pr_node(1, created="2026-09-19T00:00:00Z")],
        }}}},
        {"data": {"repository": {"pullRequests": {
            "pageInfo": {"hasNextPage": False, "endCursor": None},
            "nodes": [pr_node(2, created="2026-09-01T00:00:00Z")],
        }}}},
    ]
    calls = []

    def fake_gh(args, stdin=None):
        calls.append(args)
        return json.dumps(pages[len(calls) - 1])

    monkeypatch.setattr(mod, "run_gh", fake_gh)
    nodes = mod.fetch_pool("jsboige/CoursIA", 5, 10)
    assert [n["number"] for n in nodes] == [1, 2]
    assert len(calls) == 2
    assert "-f" in calls[0] and "query=" in " ".join(calls[0])


def test_main_rend_comptes_et_distinction(monkeypatch, capsys):
    nodes = [
        pr_node(41, decision=None, reviews=[review("VERDICT: LGTM")], created="2026-09-18T00:00:00Z"),
        pr_node(42, decision=None, created="2026-09-01T00:00:00Z"),
    ]
    monkeypatch.setattr(mod, "fetch_pool", lambda *a, **k: nodes)
    rc = mod.main(["--repo", "jsboige/CoursIA"])
    out = capsys.readouterr().out
    assert rc == 0
    assert "pool=2" in out
    assert "decision_null=2" in out
    assert '"LGTM": 1' in out and '"SANS-REVIEW": 1' in out
    assert "VERDICT=LGTM" in out and "VERDICT=SANS-REVIEW" in out
    assert "DECISION=-" in out


def test_gradient_quartiles_order_recent_first(monkeypatch, capsys):
    nodes = [
        pr_node(50 + i, reviews=[review("VERDICT: LGTM" if i % 2 else "VERDICT: CONCERNS")],
                created=f"2026-09-{(i % 28) + 1:02d}T00:00:00Z")
        for i in range(8)
    ]
    monkeypatch.setattr(mod, "fetch_pool", lambda *a, **k: nodes)
    rc = mod.main(["--gradient", "--json"])
    payload = json.loads(capsys.readouterr().out)
    assert rc == 0
    grad = payload["gradient"]
    assert len(grad) == 4
    assert all(g["n"] == 2 for g in grad)
    assert sum(g["counts"].get("LGTM", 0) for g in grad) == 4
    assert sum(g["counts"].get("CONCERNS", 0) for g in grad) == 4


def test_fetch_prs_classifies_each_and_skips_absent(monkeypatch):
    """#16926 : consommation per-PR -- une requete par numero, classify_pr sur
    chaque noeud ; une PR fermee/injoignable (pullRequest: null) rend une
    entree ABSENTE, jamais une exception."""
    payloads = {
        20961: {"data": {"repository": {"pullRequest": pr_node(
            20961,
            reviews=[review("**[Hermes]** — VERDICT: CONCERNS",
                            at="2026-10-16T10:00:00Z")])}}},
        42: {"data": {"repository": {"pullRequest": None}}},
    }
    calls = []

    def fake_gh(args, stdin=None):
        # le numero est interpole dans la requete (gh -f ne coercerait pas
        # vers Int!), pas passe en variable
        match = re.search(r"pullRequest\(number: (\d+)\)", " ".join(args))
        calls.append(int(match.group(1)))
        return json.dumps(payloads[calls[-1]])

    monkeypatch.setattr(mod, "run_gh", fake_gh)
    out = mod.fetch_prs("jsboige/CoursIA", [20961, 42])
    assert out[20961]["verdict"] == "CONCERNS"
    assert out[20961]["verdict_surface"] == "review-body"
    # la PR fermee n'a pas d'entree, et n'a pas fait echouer l'autre
    assert 42 not in out
    assert len(calls) == 2


def test_fetch_prs_une_pr_illisible_n_arrete_pas_les_autres(monkeypatch):
    """Un payload invalide sur UNE PR est avale par PR : les suivantes sont
    quand meme classifiees (la file de reparation ne se bloque pas)."""
    state = {"first": True}

    def fake_gh(args, stdin=None):
        if state["first"]:
            state["first"] = False
            return "ceci n'est pas du json"
        return json.dumps({"data": {"repository": {"pullRequest": pr_node(
            7, comments=[comment("VERDICT: LGTM", at="2026-10-16T11:00:00Z")])}}})

    monkeypatch.setattr(mod, "run_gh", fake_gh)
    out = mod.fetch_prs("jsboige/CoursIA", [1, 7])
    assert 1 not in out
    assert out[7]["verdict"] == "LGTM"
    assert out[7]["verdict_surface"] == "comment"


def test_prefix_form_comment_with_concerns_is_a_concerns_verdict():
    """Forme HISTORIQUE Hermes (#16926) : « **[Hermes] Review —
    COMMENT_WITH_CONCERNS** » porte un verdict CONCERNS — mesure firsthand
    sur #20961 : 4 des 5 PRs de la file de reparation portent cette forme
    et se lisaient VOIX-SANS-VERDICT."""
    node = pr_node(20961, reviews=[
        review("**[Hermes] Review — COMMENT_WITH_CONCERNS** @ `c3b33918`",
               at="2026-10-15T10:00:00Z")
    ])
    row = mod.classify_pr(node)
    assert row["verdict"] == "CONCERNS"
    assert row["verdict_surface"] == "review-body"


def test_prefix_form_bare_marker_without_review_word():
    node = pr_node(31, reviews=[review("[Hermes] COMMENT_WITH_CONCERNS")])
    assert mod.classify_pr(node)["verdict"] == "CONCERNS"


def test_prefix_form_arbitrary_word_after_header_is_not_a_verdict():
    """« **[NanoClaw]** structural review » : le mot apres l'en-tete n'est
    pas dans la table -> voix de persona SANS verdict, pas un faux LGTM."""
    node = pr_node(32, reviews=[review("**[NanoClaw]** structural review")])
    assert mod.classify_pr(node)["verdict"] == "VOIX-SANS-VERDICT"


def test_prefix_form_mid_sentence_mention_is_not_an_emission():
    node = pr_node(33, comments=[
        comment("cf [Hermes] COMMENT_WITH_CONCERNS poste hier, desormais leve")
    ])
    assert mod.classify_pr(node)["verdict"] == "VOIX-SANS-VERDICT"


def test_prefix_form_backticked_citation_is_not_an_emission():
    node = pr_node(34, comments=[
        comment("la review disait `[Hermes] COMMENT_WITH_CONCERNS` avant correction")
    ])
    row = mod.classify_pr(node)
    # le backtick exclut l'en-tete ET la persona : pas une voix du tout
    assert row["verdict"] == "SANS-REVIEW"


def test_prefix_form_lgtm_maps_to_lgtm():
    node = pr_node(35, reviews=[review("**[Hermes] Review — LGTM** (re-review)")])
    assert mod.classify_pr(node)["verdict"] == "LGTM"
