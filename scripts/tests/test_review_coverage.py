#!/usr/bin/env python3
"""Unit tests for the pure classification core of review_coverage.py (#11232).

The ``classify`` function is network-free; ``main`` (the gh wiring) is
exercised end-to-end in CI dry-runs, not here. These fixtures encode the
verdicts measured firsthand on the #11232 sample (2026-08-16):

  - #11132 : 1041 additions, 0 reviews -> flag
  - #11210 : 883 additions, 0 reviews -> flag
  - #11217 : 318 additions, 2 reviews (Hermes + ai-01) -> clear
  - #11048 : 425 additions, 1 review (Hermes) -> clear
  - young PR : < threshold AND 0 reviews -> clear
  - draft PR : any size, 0 reviews -> skip_draft
  - base=branch PR : any size, 0 reviews -> skip_base
  - bot review : 1 review from clusterManager-Myia -> clear (the defect
    is the absence, not the absence of a human)

The bot review is important: a check that excluded bot reviews would
itself be the defect (it would re-create the hole it claims to fill, just
on a narrower surface).
"""

import json
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import review_coverage as rc  # noqa: E402
from review_coverage import classify  # noqa: E402


def _pr(additions: int, reviews: int | None = 0, *,
        is_draft: bool = False, base: str = "main") -> dict:
    """Build a PR fixture shaped like ``gh pr view --json`` output."""
    return {
        "number": 99999,
        "title": "test",
        "isDraft": is_draft,
        "baseRefName": base,
        "additions": additions,
        "reviews": [{"author": {"login": "x"}, "state": "APPROVED"}] * (reviews or 0),
    }


def test_large_no_review_flags():
    """#11132 1041 additions, 0 reviews -> flag (the headline case)."""
    assert classify(_pr(1041, 0)) == "flag"


def test_large_no_review_flags_883():
    """#11210 883 additions, 0 reviews -> flag."""
    assert classify(_pr(883, 0)) == "flag"


def test_medium_with_2_reviews_clears():
    """#11217 318 additions, 2 reviews -> clear (Hermes + ai-01)."""
    assert classify(_pr(318, 2)) == "clear"


def test_medium_with_1_review_clears():
    """#11048 425 additions, 1 review (Hermes) -> clear."""
    assert classify(_pr(425, 1)) == "clear"


def test_below_threshold_with_no_review_clears():
    """Young PR below threshold: 100 additions, 0 reviews -> clear.

    The signal is large-no-review, not just no-review. Otherwise the
    organ would label every fresh PR the moment it opens, defeating the
    purpose (the dashboard label would be a rediscovery of the PR list).
    """
    assert classify(_pr(100, 0)) == "clear"


def test_draft_large_no_review_skips():
    """Draft PR: 9999 additions, 0 reviews -> skip_draft, NOT flag.

    Draft PRs are by design unready for review; flagging them would mix
    two signals (coverage hole + "not ready") and produce noise.
    """
    assert classify(_pr(9999, 0, is_draft=True)) == "skip_draft"


def test_non_main_base_skips():
    """base != main: 9999 additions, 0 reviews -> skip_base.

    A PR targeting a feature branch has a different review audience
    (the branch owner / co-workers, not the cross-lane coordinator).
    The label is a current-state signal of the main-track coverage hole.
    """
    assert classify(_pr(9999, 0, base="feature/x")) == "skip_base"


def test_threshold_default_is_300():
    """The default threshold of 300 is the per-issue-body rationale.

    300 is just above the +318 LOC of #11217 (Hermes triggered) and
    well below #11132 / #11210. Documented in
    docs/reference/review-coverage-threshold.md.
    """
    from review_coverage import THRESHOLD_DEFAULT
    assert THRESHOLD_DEFAULT == 300


def test_exact_threshold_with_no_review_flags():
    """Edge case: PR at exactly the threshold, no review -> flag.

    ``additions >= threshold`` semantics: 300 with threshold 300 is in
    scope. Off-by-one here would be a silent scanner that misses the
    exact-threshold case.
    """
    assert classify(_pr(300, 0)) == "flag"


def test_exact_threshold_with_review_clears():
    """Edge case: PR at exactly the threshold, has review -> clear."""
    assert classify(_pr(300, 1)) == "clear"


def test_bot_review_clears():
    """A bot review alone counts (the defect is the ABSENCE, not the
    absence of a human).

    If we excluded bot reviews, the organ would re-create the hole it
    claims to fill, just on a narrower surface.
    """
    pr = _pr(1000, 0)
    pr["reviews"] = [{"author": {"login": "clusterManager-Myia"}, "state": "COMMENTED"}]
    assert classify(pr) == "clear"


def test_legacy_classification_unknown_field_is_robust():
    """Missing fields default to safe values (no crash).

    Real `gh pr view` payloads occasionally drop fields; the classifier
    must not raise on missing keys, or the cron would hard-fail.
    """
    minimal = {"number": 1}
    assert classify(minimal) in {"clear", "skip_draft", "skip_base", "flag"}
    # Specific check: no `additions` key + no `reviews` key = below threshold
    # + no reviews = clear (a no-op pass), not flag.
    assert classify(minimal) == "clear"


# ---------------------------------------------------------------------------
# Comment plumbing : the two SILENT defects of the first draft (Hermes review
# on #11526 found the first ; the second was on the same path, under it).
#
# Both fixtures below encode a shape MEASURED against the live API, not an
# imagined one -- which is the whole point, since neither defect raised.
# ---------------------------------------------------------------------------

# Measured 2026-08-17 on a real comment of PR #11444 :
#   `gh pr view --json comments --jq '.comments[0]'`
#     id  = "IC_kwDOH2Odns8AAAABPNf6UA"     <- GraphQL node id
#     url = "https://.../pull/11444#issuecomment-5315754576"
# and, on the same REST path the delete uses,
#   GET repos/jsboige/CoursIA/issues/comments/IC_kwDO...  -> HTTP 404
#   GET repos/jsboige/CoursIA/issues/comments/5315754576  -> the comment
_REAL_NODE_ID = "IC_kwDOH2Odns8AAAABPNf6UA"
_REAL_REST_ID = "5315754576"
_REAL_URL = f"https://github.com/jsboige/CoursIA/pull/11444#issuecomment-{_REAL_REST_ID}"


def _fake_gh(payload: list[dict]):
    """Stand in for `gh pr view --json comments --jq '[.comments[]|{url,body}]'`."""
    class _Res:
        returncode = 0
        stdout = json.dumps(payload)
        stderr = ""
    return lambda *a, **k: _Res()


def test_framed_comment_detected_across_lines(monkeypatch):
    """The framing puts START and END on DIFFERENT lines.

    The first draft split the raw `--jq .comments[].body` output on newlines
    and kept lines holding BOTH markers -- which no framed comment can ever
    satisfy. Detection was empty forever, so the no-op never fired and the
    daily cron would have posted one comment per flagged PR per day.
    """
    body = f"{rc.COMMENT_MARKER_START}\nligne 1\nligne 2\n{rc.COMMENT_MARKER_END}"
    monkeypatch.setattr(rc.subprocess, "run",
                        _fake_gh([{"url": _REAL_URL, "body": body}]))
    found = rc.framed_comments(11444)
    assert len(found) == 1, "multi-line framed comment must be detected"
    assert found[0][1] == body


def test_rest_id_recovered_from_url_not_node_id(monkeypatch):
    """The id used for DELETE is the NUMERIC one, taken from the url.

    `.comments[].id` is a GraphQL node id; the delete endpoint is REST and
    404s on it -- silently, since that subprocess carries no `check`.
    """
    body = f"{rc.COMMENT_MARKER_START}\nx\n{rc.COMMENT_MARKER_END}"
    monkeypatch.setattr(rc.subprocess, "run",
                        _fake_gh([{"url": _REAL_URL, "body": body}]))
    cid, _ = rc.framed_comments(11444)[0]
    assert cid == _REAL_REST_ID
    assert cid != _REAL_NODE_ID


def test_foreign_comments_never_touched(monkeypatch):
    """A comment without our markers is not ours -- it is never a delete target."""
    monkeypatch.setattr(rc.subprocess, "run", _fake_gh([
        {"url": _REAL_URL, "body": "un commentaire humain"},
        {"url": _REAL_URL, "body": "<!-- variation-genre-signals -->\nautre bot"},
    ]))
    assert rc.framed_comments(11444) == []


def test_identical_body_is_a_noop(monkeypatch):
    """Re-posting the same content must not call gh at all beyond the lookup."""
    framed = f"{rc.COMMENT_MARKER_START}\n{rc.REMEDIATION}\n{rc.COMMENT_MARKER_END}"
    calls = []

    class _Res:
        returncode = 0
        stdout = json.dumps([{"url": _REAL_URL, "body": framed}])
        stderr = ""

    def _run(cmd, *a, **k):
        calls.append(cmd)
        return _Res()

    monkeypatch.setattr(rc.subprocess, "run", _run)
    assert rc.upsert_comment(11444, rc.REMEDIATION) == []
    assert len(calls) == 1, f"no-op must not post or delete, got {calls}"


def test_changed_body_deletes_then_posts(monkeypatch):
    """Different content -> delete the stale one by REST id, then post."""
    stale = f"{rc.COMMENT_MARKER_START}\nvieux texte\n{rc.COMMENT_MARKER_END}"
    calls = []

    class _Res:
        returncode = 0
        stdout = json.dumps([{"url": _REAL_URL, "body": stale}])
        stderr = ""

    def _run(cmd, *a, **k):
        calls.append(cmd)
        return _Res()

    monkeypatch.setattr(rc.subprocess, "run", _run)
    assert rc.upsert_comment(11444, rc.REMEDIATION) == []
    joined = [" ".join(c) for c in calls]
    assert any("DELETE" in c and _REAL_REST_ID in c for c in joined), joined
    assert any("pr comment" in c for c in joined), joined


def test_failed_delete_is_reported_not_swallowed(monkeypatch):
    """An advisory must never block -- but it must not fail in silence either."""
    stale = f"{rc.COMMENT_MARKER_START}\nvieux\n{rc.COMMENT_MARKER_END}"

    class _Lookup:
        returncode = 0
        stdout = json.dumps([{"url": _REAL_URL, "body": stale}])
        stderr = ""

    class _Fail:
        returncode = 1
        stdout = ""
        stderr = "gh: Not Found (HTTP 404)"

    seen = {"n": 0}

    def _run(cmd, *a, **k):
        seen["n"] += 1
        if seen["n"] == 1:
            return _Lookup()
        return _Fail() if "DELETE" in cmd else _Lookup()

    monkeypatch.setattr(rc.subprocess, "run", _run)
    warnings = rc.upsert_comment(11444, rc.REMEDIATION)
    assert len(warnings) == 1 and "404" in warnings[0], warnings


# ---------------------------------------------------------------------------
# Second review surface : une passe emise en COMMENTAIRE d'issue (#16284).
#
# Le perimetre `reviews[]` seul rendait l'organe aveugle a un mode d'emission
# STRUCTUREL du cluster : les personas emettent leur verdict en commentaire
# quand elles sont contraintes en jetons (« contrainte token : COMMENT only
# — opener `jsboige`, cap self-review #3219 », verbatim des fils).
#
# Les deux fixtures ci-dessous sont les corps REELS des deux cas mesures le
# 2026-09-15 ; l'organe avait publie « aucune review » 9 min et 6 min APRES
# la passe, et les deux PR portent encore le label.
# ---------------------------------------------------------------------------

# Reel #16133 — clusterManager-Myia, 2026-09-14T12:29:47Z (tronque a la 3e
# ligne, qui suffit : le tag ouvre le paragraphe).
_REAL_PASS_CONCERNS = (
    "VERDICT: CONCERNS\n"
    "\n"
    "**[Hermes]** — #16133 — reproduction firsthand sur head `250707e2` "
    "(fetch raw du notebook au ref branche), 3 artefacts :\n"
)
# Reel #16145 — clusterManager-Myia, 2026-09-14T12:31:38Z.
_REAL_PASS_LGTM = (
    "VERDICT: LGTM\n"
    "\n"
    "**[Hermes]** — #16145 — reproduction firsthand sur head `f230ac1e` "
    "(fetch raw du notebook + patch README au ref branche), 3 artefacts :\n"
)


def _comment(login: str, body: str) -> dict:
    """Une entree de `gh pr list --json comments` (forme mesuree : author.login)."""
    return {"author": {"login": login}, "body": body}


def _pr_with_comments(additions: int, comments: list[dict]) -> dict:
    return {**_pr(additions, 0), "comments": comments}


def test_review_pass_in_comment_lifts_the_flag():
    """#16133 : verdict CONCERNS en commentaire -> clear, plus flag."""
    pr = _pr_with_comments(2531, [_comment("clusterManager-Myia", _REAL_PASS_CONCERNS)])
    assert classify(pr) == "clear"


def test_review_pass_approval_in_comment_lifts_the_flag():
    """#16145 : verdict LGTM en commentaire -> clear.

    Meme defaut, surface APPROBATION -- le cas qui condamne un predicat bati
    sur `nits.classify()` (cf. la garde ci-dessous).
    """
    pr = _pr_with_comments(1705, [_comment("clusterManager-Myia", _REAL_PASS_LGTM)])
    assert classify(pr) == "clear"


def test_classify_alone_would_miss_the_approval():
    """Garde du choix d'implementation -- le piege, en executable.

    `nits.classify()` attrape CONCERNS (``BOT-CONCERN``) mais rend **None**
    sur LGTM : cet organe classe les RESERVES, pas les passes. Un predicat
    bati dessus fermerait #16133 en laissant #16145 faux -- le defaut du
    ticket, deplace sur la surface des approbations.
    """
    assert rc.nits.classify("clusterManager-Myia", _REAL_PASS_CONCERNS) == "BOT-CONCERN"
    assert rc.nits.classify("clusterManager-Myia", _REAL_PASS_LGTM) is None
    # ...et pourtant c'est une passe, des deux cotes :
    for body in (_REAL_PASS_CONCERNS, _REAL_PASS_LGTM):
        assert rc.review_pass_in_comments([_comment("clusterManager-Myia", body)])


def test_bare_login_verdict_is_not_a_review_pass():
    """Un commentaire NU d'un login partage ne prouve pas qu'on a relu.

    `jsboige` est l'identite de poussee de toutes les lanes (#13316), donc un
    ``VERDICT: LGTM`` nu sous ce login peut etre une lane qui parle de sa
    propre PR. Le canon ne l'admet que porteur d'un marqueur ; on suit le
    canon plutot que d'ouvrir un second juge.
    """
    pr = _pr_with_comments(
        1000, [_comment("jsboige", "VERDICT: LGTM\n\nOK pour moi.\n")])
    assert classify(pr) == "flag"


def test_own_remediation_comment_never_self_exempts():
    """Le commentaire de l'organe n'est JAMAIS une passe de review.

    Garde d'auto-desactivation : le texte de remediation nomme les reviewers
    (« Hermes, ai-01, ou review humaine »). Le jour ou il les nommerait entre
    crochets, l'organe se reconnaitrait comme revu et ne poserait plus jamais
    son label -- en silence.
    """
    own = f"{rc.COMMENT_MARKER_START}\n{rc.REMEDIATION}\n{rc.COMMENT_MARKER_END}"
    assert rc.review_pass_in_comments([_comment("github-actions[bot]", own)]) is False
    # Controle : le MEME texte, sans nos marqueurs mais coiffe d'un tag de
    # persona -- la garde tombe, la passe est vue. C'est bien le marqueur de
    # l'organe, et non son auteur, qui l'exempte.
    tagged = "**[Hermes]**\n" + rc.REMEDIATION
    assert rc.review_pass_in_comments([_comment("clusterManager-Myia", tagged)]) is True


def test_untagged_persona_comment_is_not_a_pass():
    """Mesure qui a tranche le predicat : le login SEUL compterait une LEVEE.

    Sur les 121 PR ouvertes du 2026-09-15, ``clusterManager-Myia`` a commente
    10 fois : 9 passes portant le tag, et 1 sans tag -- #15795, une levee
    (« Levee a la tete exacte ... -- review 5202580554 »).

    Honnetement : sur ce corpus les deux predicats rendent le **meme**
    verdict, parce que cette levee tombe sur une PR sous le seuil. Le test
    ne pretend donc pas que le login coute quelque chose aujourd'hui -- il
    fige la classe : une levee non taggee n'est pas une passe, et le jour ou
    elle tombe sur une PR large non revue, le login la declarerait couverte
    (le trou de #11232, invisible). Le tag est requis, comme le demande le
    canon.
    """
    lift = ("Levée à la tête exacte `284d067ee6265d99e42590897d8c38597c47cca4`"
            " — review `5202580554`.\n")
    pr = _pr_with_comments(1000, [_comment("clusterManager-Myia", lift)])
    assert classify(pr) == "flag"


def test_backticked_tag_is_a_citation_not_a_pass():
    """`` `[Hermes]` `` cite est une CITATION, pas une emission (#13030).

    C'est la raison exacte pour laquelle on importe le motif durci du canon au
    lieu du `has_marker()` public : ce dernier est un `in` de sous-chaine et
    compterait la citation. Le test fige les deux comportements cote a cote --
    si le public devenait utilisable, ce test le dirait.
    """
    quoted = "Le ticket dit : `[Hermes]` a rendu un verdict CONCERNS.\n"
    assert rc.nits.has_marker(quoted, ("[Hermes]",)) is True      # le public matcherait
    assert rc.nits._PERSONA_MARKERS_RE.search(quoted) is None     # le durci non
    pr = _pr_with_comments(1000, [_comment("clusterManager-Myia", quoted)])
    assert classify(pr) == "flag"


def test_bold_persona_tag_counts():
    """Un en-tete en GRAS compte (#14503, PR #14548).

    Une variante `(?:^|\\s)` du motif exigeait une espace avant `[` : le `*`
    du gras suffisait alors a effacer la passe entiere du radar.
    """
    assert rc.review_pass_in_comments(
        [_comment("clusterManager-Myia", "**[NanoClaw]** structural review\n")]) is True


def test_comment_pass_does_not_override_the_skips():
    """L'ordre des verdicts tient : un draft reste un draft.

    Les skips precedent le seuil ET les surfaces de review ; une passe en
    commentaire ne doit pas transformer un hors-perimetre en couvert.
    """
    draft = {**_pr(9999, 0, is_draft=True),
             "comments": [_comment("clusterManager-Myia", _REAL_PASS_LGTM)]}
    assert classify(draft) == "skip_draft"
    off_base = {**_pr(9999, 0, base="feature/x"),
                "comments": [_comment("clusterManager-Myia", _REAL_PASS_LGTM)]}
    assert classify(off_base) == "skip_base"


def test_missing_comments_key_is_not_a_crash():
    """Projection anterieure / fixture sans `comments` : pas de passe, pas d'exception.

    Le cron ne doit pas tomber parce qu'une forme de payload a change -- et
    les fixtures historiques du haut de ce fichier n'ont pas la cle.
    """
    assert rc.review_pass_in_comments(None) is False
    assert rc.review_pass_in_comments([]) is False
    assert classify(_pr(1000, 0)) == "flag"


def test_label_constants_within_github_api_limits():
    # 422 muet du run 2026-08-29 : LABEL_DESC faisait 189 chars, la limite
    # REST est 100 -- gh label create echouait en silence et le payload
    # (le label) ne s'appliquait jamais.
    assert len(rc.LABEL_DESC) <= 100
    assert len(rc.LABEL_DEFAULT) <= 63


if __name__ == "__main__":
    test_label_constants_within_github_api_limits()
    test_large_no_review_flags()
    test_large_no_review_flags_883()
    test_medium_with_2_reviews_clears()
    test_medium_with_1_review_clears()
    test_below_threshold_with_no_review_clears()
    test_draft_large_no_review_skips()
    test_non_main_base_skips()
    test_threshold_default_is_300()
    test_exact_threshold_with_no_review_flags()
    test_exact_threshold_with_review_clears()
    test_bot_review_clears()
    test_legacy_classification_unknown_field_is_robust()
    print("All tests passed")
