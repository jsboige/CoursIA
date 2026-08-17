"""Tests de falsification pour la mesure d'autorite des levees (#11145).

Donnees synthetiques, sans reseau. Un detecteur sans test qui prouve qu'il
se tait sur les cas sains serait un detecteur qu'on desactivera (cf #10020).
"""
from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from nit_lift_authorship import measure_pr  # noqa: E402


def _pr(number, comments=(), reviews=(), merged="2026-08-01T12:00:00Z",
        author="worker"):
    return {
        "number": number,
        "mergedAt": merged,
        "author": {"login": author},
        "comments": [
            {"author": {"login": a}, "body": b, "createdAt": t}
            for (a, b, t) in comments
        ],
        "reviews": [
            {"author": {"login": a}, "body": b, "state": s, "submittedAt": t}
            for (a, b, s, t) in reviews
        ],
    }


def test_bystander_lift_is_flagged():
    """Le scenario #10761 : reserve d'un reviewer, commentaire d'un tiers
    qui n'est NI l'auteur de la reserve NI l'auteur de la PR."""
    pr = _pr(1, author="worker", comments=[
        ("hermes", "Verdict: COMMENT_WITH_CONCERNS — 2 reserves.", "2026-08-01T10:00:00Z"),
        ("other-agent", "Interprete, rien a redire de plus ici.", "2026-08-01T11:00:00Z"),
    ])
    rows = measure_pr(pr)["rows"]
    assert len(rows) == 1
    assert rows[0]["authority"] == "BYSTANDER"
    assert rows[0]["lifter"] == "other-agent"


def test_pr_author_lift_is_its_own_class():
    """Le flux sain : l'auteur de la PR repond lui-meme a la reserve du
    reviewer (pas SELF, pas BYSTANDER — classe dediee PR_AUTHOR)."""
    pr = _pr(9, author="worker", comments=[
        ("hermes", "Verdict: COMMENT_WITH_CONCERNS — 2 reserves.", "2026-08-01T10:00:00Z"),
        ("worker", "Reserves adressees au commit 3c1, explication inline.", "2026-08-01T11:00:00Z"),
    ])
    rows = measure_pr(pr)["rows"]
    assert rows[0]["authority"] == "PR_AUTHOR"
    assert rows[0]["lifter"] == "worker"


def test_self_lift_is_classified_self():
    """Le reserveur revient repondre lui-meme."""
    pr = _pr(2, comments=[
        ("hermes", "Verdict: COMMENT_WITH_CONCERNS — 2 reserves.", "2026-08-01T10:00:00Z"),
        ("hermes", "Traite dans le push suivant, reserve levee.", "2026-08-01T11:00:00Z"),
    ])
    rows = measure_pr(pr)["rows"]
    assert rows[0]["authority"] == "SELF"
    assert rows[0]["lifter"] == "hermes"


def test_changes_requested_third_comment_does_not_lift():
    """Regime natif : un CHANGES_REQUESTED n'est leve que par son auteur
    (re-review APPROVED) ou une phrase explicite — un commentaire de tiers
    quelconque ne leve rien (le regime durci de analyse, copie ici)."""
    pr = _pr(3, comments=[
        ("other-agent", "Vu, rien a ajouter.", "2026-08-01T11:00:00Z"),
    ], reviews=[
        ("hermes", "", "CHANGES_REQUESTED", "2026-08-01T10:00:00Z"),
    ])
    rows = measure_pr(pr)["rows"]
    assert rows[0]["authority"] == "UNLIFTED"


def test_changes_requested_lifted_by_same_author_rereview():
    pr = _pr(4, reviews=[
        ("hermes", "", "CHANGES_REQUESTED", "2026-08-01T10:00:00Z"),
        ("hermes", "", "APPROVED", "2026-08-01T11:00:00Z"),
    ])
    rows = measure_pr(pr)["rows"]
    assert rows[0]["authority"] == "SELF"


def test_changes_requested_lifted_by_third_explicit_lift():
    """La phrase explicite de levee leve un CHANGES_REQUESTED, tiers inclus."""
    pr = _pr(5, comments=[
        ("merger", "Reserves adressees par le push 4f2a, levee.", "2026-08-01T11:00:00Z"),
    ], reviews=[
        ("hermes", "", "CHANGES_REQUESTED", "2026-08-01T10:00:00Z"),
    ])
    rows = measure_pr(pr)["rows"]
    assert rows[0]["authority"] == "BYSTANDER"
    assert rows[0]["lifter"] == "merger"


def test_healthy_pr_produces_no_rows():
    """Le detecteur se tait : PR sans reserve = zero lignes, zero faux signal."""
    pr = _pr(6, comments=[
        ("jsboige", "Merci, integre.", "2026-08-01T11:00:00Z"),
    ])
    res = measure_pr(pr)
    assert res["rows"] == []
    assert res["re_precited"] == 0


def test_post_merge_lift_does_not_count():
    """Un commentaire poste APRES le merge n'a rien leve (borne cutoff)."""
    pr = _pr(7, comments=[
        ("hermes", "Verdict: COMMENT_WITH_CONCERNS — reserve.", "2026-08-01T10:00:00Z"),
        ("other-agent", "Vu.", "2026-08-01T13:00:00Z"),
    ])
    rows = measure_pr(pr)["rows"]
    assert rows[0]["authority"] == "UNLIFTED"


def test_re_precited_counter_fires_and_crosses_with_reserve():
    """Concern 1 : « Re: CONCERNS » compte comme occurrence pre-citee ;
    le commentaire-porteur reste classifie par classify() (ici reponse
    « Fixed. » => non-reserve => pas un faux negatif)."""
    pr = _pr(8, comments=[
        ("worker", "## Re: CONCERNS\n\n**Fixed.** Commit 1a2b.", "2026-08-01T11:00:00Z"),
    ])
    res = measure_pr(pr)
    assert res["re_precited"] >= 1
    assert res["re_precited_in_reserve"] == 0
