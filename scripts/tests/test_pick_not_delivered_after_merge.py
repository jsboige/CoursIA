"""#22987 -- un `[NOT-DELIVERED]` posterieur a la fusion revoque le signal.

Defaut mesure : la surface « PR MERGEE <90j » du picker etait traitee comme
TERMINALE. Une PR fusionnee il y a moins de 90 jours ecartait l'issue de
l'urne `grain` a perpetuite, meme si le coordinateur avait ensuite constate
que la livraison etait partielle et poste `[NOT-DELIVERED]`. Le tapis
servait alors du travail que le fil declarait non livre, et la lane ne
pouvait plus rien y faire -- exactement le symptome que la surface
« commentaire de cloture » sait deja reparer (#22500 point 1 : le marqueur
re-arme l'issue).

Trois exigences d'acceptation, une par test nomme :

1. une revocation **apres** la fusion annule le signal `PR MERGEE <90j` ;
2. le cas reel de **#15002** (dates mesurees sur le depot, pas inventees) ;
3. le **controle negatif** -- une revocation **anterieure** a la fusion ne
   revoque rien : la fusion qui la suit re-livre l'issue.

Pourquoi le controle negatif est obligatoire : un detecteur se valide par
ses faux positifs autant que par ses faux negatifs. Sans lui, une sonde qui
revoque TOUT signal de fusion (donc qui rend la surface inoperante) passerait
les deux premiers tests.

Tri-etat : la sonde rend ``True`` (revocation posterieure trouvee), ``False``
(rien apres la fusion) ou ``None`` (illisible). Seul ``True`` revoque ;
``None`` est **fail-CLOSED** -- sur un signal deja etabli, une lecture
impossible ne doit pas re-servir du travail que le fil a peut-etre declare
non livre.
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import pick_idle_grain as pig  # noqa: E402

from pick_idle_grain import (  # noqa: E402
    _DELIVERED_MARKER_REVOKED_RE,
    delivered_signal_reason,
    revocation_probe_inert,
    revoked_after_merge_signal,
)

# ---------------------------------------------------------------------------
# Dates REELLES de #15002, relevees sur le depot le 2026-11-03 :
#   gh pr list --state merged --search '15002 in:title,body'  (ancre #15002)
#   gh issue view 15002 --json comments                        (marqueurs)
# ---------------------------------------------------------------------------
# PR fusionnees citant #15002 par ancre, de la plus recente a la plus ancienne
# (les plus pertinentes pour ce cas) :
#   22939  2026-10-27T18:35:42Z
#   20841  2026-10-24T00:31:46Z
#   21379  2026-10-21T04:52:41Z
#   ...
MERGE_15002_AFTER_REVOCATION = "2026-10-27T18:35:42Z"  # PR #22939
MERGE_15002_BEFORE_REVOCATION = "2026-10-24T00:31:46Z"  # PR #20841

# Revisions postees sur #15002, verbatim du fil :
#   2026-10-12T09:13:45Z  [NOT-DELIVERED] Livraison partielle, verifiee par
#                         le coordinateur le 1...
#   2026-10-12T22:33:56Z  [NOT-DELIVERED] Livraison partielle, verifiee par
#                         le coordinateur le 1...
#   2026-10-25T12:44:47Z  [NOT-DELIVERED] lane myia-ai-01:CoursIA --
#                         instruction de fermeture du...
NOT_DELIVERED_15002 = "2026-10-25T12:44:47Z"


def _stub_snapshot(monkeypatch, comments):
    """Remplace le snapshot local des commentaires (#22630) par une fixture.

    On ne teste pas `_snapshot_comments` ici : il a ses propres tests. Ce qui
    est sous test, c'est la lecture des horodatages et la comparaison a la
    date de fusion.
    """
    monkeypatch.setattr(pig, "_snapshot_comments", lambda _n: comments)


# ---------------------------------------------------------------------------
# 1. La revoqueresse elle-meme
# ---------------------------------------------------------------------------

def test_revocation_after_merge_is_detected(monkeypatch):
    """Exigence 1, au niveau de la sonde : la revocation posterieure est vue."""
    _stub_snapshot(monkeypatch, [
        {"body": "[NOT-DELIVERED] livraison partielle",
         "createdAt": NOT_DELIVERED_15002},
    ])
    assert revoked_after_merge_signal(
        15002, "myia-po-2025:CoursIA", MERGE_15002_BEFORE_REVOCATION) is True


def test_revocation_before_merge_is_not_detected(monkeypatch):
    """Exigence 3, au niveau de la sonde : l'anterieure ne revoque rien."""
    _stub_snapshot(monkeypatch, [
        {"body": "[NOT-DELIVERED] livraison partielle",
         "createdAt": NOT_DELIVERED_15002},
    ])
    assert revoked_after_merge_signal(
        15002, "myia-po-2025:CoursIA", MERGE_15002_AFTER_REVOCATION) is False


def test_two_revocations_either_side_of_the_merge(monkeypatch):
    """Frontiere exacte : deux marqueurs, un de chaque cote.

    Seul celui qui suit la fusion compte -- une sonde qui se contente de
    « il existe un marqueur quelque part » echoue ici.
    """
    _stub_snapshot(monkeypatch, [
        {"body": "[NOT-DELIVERED] avant", "createdAt": "2026-10-12T09:13:45Z"},
        {"body": "[NOT-DELIVERED] apres", "createdAt": NOT_DELIVERED_15002},
    ])
    assert revoked_after_merge_signal(
        15002, None, MERGE_15002_BEFORE_REVOCATION) is True
    assert revoked_after_merge_signal(
        15002, None, MERGE_15002_AFTER_REVOCATION) is False


def test_marker_in_prose_does_not_revoke(monkeypatch):
    """Le marqueur se lit en TETE de commentaire, comme partout ailleurs.

    Une phrase qui parle du marqueur au fil du texte ne revoque pas : sinon
    un commentaire expliquant la regle revoquerait toutes les issues qu'il
    cite.
    """
    _stub_snapshot(monkeypatch, [
        {"body": "Pour rappel, le marqueur [NOT-DELIVERED] se pose en tete.",
         "createdAt": NOT_DELIVERED_15002},
    ])
    assert revoked_after_merge_signal(
        15002, None, MERGE_15002_BEFORE_REVOCATION) is False


def test_marker_heading_forms_are_recognised():
    """Les deux formes en tete reconnues par le garde de marqueur."""
    for body in (
        "[NOT-DELIVERED] livraison partielle",
        "  [NOT-DELIVERED] livraison partielle",
        "## [NOT-DELIVERED] livraison partielle",
        "[INFO] candidate-delivered-revoked -- la PR precedente n'a rien livre",
    ):
        assert _DELIVERED_MARKER_REVOKED_RE.search(body), body


def test_unreadable_snapshot_fails_closed(monkeypatch):
    """Tri-etat : illisible -> ``None``, jamais ``False``.

    `None` n'est pas une absence de revocation, c'est une absence de mesure.
    Le rendu `False` ferait passer une panne de lecture pour une preuve
    d'absence -- c'est le mode d'echec que le reste du picker combat.
    """
    monkeypatch.setattr(pig, "_snapshot_comments", lambda _n: None)
    monkeypatch.setattr(pig.subprocess, "run", _boom)
    assert revoked_after_merge_signal(
        15002, None, MERGE_15002_BEFORE_REVOCATION) is None


def test_missing_merge_date_is_unmeasurable():
    """Sans date de fusion, il n'y a pas d'ordre a etablir -> ``None``."""
    assert revoked_after_merge_signal(15002, None, None) is None
    assert revoked_after_merge_signal(15002, None, "pas une date") is None


def test_comment_without_timestamp_is_ignored(monkeypatch):
    """Une revocation non horodatee ne peut pas etre situee : ignoree.

    Le repli REST de `_snapshot_comments` rend des corps SANS horodatage
    (#22630). Les compter comme posterieures revoquerait a l'aveugle.
    """
    _stub_snapshot(monkeypatch, [
        {"body": "[NOT-DELIVERED] sans date"},
    ])
    assert revoked_after_merge_signal(
        15002, None, MERGE_15002_BEFORE_REVOCATION) is False


# ---------------------------------------------------------------------------
# 2. Effet sur la surface « PR MERGEE » de delivered_signal_reason
# ---------------------------------------------------------------------------

ITEM_15002 = {"number": 15002, "title": "cas reel", "labels": []}


def test_merged_pr_signal_revoked_after_merge_stops_excluding():
    """Exigence 1 + 2 bout en bout : l'issue redevient un grain servable."""
    reason = delivered_signal_reason(
        ITEM_15002,
        lane="myia-po-2025:CoursIA",
        probe=lambda *_a, **_k: False,
        merged_pr_probe=lambda *_a, **_k: MERGE_15002_BEFORE_REVOCATION,
        revocation_probe=lambda _n, _l, merged: merged ==
        MERGE_15002_BEFORE_REVOCATION,
    )
    assert reason is None


def test_merged_pr_signal_kept_when_revocation_precedes_merge():
    """Controle negatif bout en bout : le signal reste, l'issue est ecartee."""
    reason = delivered_signal_reason(
        ITEM_15002,
        lane="myia-po-2025:CoursIA",
        probe=lambda *_a, **_k: False,
        merged_pr_probe=lambda *_a, **_k: MERGE_15002_AFTER_REVOCATION,
        revocation_probe=lambda _n, _l, merged: merged !=
        MERGE_15002_AFTER_REVOCATION,
    )
    assert reason is not None
    assert "PR MERGEE" in reason


def test_merged_pr_signal_kept_when_revocation_probe_is_unmeasurable():
    """Fail-CLOSED : une sonde muette ne rend pas le grain a la production."""
    reason = delivered_signal_reason(
        ITEM_15002,
        lane="myia-po-2025:CoursIA",
        probe=lambda *_a, **_k: False,
        merged_pr_probe=lambda *_a, **_k: MERGE_15002_BEFORE_REVOCATION,
        revocation_probe=lambda _n, _l, _m: None,
    )
    assert reason is not None
    assert "PR MERGEE" in reason


def test_no_merge_means_no_revocation_call():
    """Sans signal de fusion, la sonde n'est pas appelee (budget partage)."""
    calls = []

    def _probe(*args):
        calls.append(args)
        return True

    reason = delivered_signal_reason(
        ITEM_15002,
        lane="myia-po-2025:CoursIA",
        probe=lambda *_a, **_k: False,
        merged_pr_probe=lambda *_a, **_k: False,
        revocation_probe=_probe,
    )
    assert reason is None
    assert calls == []


def test_default_revocation_probe_is_inert():
    """Retro-compatibilite : sans injection, aucune revocation.

    Les appelants existants (52 tests) injectent `merged_pr_probe` seul ;
    ils doivent garder exactement leur comportement anterieur.
    """
    assert revocation_probe_inert(15002, None, MERGE_15002_BEFORE_REVOCATION) \
        is False
    reason = delivered_signal_reason(
        ITEM_15002,
        lane="myia-po-2025:CoursIA",
        probe=lambda *_a, **_k: False,
        merged_pr_probe=lambda *_a, **_k: MERGE_15002_BEFORE_REVOCATION,
    )
    assert reason is not None
    assert "PR MERGEE" in reason


def test_label_surface_still_wins_over_revocation():
    """Une revocation ne rouvre pas une issue portant le label de livraison.

    Le label est un acte explicite pose par le workflow advisory ; il n'est
    pas revoque par un commentaire. Seule la surface « PR MERGEE » l'est.
    """
    item = {"number": 15002, "title": "x", "labels": ["candidate-delivered"]}
    calls = []

    def _probe(*args):
        calls.append(args)
        return True

    reason = delivered_signal_reason(
        item,
        lane="myia-po-2025:CoursIA",
        probe=lambda *_a, **_k: False,
        merged_pr_probe=lambda *_a, **_k: MERGE_15002_BEFORE_REVOCATION,
        revocation_probe=_probe,
    )
    assert reason is not None
    assert "label" in reason
    assert calls == []


def _boom(*_args, **_kwargs):
    raise RuntimeError("gh indisponible")
