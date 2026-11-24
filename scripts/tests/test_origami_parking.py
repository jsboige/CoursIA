#!/usr/bin/env python3
"""Tests for ``scripts/coordination/origami_parking.py`` -- the Origami parking organ (#24373).

The organ recognises the barrier "the next fold is not unfolded" on an Origami
EPIC, parks it (it is no longer served to worker lanes), and makes it visible
to the coordinator. The tests pin the decision layer on four controls:

* **positive** -- #19309 and #20404 (real shapes): every materialised fold is
  finished, the next fold is not announced -> parked;
* **negative 1** -- an Origami EPIC with an OPEN, undelivered fold stays
  served (it is actionable work, not a barrier);
* **negative 2** -- a non-Origami EPIC is never a candidate, so a
  ``[RELEASED]`` on it keeps the #21721 semantics (the item returns to the
  fleet).

They also pin the two traps measured on the real fil: a lane that *quotes* the
missing marker (``aucun [PLI 4 DEPLIE]``) does not declare an unfolding, and a
fold that is closed but not delivered is still finished.

Never calls ``gh``.
Run: python -m pytest scripts/tests/test_origami_parking.py
"""
from __future__ import annotations

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "coordination"))

import origami_parking as op  # noqa: E402


def _epic(number, title="[Epic Origami] Exemple", body="", **kw):
    item = {"number": number, "title": title, "body": body, "labels": ["EPIC"]}
    item.update(kw)
    return item


def _fold(number, epic, pli=None, state="CLOSED", delivered=True, title=None):
    body = f"Part of #{epic}"
    return {"number": number, "title": title or f"[Origami pli {pli}] Issue",
            "body": body, "pli": pli, "state": state, "delivered": delivered}


def _comment(body, at="2026-10-30T00:00:00Z", author="myia-ai-01"):
    return {"createdAt": at, "body": body, "author": {"login": author}}


# ---------------------------------------------------------------------------
# Positive : les deux controles positifs du dispatch
# ---------------------------------------------------------------------------

def test_epic_19309_est_parque():
    """#19309 : plis 1-3 fermes, aucun marqueur de depliage du pli 4."""
    epic = _epic(19309, "[Epic] Completer la constellation causale (format Origami)")
    folds = [_fold(19310, 19309, 1), _fold(20972, 19309, 2), _fold(21680, 19309, 3)]
    comments = [
        _comment("> Etat mesure au 2026-10-05 ... **Pli 1 ouvert** : #19310"),
        _comment("[INFO] Pli 2 materialise : sous-issue #20972 creee"),
        _comment("[INFO] Pli 3 materialise : sous-issue #21680 creee"),
    ]
    verdict = op.parking_verdict(epic, folds, op.unfolded_declarations(comments))
    assert verdict["parked"] is True
    assert verdict["next_pli"] == 4


def test_epic_20404_est_parque_meme_avec_des_plis_ouverts_livres():
    """#20404 : les plis 2 et 3 sont OUVERTS mais LIVRES (PR #21795, #23745).

    C'est le controle positif du dispatch : sous la lecture « tous les plis sont
    fermes », il ne serait pas parque. La lecture « termines » (ferme ou
    livre) est la seule sous laquelle il tient.
    """
    epic = _epic(20404, "EPIC Origami: Thurston")
    folds = [_fold(20426, 20404, 1, state="CLOSED"),
             _fold(21701, 20404, 2, state="OPEN", delivered=True),
             _fold(23742, 20404, 3, state="OPEN", delivered=True)]
    comments = [_comment("[PLI 1 DEPLIE] -- 12/10/2026 Sous-issue creee : #20426")]
    verdict = op.parking_verdict(epic, folds, op.unfolded_declarations(comments))
    assert verdict["parked"] is True


# ---------------------------------------------------------------------------
# Controle negatif 1 : un pli ouvert et non livre reste servi
# ---------------------------------------------------------------------------

def test_un_pli_ouvert_non_livre_garde_l_epic_servi():
    epic = _epic(18205, "EPIC origami : geometrie differentielle en Lean")
    folds = [_fold(23499, 18205, 2, state="OPEN", delivered=False)]
    verdict = op.parking_verdict(epic, folds, [])
    assert verdict["parked"] is False
    assert "actionnable" in verdict["reason"]
    assert verdict["open_folds"][0]["number"] == 23499


# ---------------------------------------------------------------------------
# Controle negatif 2 : un EPIC non-Origami n'est jamais candidat
# ---------------------------------------------------------------------------

def test_un_epic_non_origami_n_est_jamais_candidat():
    """Un EPIC qui porte un [RELEASED] garde la semantique #21721.

    L'organe ne le touche pas : il ne devient ni candidat ni parque, donc le
    tapis continue de le servir apres une main rendue.
    """
    pool = [{"number": 21721, "title": "[Epic] Un chantier ordinaire",
             "body": "rien ici ne parle d'origami", "labels": ["EPIC"]}]
    assert op.origami_epic_numbers(pool) == []


def test_un_epic_qui_parle_d_origami_dans_son_corps_seul_n_est_pas_candidat():
    """#13906 : « Les body d'Epic ne sont jamais reecrits » mentionne origami.

    Le titre ne porte pas la mention : le candidat est ecarte.
    """
    pool = [{"number": 13906,
             "title": "[EPIC] Les body d'Epic ne sont jamais reecrits",
             "body": "le format Origami est cite ici pour l'exemple",
             "labels": ["EPIC"]}]
    assert op.origami_epic_numbers(pool) == []


def test_un_pli_n_est_pas_un_epic():
    """Une sous-issue qui porte un numero de pli n'est pas un EPIC Origami."""
    pool = [{"number": 22178,
             "title": "[Epic Origami #19742 - Pli 2] Programmes simples",
             "body": "Part of #19742", "labels": []}]
    assert op.origami_epic_numbers(pool) == []


# ---------------------------------------------------------------------------
# Les deux pieges mesures sur le fil reel
# ---------------------------------------------------------------------------

def test_une_mention_du_marqueur_ABSENT_ne_declare_pas_un_depliage():
    """Une lane qui RECITE le marqueur qu'elle n'a pas trouve ne declenche rien.

    C'est la forme mesuree sur #19309 : six commentaires de lanes y citent
    `[PLI 4 DEPLIE]` en expliquant qu'il est absent. Sans ce filtre, le pli 4
    paraitrait deplie et l'EPIC sortirait du parcage.
    """
    comments = [
        _comment("[RELEASED] lane myia-po-2024:CoursIA -- aucun commentaire "
                 "[PLI 4 DEPLIE] du coordinateur depuis le dernier [RELEASED]"),
        _comment("[RELEASED] lane myia-po-2027:CoursIA -- EPIC Origami non "
                 "servable par un worker : le pli 4 n'est pas deplie"),
        _comment("[INFO] Pli 3 materialise : sous-issue #21680 creee"),
    ]
    declarations = op.unfolded_declarations(comments)
    assert [d["pli"] for d in declarations] == [3]


def test_une_declaration_de_depliage_est_lue():
    comments = [
        _comment("[PLI 4 DEPLIE] -- 30/10/2026 Sous-issue creee : #21680"),
        _comment("[INFO] Pli 5 materialise : sous-issue #21785 creee"),
    ]
    assert sorted(d["pli"] for d in op.unfolded_declarations(comments)) == [4, 5]


def test_un_pli_annonce_au_dela_du_dernier_materialise_resort_de_parcage():
    """Le pli suivant annonce fait resortir l'EPIC du parcage."""
    epic = _epic(19309, "[Epic] constellation causale (format Origami)")
    folds = [_fold(19310, 19309, 1), _fold(20972, 19309, 2), _fold(21680, 19309, 3)]
    comments = [_comment("[PLI 4 DEPLIE] -- 03/11/2026 Sous-issue a creer")]
    verdict = op.parking_verdict(epic, folds, op.unfolded_declarations(comments))
    assert verdict["parked"] is False
    assert "annonce" in verdict["reason"]


# ---------------------------------------------------------------------------
# Detection des plis
# ---------------------------------------------------------------------------

def test_le_numero_de_pli_vient_du_titre_puis_du_corps():
    assert op.declared_pli("[Origami pli 3] Une issue") == 3
    assert op.declared_pli("Pli 0/6 de l'Epic") == 0
    assert op.declared_pli("rien ici") is None


def test_une_sous_issue_sans_parent_n_est_pas_un_pli():
    child = {"number": 5, "title": "[Origami pli 1] X", "body": "rien"}
    assert not op.is_fold_of(child, 19309)
    child = {"number": 6, "title": "[Origami pli 1] X", "body": "Part of #19309"}
    assert op.is_fold_of(child, 19309)


def test_le_corps_n_est_lu_que_dans_ses_trois_premieres_lignes():
    """Une sous-issue qui cite un pli plus loin n'en est pas un."""
    child = {"number": 7, "title": "[RL] Auto-jeu",
             "body": "Part of #18220\n\n## Suite\n\nle pli 3 garde des lignes ouvertes"}
    assert op.fold_pli(child) is None


# ---------------------------------------------------------------------------
# La mesure ne parque rien quand elle n'a rien mesure
# ---------------------------------------------------------------------------

def test_absence_de_pli_connu_ne_parque_rien():
    epic = _epic(21310, "EPIC origami : Project DarkSnail")
    verdict = op.parking_verdict(epic, [], [])
    assert verdict["parked"] is False
    assert verdict["measured"] is False


@pytest.mark.parametrize("state,delivered,expected", [
    ("CLOSED", False, True),   # ferme = termine, meme sans livraison tracable
    ("OPEN", True, True),       # livre = termine
    ("OPEN", False, False),     # ouvert et non livre = actionnable
])
def test_un_pli_est_termine_selon_son_etat(state, delivered, expected):
    epic = _epic(1, "[Epic Origami] X")
    folds = [{"number": 2, "pli": 1, "state": state, "delivered": delivered}]
    verdict = op.parking_verdict(epic, folds, [])
    assert verdict["parked"] is expected


# ---------------------------------------------------------------------------
# L'integration dans le tapis
# ---------------------------------------------------------------------------

def _pool_item(number, title, last_delivery_stamp=None):
    return {"number": number, "title": title, "body": "",
            "labels": ["EPIC"], "last_delivery_stamp": last_delivery_stamp}


def test_le_tapis_ecarte_un_epic_parque(monkeypatch):
    """Le parcage retire l'EPIC du tirage et le nomme dans la mesure."""
    import pick_idle_grain as pig

    def _fake_measure(pool, delivered_probe=None):
        return [{"epic": 19309, "parked": True,
                 "reason": "tous les plis materialises sont termines",
                 "title": "[Epic] constellation causale", "next_pli": 4}]

    monkeypatch.setattr(pig.origami_parking, "measure", _fake_measure)
    parked, state = pig._origami_parking_state([_pool_item(19309, "[Epic] X")])
    assert list(parked) == [19309]
    assert state["measured"] is True
    assert state["parked"] == [19309]


def test_le_tapis_ne_parque_rien_sans_mesure(monkeypatch):
    """Fail-OPEN : une mesure qui echoue ne retire aucun grain du tapis."""
    import pick_idle_grain as pig

    def _boom(pool, delivered_probe=None):
        raise RuntimeError("reseau tombe")

    monkeypatch.setattr(pig.origami_parking, "measure", _boom)
    parked, state = pig._origami_parking_state([_pool_item(19309, "[Epic] X")])
    assert parked == {}
    assert state["measured"] is False
    assert "echec" in state["reason"]


def test_la_livraison_d_un_pli_vient_du_corpus_de_prs_du_tapis(monkeypatch):
    """Le probe de livraison lit le pool, pas le reseau."""
    import pick_idle_grain as pig

    seen = {}

    def _fake_measure(pool, delivered_probe=None):
        seen["delivered"] = delivered_probe(23499)
        return []

    monkeypatch.setattr(pig.origami_parking, "measure", _fake_measure)
    pool = [_pool_item(23499, "Pli 2 (#18205) : ...", last_delivery_stamp=None)]
    pig._origami_parking_state(pool)
    assert seen["delivered"] is False

    seen.clear()
    pool = [_pool_item(23499, "Pli 2 (#18205) : ...",
                       last_delivery_stamp="2026-10-30T00:00:00Z")]
    pig._origami_parking_state(pool)
    assert seen["delivered"] is True
