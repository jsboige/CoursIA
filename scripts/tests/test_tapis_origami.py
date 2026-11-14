"""Tests de `coordination/tapis_origami.py` -- le parcage Origami du tapis rapide.

Le parquet Origami (#24373) : un EPIC dont le pli suivant n'est pas deplie
n'est pas servi aux lanes -- c'est le geste du coordinateur. Le tapis rapide
(#26523) l'applique, avec une sonde de livraison fondee sur les lectures
groupees de `gh_bulk` et la mesure des plis venue de `origami_parking`.

Aucun test ne touche le reseau : le module `origami_parking` est remplace par
un faux, et la sonde de livraison est verifiee sur les citations de la lecture.
"""
import ast
import json
import sys
from datetime import UTC, datetime
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from coordination import belt_queues, gh_bulk
from coordination import tapis_origami as to
from coordination import tapis_rapide as tr

pytestmark = pytest.mark.usefixtures("forbid_shell_escape")

NOW = datetime(2026, 11, 14, 12, 0, tzinfo=UTC)
LANE = "myia-ai-01:CoursIA-2"
COORD = Path(__file__).resolve().parents[1] / "coordination"

TITRE_EPIC = "[EPIC Origami] Le chantier long"
TITRE_PLI = "[Epic Origami #19309 - Pli 2] Un pli"


class Op:
    """Un faux `origami_parking` : aucun appel reseau, tout est injecte."""

    def __init__(self, verdicts=None, cache=None, echec=None, mesure=None):
        self.verdicts = verdicts if verdicts is not None else []
        self.cache = cache
        self.echec = echec
        self.mesure = mesure
        self.sauvegarde = None
        self.probe = None

    def origami_epic_numbers(self, pool):
        return [int(it["number"]) for it in pool if "origami" in (it.get("title") or "").lower()]

    def load_cache(self):
        return self.cache

    def save_cache(self, verdicts):
        self.sauvegarde = verdicts

    def measure(self, pool, delivered_probe=None):
        if self.echec is not None:
            raise self.echec
        self.probe = delivered_probe
        return self.mesure(pool) if self.mesure else self.verdicts


def issue(n, titre="", body="", labels=(), comments=(), cree="2026-10-01T00:00:00Z"):
    return {"number": n, "title": titre or f"Grain {n}", "body": body, "labels": list(labels),
            "created_at": cree, "comments": list(comments), "comments_total": len(comments)}


def lecture(issues, citations=None):
    return gh_bulk.Lecture(issues=list(issues), prs=[], citations=citations or {})


def verdict(parked=True, epic=19309, pli=4):
    return {"epic": epic, "parked": parked, "measured": True,
            "reason": (f"tous les plis materialises sont termines (dernier pli {pli - 1}) "
                       f"et le pli {pli} n'est pas annonce -- depliage reserve au coordinateur"
                       if parked else f"pli {pli} annonce mais non materialise"),
            "next_pli": pli, "title": TITRE_EPIC}


# --- le parcage -------------------------------------------------------------

def test_un_epic_origami_parque_est_ecarte_du_tirage():
    lec = lecture([issue(19309, titre=TITRE_EPIC), issue(7, titre="Grain ordinaire")])
    parcs, etat = to.mesurer(lec, op=Op(verdicts=[verdict()]))
    assert list(parcs) == [19309] and etat["measured"] is True
    tous = tr.etats(lec, LANE, NOW)
    tr._parquer(tous, parcs)
    e = next(e for e in tous if e.numero == 19309)
    assert e.ecart == "ORIGAMI" and "depliage reserve au coordinateur" in e.motif
    file = tr.ordonner(tous, LANE, NOW, 8)
    assert [e.numero for e in file] == [7]  # l'EPIC parque n'est pas servi


def test_le_meme_epic_est_servi_une_fois_le_pli_deplie():
    lec = lecture([issue(19309, titre=TITRE_EPIC), issue(7, titre="Grain ordinaire")])
    parcs, etat = to.mesurer(lec, op=Op(verdicts=[verdict(parked=False)]))
    assert parcs == {} and etat["measured"] is True
    tous = tr.etats(lec, LANE, NOW)
    tr._parquer(tous, parcs)
    file = tr.ordonner(tous, LANE, NOW, 8)
    assert 19309 in [e.numero for e in file]


def test_le_parcage_ne_touche_pas_les_grains_voisins():
    lec = lecture([issue(19309, titre=TITRE_EPIC), issue(7), issue(8)])
    parcs, _ = to.mesurer(lec, op=Op(verdicts=[verdict()]))
    tous = tr.etats(lec, LANE, NOW)
    tr._parquer(tous, parcs)
    assert [e.ecart for e in tous if e.numero in (7, 8)] == [None, None]


def test_un_ecart_precedent_garde_la_priorite():
    """Un EPIC deja livre reste livre : son motif est plus utile a la lane."""
    lec = lecture([issue(19309, titre=TITRE_EPIC, labels=["candidate-delivered"])])
    parcs, _ = to.mesurer(lec, op=Op(verdicts=[verdict()]))
    tous = tr.etats(lec, LANE, NOW)
    tr._parquer(tous, parcs)
    e = next(e for e in tous if e.numero == 19309)
    assert e.ecart == "LABEL"


# --- la mesure --------------------------------------------------------------

def test_aucun_epic_origami_dans_le_pool_mesure_vide_faute_de_parcage():
    lec = lecture([issue(7), issue(8)])
    parcs, etat = to.mesurer(lec, op=Op())
    assert parcs == {}
    assert etat["measured"] is True and etat["epics"] == 0
    assert etat["reason"] == "aucun EPIC Origami dans le pool"


def test_mesure_impossible_nomme_sa_cause_et_ne_parque_rien():
    lec = lecture([issue(19309, titre=TITRE_EPIC)])
    parcs, etat = to.mesurer(lec, op=Op(echec=RuntimeError("boum")))
    assert parcs == {}
    assert etat["measured"] is False and "boum" in etat["reason"]
    assert "details" not in etat  # jamais une liste vide qui se lirait « rien a parquer »


def test_rejeu_hors_ligne_dit_quil_ne_sait_pas():
    lec = lecture([issue(19309, titre=TITRE_EPIC)])
    parcs, etat = to.mesurer(lec, op=Op(), cache=False, reseau=False)
    assert parcs == {} and etat["measured"] is False
    assert "hors ligne" in etat["reason"]


def test_le_cache_machine_evite_la_mesure():
    lec = lecture([issue(19309, titre=TITRE_EPIC)])
    op = Op(cache={"verdicts": [verdict()]})
    parcs, etat = to.mesurer(lec, op=op)
    assert list(parcs) == [19309] and op.sauvegarde is None  # le cache a suffi


def test_une_mesure_fraiche_est_mise_en_cache():
    lec = lecture([issue(19309, titre=TITRE_EPIC)])
    op = Op(verdicts=[verdict()])
    to.mesurer(lec, op=op)
    assert op.sauvegarde and op.sauvegarde[0]["epic"] == 19309


def test_la_sonde_de_livraison_vient_des_citations_groupees():
    """Un pli est livre quand un commit de fusion le cite : la lecture groupee
    suffit, aucune lecture par issue."""
    lec = lecture([issue(19309, titre=TITRE_EPIC)],
                  citations={42: [{"sha": "abc", "date": "2026-11-01T00:00:00Z"}]})
    op = Op(verdicts=[verdict()])
    to.mesurer(lec, op=op)
    assert op.probe is not None
    assert op.probe(42) is True and op.probe(43) is False


# --- la forme du JSON -------------------------------------------------------

def test_le_bloc_json_porte_la_forme_du_tableau_du_coordinateur():
    lec = lecture([issue(19309, titre=TITRE_EPIC)])
    _, etat = to.mesurer(lec, op=Op(verdicts=[verdict()]))
    assert etat["measured"] is True and etat["parked"] == [19309]
    detail = etat["details"][0]
    assert detail["epic"] == 19309 and detail["parked"] is True
    assert detail["next_pli"] == 4 and detail["title"] == TITRE_EPIC


def test_le_tableau_du_coordinateur_affiche_la_section_sans_non_mesure():
    lec = lecture([issue(19309, titre=TITRE_EPIC)])
    _, etat = to.mesurer(lec, op=Op(verdicts=[verdict()]))
    b = belt_queues.board({"picks": [], "origami_parking": etat}, [], None, NOW)
    rendu = belt_queues.render_board(b)
    assert "#19309" in rendu and "non mesure" not in rendu


def test_un_bloc_non_mesure_dit_pourquoi():
    b = belt_queues.board({"picks": [], "origami_parking": {"measured": False,
                                                           "reason": "rejeu hors ligne"}},
                          [], None, NOW)
    assert "non mesure : rejeu hors ligne" in belt_queues.render_board(b)


# --- structure --------------------------------------------------------------

def test_plafond_de_lignes_du_module():
    """Un depassement se paie en extrayant un module, pas en relevant le plafond."""
    texte = (COORD / "tapis_origami.py").read_text(encoding="utf-8")
    assert len(texte.splitlines()) <= 160
    for noeud in ast.walk(ast.parse(texte)):
        if isinstance(noeud, ast.FunctionDef | ast.AsyncFunctionDef):
            assert noeud.end_lineno - noeud.lineno + 1 <= 60, noeud.name
