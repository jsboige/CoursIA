#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Tests du champ `resource_cost` du catalogue (cout d'execution et de creation).

Ce que ces tests epinglent, par ordre de degat s'ils cassent :

1. **Une absence de mesure ne devient jamais « leger ».** C'est la seule
   propriete qui separe ce champ d'un champ decoratif : un notebook qu'on n'a
   pas pu chronometrer rend UNKNOWN, et un historique coupe rend
   UNKNOWN/TRUNCATED. Rendre LIGHT ferait passer pour bon marche ce que
   l'instrument n'a pas ouvert.
2. **Un horizon de clone n'est pas une date de creation.** Sur un clone
   shallow, `first_commit` vaut la date de coupe ; le champ le tait plutot que
   de fabriquer un age.
3. **Une duree aberrante est ecartee, pas additionnee.** Un horodatage qui
   recule ou un ecart de plusieurs jours est un artefact, pas une mesure.
4. **Les seuils discriminent.** Un champ qui rend la meme valeur partout ne
   renseigne personne -- c'est le defaut qu'on vient de mesurer sur les trois
   autres axes declaratifs du catalogue (#17217).

Run: python -m pytest scripts/notebook_tools/tests/test_resource_cost.py
"""
import datetime as dt
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from generate_catalog import (  # noqa: E402
    classify_creation_cost,
    measure_execution_cost,
)

NO_REQ = {"requires_api": False, "requires_gpu": False,
          "requires_cloud": False, "requires_wsl": False}


def timed(seconds: float, start: str = "2026-09-21T10:00:00.000000Z") -> dict:
    """Cellule code portant un couple d'horodatages nbclient."""
    began = dt.datetime.fromisoformat(start.replace("Z", "+00:00"))
    ended = began + dt.timedelta(seconds=seconds)
    return {"cell_type": "code", "source": "x = 1", "metadata": {"execution": {
        "iopub.execute_input": began.isoformat().replace("+00:00", "Z"),
        "shell.execute_reply": ended.isoformat().replace("+00:00", "Z"),
    }}}


def untimed() -> dict:
    return {"cell_type": "code", "source": "x = 1", "metadata": {}}


# --- 1. une absence de mesure n'est jamais « leger » -------------------------

def test_sans_horodatage_la_classe_est_unknown_jamais_light():
    out = measure_execution_cost([untimed(), untimed()], NO_REQ)
    assert out["class"] == "UNKNOWN"
    assert out["coverage"] == "NONE"
    assert out["wall_seconds"] is None


def test_un_notebook_sans_cellule_code_est_unknown():
    out = measure_execution_cost([], NO_REQ)
    assert out["class"] == "UNKNOWN"
    assert out["coverage"] == "NONE"


def test_sans_historique_la_creation_est_unknown():
    assert classify_creation_cost(None)["class"] == "UNKNOWN"
    assert classify_creation_cost(None)["history"] == "ABSENT"
    assert classify_creation_cost({})["class"] == "UNKNOWN"


def test_un_git_meta_sans_drapeau_est_traite_comme_coupe():
    """Fail-closed : le defaut de `history_truncated` est True. Un appelant qui
    oublie de le poser obtient UNKNOWN, pas une classe inventee."""
    out = classify_creation_cost({"revisions": 9, "authors": 2,
                                  "last_validation": "2026-09-21"})
    assert out["class"] == "UNKNOWN"
    assert out["history"] == "TRUNCATED"


# --- 2. un horizon de clone n'est pas une date de creation -------------------

def test_sur_historique_coupe_la_date_de_creation_est_tue():
    out = classify_creation_cost({"revisions": 13, "authors": 2,
                                  "first_commit": "2026-08-25",
                                  "last_validation": "2026-09-21",
                                  "history_truncated": True})
    assert out["class"] == "UNKNOWN"
    assert out["history"] == "TRUNCATED"
    assert out["first_commit"] == "", "la date de coupe n'est pas une creation"
    assert out["span_days"] is None
    # les comptes restent rendus : ils sont vrais POUR LA FENETRE
    assert out["revisions"] == 13
    assert out["authors"] == 2


def test_sur_historique_complet_la_classe_et_l_age_existent():
    out = classify_creation_cost({"revisions": 3, "authors": 1,
                                  "first_commit": "2026-01-01",
                                  "last_validation": "2026-01-31",
                                  "history_truncated": False})
    assert out["class"] == "MODERATE"
    assert out["history"] == "COMPLETE"
    assert out["first_commit"] == "2026-01-01"
    assert out["span_days"] == 30


# --- 3. une duree aberrante est ecartee, pas additionnee ---------------------

def test_un_horodatage_qui_recule_n_est_pas_une_mesure():
    negatif = timed(5.0)
    negatif["metadata"]["execution"]["shell.execute_reply"] = "2026-09-21T09:00:00.000000Z"
    out = measure_execution_cost([negatif, timed(4.0)], NO_REQ)
    assert out["wall_seconds"] == 4.0, "l'aberrante est ecartee du total"
    assert out["cells_timed"] == 1
    assert out["coverage"] == "PARTIAL", "et decomptee de la couverture"


def test_un_ecart_de_plusieurs_jours_est_ecarte():
    out = measure_execution_cost([timed(200000.0), timed(3.0)], NO_REQ)
    assert out["wall_seconds"] == 3.0
    assert out["cells_timed"] == 1


def test_un_horodatage_illisible_n_interrompt_pas_la_mesure():
    casse = timed(5.0)
    casse["metadata"]["execution"]["iopub.execute_input"] = "pas-une-date"
    out = measure_execution_cost([casse, timed(7.0)], NO_REQ)
    assert out["wall_seconds"] == 7.0


# --- 4. les seuils discriminent ----------------------------------------------

def test_les_quatre_classes_d_execution_sont_atteignables():
    cas = [(1.0, "LIGHT"), (59.0, "LIGHT"), (60.0, "MODERATE"),
           (599.0, "MODERATE"), (600.0, "HEAVY"), (3599.0, "HEAVY"),
           (3600.0, "VERY_HEAVY"), (17761.9, "VERY_HEAVY")]
    for seconds, attendu in cas:
        got = measure_execution_cost([timed(seconds)], NO_REQ)["class"]
        assert got == attendu, "%s s -> %s (attendu %s)" % (seconds, got, attendu)


def test_les_quatre_classes_de_creation_sont_atteignables():
    complet = {"authors": 1, "first_commit": "2026-01-01",
               "last_validation": "2026-02-01", "history_truncated": False}
    for revisions, attendu in ((1, "LIGHT"), (2, "LIGHT"), (3, "MODERATE"),
                               (11, "MODERATE"), (12, "HEAVY"), (34, "HEAVY"),
                               (35, "VERY_HEAVY"), (64, "VERY_HEAVY")):
        got = classify_creation_cost(dict(complet, revisions=revisions))["class"]
        assert got == attendu, "%d revisions -> %s (attendu %s)" % (revisions, got, attendu)


# --- la couverture dit sur quoi la mesure porte ------------------------------

def test_la_couverture_partielle_est_nommee_et_la_classe_porte_sur_le_mesure():
    out = measure_execution_cost([timed(10.0), untimed(), untimed()], NO_REQ)
    assert out["coverage"] == "PARTIAL"
    assert out["cells_timed"] == 1 and out["cells_code"] == 3
    assert out["class"] == "LIGHT"


# --- les ressources externes sont rendues, elles ne corrigent pas la classe ---

def test_une_ressource_externe_est_rendue_sans_corriger_la_classe():
    """Le temps de paroi d'un appel d'API est de la latence, pas le calcul
    brule a l'autre bout. Corriger la classe fabriquerait un chiffre que rien
    ne mesure ; la nommer a cote laisse le lecteur juger."""
    req = dict(NO_REQ, requires_api=True, requires_gpu=True)
    out = measure_execution_cost([timed(2.0)], req)
    assert out["class"] == "LIGHT"
    assert out["external"] == ["api", "gpu"]
