# -*- coding: utf-8 -*-
"""Tests CPU du critere de comparaison du controle d'innocuite (#25492).

Exercent la **regle** du controle, hors ligne : aucune dependance QC, aucun
reseau, aucune dependance lourde (le module `league_control` est pur).

Mesure a l'origine du test (2026-11-09) : le controle comparait la
concatenation des series `ret` et `spy` du graphique `Monthly`, donc la
LONGUEUR des deux graphiques -- il rendait rouge deux executions dont la serie
commune etait identique, pour la seule raison que l'une exposait `spy` et pas
l'autre. La divergence de valeurs, elle, doit toujours etre detectee.

Le test porte sur le critere (`league_control`), pas sur la lecture des
graphiques QC (`league_protocol._compare_monthly` / `_compare_shadow`) :
celle-la passe par la plateforme.

Execution ::

    python -m pytest tests/test_league_control.py -v

(depuis ``MyIA.AI.Notebooks/QuantConnect/projects/LowBeta-Industries-QC``)
"""
from __future__ import annotations

import importlib.util
import json
import sys
from pathlib import Path
from types import SimpleNamespace

import pytest

PROJET = Path(__file__).resolve().parents[1]


def _charger_league_control():
    """Importe le module de production, sans le dupliquer."""
    if str(PROJET) not in sys.path:
        sys.path.insert(0, str(PROJET))
    spec = importlib.util.spec_from_file_location("league_control_sous_test",
                                                  PROJET / "league_control.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


lc = _charger_league_control()

# 2020-01-06, lundi : dix seances consecutives (le validateur de trace refuse
# un calendrier qui saute).
T0 = 1578278400
PAS = 86400


def _points(n: int = 4, debut: float = 0.1, pas: float = 0.1, t0: int = T0):
    """Une serie de points (t, v), rangee par horodatage."""
    return [(t0 + j * PAS, debut + j * pas) for j in range(n)]


def _trace(n: int = 10, delta: float = 0.0):
    """Une trace journaliere (date, valeur), une valeur par seance."""
    return [(f"2020-01-{6 + j:02d}", 100.0 + j + delta) for j in range(n)]


# --------------------------------------------------------------------------
# Le critere serie par serie
# --------------------------------------------------------------------------

def test_exposition_differente_nest_pas_une_divergence():
    """Une serie absente d'un cote est rapportee, pas comptee comme divergence."""
    reference = {"ret": _points(4), "spy": _points(4), "netexp": _points(4)}
    controle = {"ret": _points(4)}
    resultat = lc.compare_series(reference, controle)
    assert resultat["divergence"] == []
    assert resultat["series_communes"] == ["ret"]
    assert resultat["series_seulement_ref"] == ["netexp", "spy"]
    assert resultat["series_seulement_ctl"] == []


def test_divergence_de_valeurs_est_detectee():
    """La porte porte sur les valeurs : une serie qui bouge fait rouge."""
    reference = {"ret": _points(4), "spy": _points(4)}
    controle = {"ret": _points(4, debut=9.9), "spy": _points(4)}
    resultat = lc.compare_series(reference, controle)
    assert resultat["divergence"] == ["ret"]


def test_divergence_de_jours_est_detectee():
    """Un decalage d'horodatage est aussi une divergence de mesure."""
    reference = {"ret": _points(4)}
    controle = {"ret": _points(4, t0=T0 + 10 * PAS)}
    resultat = lc.compare_series(reference, controle)
    assert resultat["divergence"] == ["ret"]


def test_une_serie_en_plus_n_est_pas_une_divergence():
    """Une serie exposee par le seul controle est rapportee, pas reprochee."""
    resultat = lc.compare_series({"ret": _points(4)}, {"ret": _points(4), "spy": _points(4)})
    assert resultat["divergence"] == []
    assert resultat["series_seulement_ctl"] == ["spy"]


def test_aucune_serie_commune_ne_produit_pas_de_divergence():
    """Rien a comparer, donc rien a reprocher."""
    resultat = lc.compare_series({"ret": _points(4)}, {"spy": _points(4)})
    assert resultat["divergence"] == []
    assert resultat["series_communes"] == []


def test_le_nombre_de_points_est_compte_serie_par_serie():
    reference = {"ret": _points(4), "spy": _points(7)}
    controle = {"ret": _points(4), "spy": _points(7)}
    resultat = lc.compare_series(reference, controle)
    assert resultat["points_par_serie"] == {"ret": 4, "spy": 7}


# --------------------------------------------------------------------------
# Le critere de trace journaliere -- ce que le protocole consomme
# --------------------------------------------------------------------------

def test_traces_identiques_ne_divergent_pas():
    resultat = lc.compare_rows(_trace(), _trace())
    assert resultat["divergence"] == []
    assert resultat["points"] == 10
    assert resultat["calendrier_identique"] is True
    assert resultat["valeurs_identiques"] is True
    assert resultat["ecart_max"] == 0.0


def test_trace_divergente_en_valeur_est_detectee():
    resultat = lc.compare_rows(_trace(), _trace(delta=1.0))
    assert resultat["divergence"] == ["trace journaliere"]
    assert resultat["valeurs_identiques"] is False
    assert resultat["ecart_max"] == 1.0


def test_trace_de_calendrier_different_est_detectee():
    """Le calendrier fait partie de la mesure : d'autres seances, c'est une divergence."""
    reference = _trace()
    controle = list(reference)
    controle[0] = ("2019-12-31", reference[0][1])
    resultat = lc.compare_rows(reference, controle)
    assert resultat["divergence"] == ["trace journaliere"]
    assert resultat["calendrier_identique"] is False
    assert resultat["valeurs_identiques"] is True


def test_trace_plus_courte_est_divergente():
    resultat = lc.compare_rows(_trace(10), _trace(8))
    assert resultat["divergence"] == ["trace journaliere"]
    assert resultat["points"] == 10


# --------------------------------------------------------------------------
# Le câblage de production -- les adaptateurs de `league_protocol`
# --------------------------------------------------------------------------

def _charger_league_protocol():
    """Importe le module de production, sans le dupliquer."""
    import importlib.util

    if str(PROJET) not in sys.path:
        sys.path.insert(0, str(PROJET))
    spec = importlib.util.spec_from_file_location("league_protocol_sous_test",
                                                  PROJET / "league_protocol.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def _points_simples(chart: dict) -> dict:
    """Lecture de points factice : le parsing QC est l'organe `analyze_arms._points`.

    Ces deux tests portent sur le CÂBLAGE des adaptateurs -- ils deleguent au
    critere -- pas sur la lecture des graphiques, qui passe par la plateforme.
    """
    return {nom: sorted((int(t), float(v)) for t, v in serie["values"])
            for nom, serie in (chart.get("series") or {}).items()}


def _graphique_mensuel(*series: str) -> dict:
    """Un graphique `Monthly` factice, aux series nommees."""
    return {"name": "Monthly", "chartType": 0,
            "series": {nom: {"values": [[T0 + j * PAS, 0.1 * (j + 1)] for j in range(4)]}
                       for nom in series}}


def test_le_controle_mensuel_delegue_au_critere(monkeypatch):
    lp = _charger_league_protocol()
    monkeypatch.setattr(lp, "_series_points", _points_simples)
    resultat = lp._compare_monthly(_graphique_mensuel("ret", "spy"), _graphique_mensuel("ret"))
    assert resultat["compared"] == "Monthly"
    assert resultat["divergence"] == []
    assert resultat["series_communes"] == ["ret"]
    assert resultat["series_seulement_ref"] == ["spy"]


def test_le_controle_de_trace_delegue_au_critere(monkeypatch):
    lp = _charger_league_protocol()
    rows = _trace()
    monkeypatch.setattr(lp, "_shadow_rows", lambda chart: list(rows))
    resultat = lp._compare_shadow({}, {})
    assert resultat["compared"] == "shadow"
    assert resultat["divergence"] == []
    assert resultat["points"] == 10
    assert resultat["ecart_max"] == 0.0


def test_le_controle_de_trace_reporte_une_divergence(monkeypatch):
    lp = _charger_league_protocol()
    rows = _trace()
    lecture = {"ref": list(rows), "ctl": [(d, v + 1.0) for d, v in rows]}
    monkeypatch.setattr(lp, "_shadow_rows", lambda chart: list(lecture[chart["role"]]))
    resultat = lp._compare_shadow({"role": "ref"}, {"role": "ctl"})
    assert resultat["divergence"] == ["trace journaliere"]
    assert resultat["ecart_max"] == 1.0


@pytest.mark.parametrize("ref_present,ctl_present", [(False, True), (True, False),
                                                      (True, True), (False, False)])
def test_control_choisit_la_mesure_sans_masquer_une_trace_absente(
        monkeypatch, capsys, tmp_path, ref_present, ctl_present):
    """Le controle public refuse une trace manquante et conserve les deux voies valides."""
    lp = _charger_league_protocol()
    monthly_calls = []

    def chart(project, backtest, name):
        monthly_calls.append((backtest, name))
        return {"role": backtest}

    monkeypatch.setattr(lp, "_acces_qc", lambda: (None, chart, None, None, None))
    monkeypatch.setattr(lp, "_read_stats", lambda project, backtest: {
        "statistics": {key: "identique" for key in lp.STAT_KEYS}})
    present = {"ref": ref_present, "ctl": ctl_present}
    monkeypatch.setattr(lp, "_chart_or_none", lambda project, backtest, name:
                        {"role": backtest} if present[backtest] else None)
    monkeypatch.setattr(lp, "_compare_shadow", lambda ref, ctl:
                        {"compared": "shadow", "divergence": []})
    monkeypatch.setattr(lp, "_compare_monthly", lambda ref, ctl:
                        {"compared": "Monthly", "divergence": []})
    out = tmp_path / "controle.json"
    rc = lp.cmd_control(SimpleNamespace(project=1, ref="ref", ctl="ctl", out=str(out)))
    result = json.loads(capsys.readouterr().out)
    assert json.loads(out.read_text(encoding="utf-8")) == result
    if ref_present != ctl_present:
        missing = "reference" if not ref_present else "controle"
        assert rc == 1
        assert result["verdict"] == "REFUS"
        assert result["refus"] == f"trace journaliere absente du cote {missing}"
        assert monthly_calls == []
    else:
        assert rc == 0
        assert result["verdict"] == "OK"
        assert result["compared"] == ("shadow" if ref_present else "Monthly")
        assert len(monthly_calls) == (0 if ref_present else 2)
