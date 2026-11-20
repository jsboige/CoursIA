"""Tests de ``coordination.tapis_acceptance`` -- acceptance 2 de #25082 sur le service effectif.

Run: python -m pytest scripts/tests/test_tapis_acceptance.py
"""
from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from coordination import gh_bulk, tapis_acceptance, tirage_journal


def _record(numero: int, *, consolidation: bool = False, famille: int | None = None,
            resolue: bool = True,
            mode: str = tapis_acceptance.MODE, lane: str = "myia-ai-01:CoursIA-2"):
    return tirage_journal.TirageRecord.new(
        lane=lane,
        candidates=[numero],
        retained=numero,
        urn=tapis_acceptance.URN,
        mode=mode,
        extras={"famille": (famille if famille is not None else numero) if resolue else None,
                "consolidation": consolidation},
    )


def test_sans_echantillon_rend_aucune_mesure_pas_zero():
    m = tapis_acceptance.mesurer([])
    assert m["tirages"] == 0
    assert m["part_consolidation"] is None
    assert m["part_famille"] is None
    assert m["criteres"]["prioritaire"]["statut"] == "AUCUNE MESURE"
    assert m["criteres"]["famille"]["statut"] == "AUCUNE MESURE"


def test_les_enregistrements_diagnostic_ne_compent_pas():
    """Le rejeu (`mode=belt`) mesure une autre chose : il ne compte pas."""
    recs = [_record(1, consolidation=True, mode="belt") for _ in range(50)]
    m = tapis_acceptance.mesurer(recs)
    assert m["tirages"] == 0
    assert m["criteres"]["famille"]["statut"] == "AUCUNE MESURE"


def test_echantillon_plein_tenu_et_non_tenu():
    servis = [_record(100 + i, consolidation=(i < 10)) for i in range(50)]
    m = tapis_acceptance._statut_partiel(tapis_acceptance.mesurer(servis))
    assert m["tirages"] == 50
    assert m["part_consolidation"] == 0.2
    assert m["criteres"]["prioritaire"]["statut"] == "TENU"
    assert m["criteres"]["famille"]["statut"] == "TENU"

    servis = [_record(100 + i, consolidation=(i < 2)) for i in range(50)]
    m = tapis_acceptance._statut_partiel(tapis_acceptance.mesurer(servis))
    assert m["part_consolidation"] == 0.04
    assert m["criteres"]["prioritaire"]["statut"] == "NON TENU"


def test_echantillon_court_ne_conclut_pas():
    servis = [_record(100 + i, consolidation=(i < 2)) for i in range(8)]
    m = tapis_acceptance._statut_partiel(tapis_acceptance.mesurer(servis))
    assert m["tirages"] == 8
    assert m["criteres"]["prioritaire"]["statut"] == "MESURE PARTIELLE"
    assert m["criteres"]["prioritaire"]["echantillon"] == 8
    assert m["criteres"]["prioritaire"]["echantillon_plein"] == 50


def test_famille_non_resolue_compte_comme_non_resolue():
    servis = [_record(100 + i, resolue=(i != 0)) for i in range(50)]
    m = tapis_acceptance.mesurer(servis)
    assert m["part_famille"] == 49 / 50
    assert m["criteres"]["famille"]["statut"] == "TENU"  # 98 % au-dessus du seuil de 80 %

    servis = [_record(100 + i, resolue=(i >= 30)) for i in range(50)]
    m = tapis_acceptance.mesurer(servis)
    assert m["part_famille"] == 20 / 50
    assert m["criteres"]["famille"]["statut"] == "NON TENU"


def test_journaliser_ecrit_un_enregistrement_par_grain(tmp_path):
    grains = [
        {"numero": 11, "famille": 5, "consolidation": True, "rang": 1},
        {"numero": 12, "famille": 12, "consolidation": False, "rang": 2},
    ]
    chemin = tmp_path / "journal.jsonl"
    ecrits = tapis_acceptance.journaliser(
        grains, "myia-ai-01:CoursIA-2", path=chemin, ts="2026-11-20T21:00:00Z")
    assert ecrits == 2
    recs = tirage_journal.read_journal(chemin)
    assert len(recs) == 2
    assert {r.retained for r in recs} == {11, 12}
    assert len({r.draw_id for r in recs}) == 1  # un tirage = un draw_id
    assert all(r.mode == tapis_acceptance.MODE for r in recs)
    premier = next(r for r in recs if r.retained == 11)
    assert premier.extras["famille"] == 5
    assert premier.extras["consolidation"] is True


def test_le_magasin_du_service_est_dedie():
    """Le service a son propre magasin : le journal diagnostic est melange (945 `belt`)."""
    chemin = tapis_acceptance.default_store()
    assert chemin.name == "journal.jsonl"
    assert "tapis_service" in chemin.parts
    assert "tirage_journal" not in chemin.parts


def test_un_rejeu_n_est_pas_journalise(tmp_path):
    """Un rejeu hors ligne n'est pas un tirage servi : il ne pollue pas la mesure."""
    rapport = {"grains": [{"numero": 11, "famille": 5, "consolidation": True}]}
    out = tapis_acceptance.journaliser_service(
        rapport, "lane", True, path=tmp_path / "journal.jsonl")
    assert out["enregistres"] == 0
    assert "rejeu" in out["motif"]
    assert not (tmp_path / "journal.jsonl").exists()


def test_une_lecture_injectee_n_est_pas_journalisee(tmp_path):
    """La suite de tests appelle `main()` avec une lecture factice : elle n'ecrit pas.

    Sans ce refus, la suite pollue le magasin machine et la mesure compte des
    grains qui n'ont jamais ete servis (mesure : 24 faux enregistrements).
    """
    rapport = {"grains": [{"numero": 11, "famille": 5, "consolidation": True}]}
    out = tapis_acceptance.journaliser_service(
        rapport, "lane", False, run=lambda argv, timeout: "",
        path=tmp_path / "journal.jsonl")
    assert out["enregistres"] == 0
    assert "injectee" in out["motif"]
    assert not (tmp_path / "journal.jsonl").exists()


def test_une_lecture_reelle_est_journalisee(tmp_path):
    rapport = {"grains": [{"numero": 11, "famille": 5, "consolidation": True}]}
    out = tapis_acceptance.journaliser_service(
        rapport, "lane", False, run=gh_bulk.run_defaut, path=tmp_path / "journal.jsonl")
    assert out["enregistres"] == 1
    recs = tirage_journal.read_journal(tmp_path / "journal.jsonl")
    assert [r.retained for r in recs] == [11]


def test_une_panne_de_telemetry_ne_casse_pas_le_service(tmp_path, capsys, monkeypatch):
    """Le service est fail-OPEN : une panne de journal se dit, le tirage passe."""
    def _panne(*a, **k):
        raise OSError("disque plein")

    monkeypatch.setattr(tapis_acceptance, "journaliser", _panne)
    rapport = {"grains": [{"numero": 11, "famille": 5, "consolidation": True}]}
    out = tapis_acceptance.journaliser_service(
        rapport, "lane", False, run=gh_bulk.run_defaut,
        path=tmp_path / "journal.jsonl")
    assert out["enregistres"] == 0
    assert out["erreur"]
    assert "[WARN]" in capsys.readouterr().err


def test_la_note_delivered_est_portee():
    """La classe delivered n'est pas servie par le service effectif : la note le dit."""
    m = tapis_acceptance.mesurer([_record(1, consolidation=True)])
    assert "delivered" in m["note_delivered"]
    assert "consolidation" in m["note_delivered"]
