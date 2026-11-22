"""#21067 -- le cap de livraisons EPIC branche sur le tapis rapide (voie legere).

Le garde arbitral (charge en vol, item K=2 / famille K=4) ne vivait que dans
``pick_idle_grain.py``, retire du tirage depuis #26926 : ce module le rebranche
en important l'organe, jamais en le recopiant. Les tests verifient l'ecart, le
remplacement par les suivants de l'ordre, les exemptions, le fail-OPEN et la
re-verification du remplacant -- chacun sur fixtures pures, sans reseau.
"""
import datetime as dt
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from coordination.tapis_cap_livraisons import charge_en_vol, passer  # noqa: E402
from coordination.tapis_rapide import Etat  # noqa: E402

LANE = "myia-po-2023:CoursIA"
AUTRE = "myia-po-2024:CoursIA"
NOW = dt.datetime(2026, 11, 22, 12, 0, tzinfo=dt.timezone.utc)


def _pr(number: int, lane: str, merged_days_ago: float, cites: str) -> dict:
    merged = NOW - dt.timedelta(days=merged_days_ago)
    body = f"Grain: MED/tooling — lane {lane} — prev: MED/tooling #1\n\n{cites}\n"
    return {"number": number, "body": body,
            "mergedAt": merged.strftime("%Y-%m-%dT%H:%M:%SZ")}


def _run(corpus: list[dict]):
    """Le fetcher injecte : rend le corpus pour toute tranche demandee."""
    return lambda since, until: corpus


def _etat(numero: int, parent: int | None = None, labels: list[str] | None = None):
    return Etat(numero, f"issue {numero}", list(labels or []),
                "2026-01-01T00:00:00Z", parent, parent or numero, False, False)


# --- charge_en_vol -------------------------------------------------------


def test_charge_merge_ouvertes_et_fenetre():
    corpus = [_pr(1, LANE, 1, "Closes #100")]
    ouvertes = [{"number": 9, "body":
                 f"Grain: MED/tooling — lane {LANE} — prev: x #1\n\nPart of #100\n"}]
    charge = charge_en_vol(LANE, NOW, ouvertes, run=_run(corpus))
    assert charge == {100: 2}  # 1 mergee + 1 ouverte, meme fenetre de 7 j


def test_charge_fail_open_sur_panne():
    def panique(since, until):
        raise RuntimeError("quota")
    assert charge_en_vol(LANE, NOW, None, run=panique) is None


def test_charge_autre_lane_pas_comptee():
    corpus = [_pr(1, AUTRE, 1, "Closes #100")]
    assert charge_en_vol(LANE, NOW, None, run=_run(corpus)) == {}


# --- passer --------------------------------------------------------------


def test_item_au_cap_est_ecarte_et_remplace():
    corpus = [_pr(1, LANE, 1, "Closes #100"), _pr(2, LANE, 2, "See #100")]
    file = [_etat(100), _etat(101)]
    ordre = [_etat(100), _etat(101), _etat(102)]
    garde, temoins, mesure = passer(file, ordre, LANE, NOW, None, run=_run(corpus))
    assert mesure is True
    assert [t["numero"] for t in temoins] == [100]
    assert "PLAFOND LIVRAISONS EPIC" in temoins[0]["motif"]
    assert [e.numero for e in garde] == [101, 102]  # complete par le suivant
    assert file[0].ecart == "PLAFOND_LIVRAISONS"  # l'Etat porte la marque


def test_famille_au_cap_ecarte_lenfant():
    corpus = [_pr(i, LANE, i * 0.5, f"See #200") for i in range(1, 5)]  # 4 sur le parent
    enfant = _etat(201, parent=200)
    file = [enfant]
    ordre = [enfant, _etat(202)]
    garde, temoins, mesure = passer(file, ordre, LANE, NOW, None, run=_run(corpus))
    assert mesure is True
    assert [t["numero"] for t in temoins] == [201]
    assert "PLAFOND FAMILLE EPIC" in temoins[0]["motif"]


def test_consolidation_exemptee():
    corpus = [_pr(1, LANE, 1, "Closes #300"), _pr(2, LANE, 2, "See #300")]
    e = _etat(300, labels=["consolidation"])
    garde, temoins, mesure = passer([e], [e], LANE, NOW, None, run=_run(corpus))
    assert mesure is True and not temoins
    assert [x.numero for x in garde] == [300]


def test_fail_open_file_intacte():
    def panique(since, until):
        raise RuntimeError("reseau")
    file = [_etat(100), _etat(101)]
    garde, temoins, mesure = passer(file, list(file), LANE, NOW, None, run=panique)
    assert mesure is False and not temoins
    assert garde == file  # l'identite : rien n'a bouge


def test_remplacant_de_la_meme_famille_plafonnee_passe_pas():
    corpus = [_pr(i, LANE, i * 0.5, f"See #200") for i in range(1, 5)]  # famille K=4
    file = [_etat(201, parent=200)]
    ordre = [_etat(201, parent=200), _etat(202, parent=200), _etat(203)]
    garde, temoins, mesure = passer(file, ordre, LANE, NOW, None, run=_run(corpus))
    # 202 est de la MEME famille plafonnee : il ne remplace pas 201 ; 203 oui.
    assert [e.numero for e in garde] == [203]
    assert [t["numero"] for t in temoins] == [201]


def test_sous_le_cap_rien_n_est_ecarte():
    corpus = [_pr(1, LANE, 1, "Closes #100")]  # charge 1 < K=2
    file = [_etat(100)]
    garde, temoins, mesure = passer(file, list(file), LANE, NOW, None, run=_run(corpus))
    assert mesure is True and not temoins
    assert [e.numero for e in garde] == [100]
