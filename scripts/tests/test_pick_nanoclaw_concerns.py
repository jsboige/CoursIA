"""Controles positifs des deux concerns de la review NanoClaw sur #13466.

Chaque test est ecrit pour ECHOUER sur le code d avant le fix -- c est la
seule facon de savoir qu il mesure quelque chose. Un test qui passe aussi
sans le correctif ne protege de rien.
"""
import sys
import datetime as dt
import pathlib

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))

from pick_idle_grain import URGENT_LABELS, admissibility  # noqa: E402
from series_saturation import (  # noqa: E402
    CONSOLIDATION,
    EXPANSION,
    NEUTRAL,
    zone_balance,
)

FAM = "Search/Part4-Metaheuristics"


def _fresh(labels=None, polarity=EXPANSION, number=1):
    """Une issue creee a l instant : refusee par DWELL sauf etiquette d urgence."""
    return {
        "number": number,
        "title": "t",
        "labels": labels or [],
        "created_at": dt.datetime.now(dt.timezone.utc).isoformat(),
        "polarity": polarity,
    }


# --- concern 2 : le bypass d urgence doit aussi parler francais -----------

def test_les_variantes_fr_durgence_court_circuitent_le_dwell():
    """Sur un depot dont les issues sont en francais, `urgence` s ecrira.

    Avant le fix, URGENT_LABELS etait un ensemble exact anglais : une issue
    vraiment urgente etiquetee `urgence` restait retenue 24 h par un garde
    cense l exempter -- et en SILENCE.
    """
    for lab in ("urgence", "securite", "sécurité", "critique", "bloquant"):
        assert admissibility(_fresh(labels=[lab]), None, None) is None, (
            "l etiquette FR {!r} ne court-circuite pas le dwell".format(lab))


def test_les_etiquettes_anglaises_restent_couvertes():
    """Le fix AJOUTE, il ne remplace pas -- controle de non-regression."""
    for lab in ("urgent", "security", "hotfix", "p0"):
        assert admissibility(_fresh(labels=[lab]), None, None) is None, lab


def test_une_issue_fraiche_sans_etiquette_reste_refusee():
    """Le controle negatif : sans le veto, les deux tests ci-dessus sont vides."""
    cause = admissibility(_fresh(), None, None)
    assert cause and cause.startswith("DWELL"), cause


def test_le_set_ne_contient_que_des_minuscules():
    """Le match se fait sur `labels_lc` : une majuscule ici serait morte."""
    assert all(x == x.lower() for x in URGENT_LABELS)


# --- concern 1 : le refus SANS REMEDE doit etre refutable sur pieces ------

def _pool(*items):
    return [dict(number=n, title=t, body="") for n, t in items]


def _zones():
    return {FAM: {"new_notebooks": 5}}


def test_le_refus_nomme_les_grains_neutral_ou_le_faux_positif_se_cacherait():
    """Concern 1 : le veto lit le LEXIQUE, pas les intentions.

    Un grain de consolidation dont le titre echappe au lexique tombe en
    NEUTRAL. Le refus doit le NOMMER, sinon le faux positif est silencieux.
    """
    pool = _pool((10, "ajouter un notebook MGS-30"),
                 (11, "MGS : reprendre la paire 12 autrement"))
    i2f = {10: FAM, 11: FAM}
    bal = zone_balance(_zones(), i2f, pool)
    assert bal[FAM][CONSOLIDATION] == 0, "le cas teste exige con == 0"
    assert bal[FAM][NEUTRAL] >= 1, "le cas teste exige un grain NEUTRAL"

    item = {"number": 10, "title": "ajouter un notebook MGS-30", "labels": [],
            "created_at": "2020-01-01T00:00:00Z", "polarity": EXPANSION}
    cause = admissibility(item, bal, i2f)
    assert cause and cause.startswith("ZONE SANS REMEDE"), cause
    assert "#11" in cause, "le refus ne cite pas le grain NEUTRAL : {}".format(cause)
    assert "faux positif" in cause, cause


def test_sans_grain_neutral_le_refus_reste_sobre():
    """Controle negatif : pas de NEUTRAL, pas de rallonge inventee."""
    pool = _pool((10, "ajouter un notebook MGS-30"),
                 (11, "creer un notebook MGS-31"))
    i2f = {10: FAM, 11: FAM}
    bal = zone_balance(_zones(), i2f, pool)
    assert bal[FAM][NEUTRAL] == 0, "le cas teste exige zero NEUTRAL"
    item = {"number": 10, "title": "ajouter un notebook MGS-30", "labels": [],
            "created_at": "2020-01-01T00:00:00Z", "polarity": EXPANSION}
    cause = admissibility(item, bal, i2f)
    assert cause.startswith("ZONE SANS REMEDE"), cause
    assert "faux positif" not in cause, cause


def test_un_vrai_remede_leve_le_veto_et_ne_declenche_aucune_rallonge():
    """Non-regression : con >= 1 admet, quel que soit le nombre de NEUTRAL."""
    pool = _pool((10, "ajouter un notebook MGS-30"),
                 (11, "MGS : reprendre la paire 12 autrement"),
                 (12, "consolider les notebooks MGS 20-28"))
    i2f = {10: FAM, 11: FAM, 12: FAM}
    bal = zone_balance(_zones(), i2f, pool)
    assert bal[FAM][CONSOLIDATION] == 1
    item = {"number": 10, "title": "ajouter un notebook MGS-30", "labels": [],
            "created_at": "2020-01-01T00:00:00Z", "polarity": EXPANSION}
    assert admissibility(item, bal, i2f) is None


def test_neutral_issues_ne_retient_que_la_zone_concernee():
    """Un NEUTRAL d une AUTRE zone ne doit pas polluer le refus."""
    autre = "GenAI/Image"
    pool = _pool((10, "ajouter un notebook MGS-30"),
                 (11, "MGS : reprendre la paire 12 autrement"),
                 (99, "reprendre autrement le pipeline image"))
    i2f = {10: FAM, 11: FAM, 99: autre}
    bal = zone_balance({FAM: {"new_notebooks": 5}, autre: {"new_notebooks": 5}},
                       i2f, pool)
    assert bal[FAM]["neutral_issues"] == [11], bal[FAM]["neutral_issues"]
    assert bal[autre]["neutral_issues"] == [99], bal[autre]["neutral_issues"]
