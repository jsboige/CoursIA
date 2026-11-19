"""Le CONTROLE ISOLE d'une citation : ce qu'il mesure, et ce qu'il ne decide pas.

Mandat du coordinateur (20/11/2026, DM `coord1911-27338-isolate`) :
« si le diff de #27393 ne livre pas #27338, ajouter ou retirer cette citation
seule doit laisser exactement inchangee la date de service de #27338. Rends le
couple de dates avant/apres sur ce controle isole. »

Ces tests verrouillent deux choses :

- le controle **isole** bien UNE citation : le couple de dates avant/apres se
  lit, et rien d'autre ne bouge ;
- la **livraison confirmee par le diff** ne bouge PAS avec une citation : le
  store ne porte que le diff.

Ils ne tranchent pas la regle du candidat : le coordinateur garde la decision
de revue.
"""
from coordination import tapis_cle, tapis_controle, tapis_releve
from coordination.tapis_rapide import Etat

LANE = "myia-ai-01:CoursIA-2"


def _etat(numero: int) -> Etat:
    return Etat(numero, "grain %d" % numero, [], "2026-01-01T00:00:00Z",
                None, numero, False, False)


def _candidat(numero: int, pr: int, date: str) -> dict:
    return {numero: [{"sha": "pr%d" % pr, "date": date,
                       "canonique": True, "pr": pr}]}


def test_le_controle_isole_une_seule_citation():
    """Avec la citation, la cle est datee par elle ; sans elle, elle n'existe pas."""
    avec, sans = _etat(400), _etat(400)
    tapis_cle.appliquer([avec], _candidat(400, 27393, "2026-11-19T16:11:50Z"))
    tapis_cle.appliquer([sans], {})
    r = tapis_controle.controler(400, 27393, [avec], [sans], LANE)
    assert r["avant"]["cle_service"] == "2026-11-19T16:11:50Z"
    assert r["apres"]["cle_service"] is None
    assert r["avant"]["cle_origine"].startswith("PR #")
    assert r["numero"] == 400 and r["pr"] == 27393


def test_la_livraison_confirmee_ne_bouge_pas_avec_une_citation(monkeypatch, tmp_path):
    """Le store ne porte que le diff : une citation ne le touche pas."""
    monkeypatch.setenv(tapis_releve.ENV_RELEVE, str(tmp_path / "store"))
    tapis_releve.enregistrer_service(401, "2026-11-05T10:00:00Z",
                                     "PR #9 (diff couvre)", 9)
    avec, sans = _etat(401), _etat(401)
    tapis_cle.appliquer([avec], _candidat(401, 27393, "2026-11-19T16:11:50Z"))
    tapis_cle.appliquer([sans], {})
    r = tapis_controle.controler(401, 27393, [avec], [sans], LANE)
    assert r["avant"]["cle_service"] == r["apres"]["cle_service"]
    assert r["livraison_confirmee"]["pr"] == 9
    assert r["store"][0] == "2026-11-05T10:00:00Z"
