"""Invariant de couverture du tapis rapide (#27590, dispatch `c0013-tapis-coverage-20`).

Le mandat du 2026-11-16 : « toute issue doit etre visitée au moins une fois avant
qu'une autre le soit deux fois ». Mesure du 21/11 : 20 issues worker a 0 visite
etaient hors du tour de 8, et deux issues **deja visitees** prenaient leurs
places -- le quota de conteneurs ecartait les conteneurs jamais visites, et le
tri final (les grains d'abord, #26926) plaçait le reste hors tour.

L'invariant verifie ici :

    **une issue jamais visitée du pool servable ne cede jamais sa place a une
    issue deja visitée** ; et le conteneur jamais visite que le quota ecarte
    passe en second temps plutot que de laisser la place a un grain deja
    visite.

Chaque regle a son controle positif et son controle negatif (une issue deja
visitee qui revient quand il ne reste plus de jamais visitee ; une issue
reclamee par une autre lane ; un marathon, qui est hors equilibrage). Aucun
test ne touche le reseau : les lectures sont construites en memoire.

Emplacement : `scripts/tests/` -- la convention du depot (il n'existe pas de
`scripts/coordination/tests/`).
"""
import importlib.util
from pathlib import Path

import pytest
from coordination import tapis_rapide as tr

# Les fabriques de test_tapis_rapide.py, chargees par chemin : sous
# `--import-mode importlib`, `tests.` designe le premier paquet `tests` collecte
# (scripts/genai-stack/tests, par exemple), pas ce repertoire.
_SPEC = importlib.util.spec_from_file_location(
    "_fabriques_tapis_rapide", Path(__file__).with_name("test_tapis_rapide.py"))
_fab = importlib.util.module_from_spec(_SPEC)
_SPEC.loader.exec_module(_fab)
AUTRE, LANE, NOW = _fab.AUTRE, _fab.LANE, _fab.NOW
com, issue, lecture = _fab.com, _fab.issue, _fab.lecture

pytestmark = pytest.mark.usefixtures("forbid_shell_escape")

MARATHON = "myia-po-2027:CoursIA"


def visite(heures: float = 100.0, lane: str = AUTRE) -> dict:
    """Une visite hors fenetre de reclamation (48 h) : l'issue est servable
    mais deja visitée dans le tour de 7 jours."""
    return com(heures, f"[CLAIMED] lane {lane} -- paths: x")


def _etat(numero: int = 1, visites: int = 0, titre: str = "Grain",
          ecart: str | None = None) -> tr.Etat:
    """Un Etat construit a la main (comme dans `test_visit_coverage.py`)."""
    return tr.Etat(numero=numero, titre=titre, labels=[], cree_le="2026-10-01T00:00:00Z",
                   parent=None, famille=numero, conteneur=False, consolidation=False,
                   visites=visites, visites_total=visites, ecart=ecart, motif="")


def _servis(issues, grains: int = 8, lane: str = LANE) -> list[int]:
    lec = lecture(issues)
    etats = tr.etats(lec, lane, NOW)
    return [e.numero for e in tr.ordonner(etats, lane, NOW, grains)]


# --- controle positif : la jamais visitee ne cede pas la place ---------------

def test_le_tour_ne_sert_pas_une_issue_deja_visitee_pendant_qu_une_jamais_visitee_reste_hors_tour():
    """Le coeur de l'invariant : un grain deja visite ne prend pas la place
    d'un conteneur jamais visite."""
    issues = [issue(10, titre="[EPIC] conteneur A"),
              issue(11, titre="[EPIC] conteneur B"),
              issue(12, comments=[visite()])]
    servis = _servis(issues, grains=2)
    assert 11 in servis and 10 in servis
    assert 12 not in servis


def test_le_quota_de_conteneurs_n_ecarte_plus_une_issue_jamais_visitee():
    """Le quota (25 % du tour) regne sur les conteneurs, mais un conteneur
    jamais visite passe en second temps : il ne se fait pas voler sa place."""
    issues = [issue(20, titre="[EPIC] conteneur A"),
              issue(21, titre="[EPIC] conteneur B"),
              issue(22, titre="[EPIC] conteneur C"),
              issue(23, titre="[EPIC] conteneur D"),
              issue(24, comments=[visite()])]
    servis = _servis(issues, grains=2)
    assert 24 not in servis  # le grain deja visite ne prend pas la place
    assert len(servis) == 2
    assert set(servis) <= {20, 21, 22, 23}  # des conteneurs jamais visites
    # et les quatre finissent par tourner, sans jamais ceder la place au grain
    lec = lecture(issues)
    etats = tr.etats(lec, LANE, NOW)
    servis_ = set()
    for _ in range(2):
        for e in tr.ordonner(etats, LANE, NOW, 2):
            assert e.visites == 0 or e.numero in servis_
            e.visites += 1
            servis_.add(e.numero)
    assert {20, 21, 22, 23} <= servis_


def test_le_tour_graine_ne_penalise_pas_le_containing_de_la_tour():
    """Les grains viennent en tete (#26926) : un conteneur jamais visite ne
    passe pas devant un grain du pool."""
    issues = [issue(30, titre="[EPIC] conteneur ancien", cree="2026-01-01T00:00:00Z"),
              issue(31, titre="Grain du pool", cree="2026-01-01T00:00:00Z")]
    assert _servis(issues, grains=2) == [31, 30]


# --- controles negatifs ----------------------------------------------------

def test_une_issue_deja_visitee_revient_quand_il_ne_reste_plus_de_jamais_visitee():
    """Controle negatif du controle positif : sans jamais visitee concurrente,
    l'issue deja visitee est bien servie."""
    issues = [issue(40, comments=[visite()]), issue(41, comments=[visite(80)])]
    assert set(_servis(issues, grains=2)) == {40, 41}


def test_une_issue_reclamee_par_une_autre_lane_est_hors_de_mon_tour():
    """Une reclamation vivante d'une autre lane n'est pas servable : elle
    n'entre pas dans le tour de personne."""
    issues = [issue(50, comments=[com(2, f"[CLAIMED] lane {MARATHON} -- paths: x")]),
              issue(51)]
    etats = tr.etats(lecture(issues), LANE, NOW)
    assert next(e for e in etats if e.numero == 50).ecart == "RECLAMEE"
    assert _servis(issues, grains=2) == [51]


def test_un_marathon_ne_dispute_pas_la_place_d_un_grain_deja_visite():
    """Un marathon est hors equilibrage (harnais sk-agent) : jamais visite, il
    ne passe pas devant le grain equilibre du tour."""
    issues = [issue(60, titre="[Marathon II] Jumeau C# RL07b"),
              issue(61, titre="Grain equilibre", comments=[visite()])]
    assert _servis(issues, grains=2) == [61, 60]


def test_une_issue_ecartee_par_un_code_ne_entre_pas_dans_le_tour():
    """Une issue livree par une autre lane est hors du pool du worker."""
    issues = [issue(70, comments=[com(10, "[INFO] candidate-delivered -- lane "
                                         f"{MARATHON}")]),
              issue(71)]
    etats = tr.etats(lecture(issues), LANE, NOW)
    assert next(e for e in etats if e.numero == 70).ecart == "LIVREE"
    assert _servis(issues, grains=2) == [71]


# --- rotation : l'invariant tient dans le temps ----------------------------

def test_toute_issue_jamais_visitee_est_servie_en_un_nombre_de_tours_borne():
    """Le tour a une taille fixe : l'invariant ne vaut pas « tout dans le
    tour », il vaut « tout finit par etre servi, et aucune issue deja
    visitee ne prend la place d'une jamais visitée ».

    Mesure : 21 issues jamais visitees, tour de 8 -> trois tours suffisent.
    """
    issues = [issue(100 + k, titre=f"[EPIC] conteneur {k}") for k in range(7)]
    issues += [issue(200 + k, titre=f"Grain {k}") for k in range(14)]
    lec = lecture(issues)
    etats = tr.etats(lec, LANE, NOW)
    pool = {e.numero for e in etats if e.ecart is None}
    servis: set[int] = set()
    for _ in range(3):
        tour = tr.ordonner(etats, LANE, NOW, 8)
        dans = {e.numero for e in tour}
        jamais_hors = {e.numero for e in etats
                       if e.ecart is None and e.visites == 0 and e.numero not in dans}
        assert not (jamais_hors and {e.numero for e in tour if e.visites > 0}), (
            "une issue deja visitee a pris la place d'une jamais visitee")
        for e in tour:
            e.visites += 1
            servis.add(e.numero)
    assert servis == pool


# --- l'organe : la mesure d'atteignabilite ----------------------------------

def test_l_organe_dit_le_nombre_de_tours_et_l_equite():
    """`visit_coverage.atteignable` mesure ce que le testInvariant verifie :
    combien de tours pour servir les jamais visitees, et si une issue deja
    visitee est servie pendant qu'une autre attend."""
    from coordination import visit_coverage as vc
    issues = [issue(300 + k, titre=f"Grain {k}") for k in range(12)]
    etats = tr.etats(lecture(issues), LANE, NOW)
    r = vc.atteignable(etats, LANE, NOW, grains=8)
    assert r["jamais_visitees"] == 12
    assert r["servies"] == 12 and r["restantes"] == []
    assert r["equite"] == []          # aucune issue deja visitee servie en avance
    assert r["tours"] == 2            # 12 issues, tour de 8


def test_l_organe_signale_l_equite_viollee(monkeypatch):
    """Controle negatif : si le tirage sert une issue deja visitee pendant
    qu'une jamais visitée attend, l'organe le dit -- il ne le masque pas.

    Le tirage casse est simule (un ordre qui met les issues les plus
    visitees devant) : l'organe doit le voir, meme si le code livre est
    correct.
    """
    from coordination import visit_coverage as vc

    def casse(etats_, lane, maintenant, grains, graine=None):
        return sorted(etats_, key=lambda e: (-e.visites, e.numero))[:grains]

    monkeypatch.setattr(vc.tapis_rapide, "ordonner", casse)
    etats = [_etat(numero=1, visites=3), _etat(numero=2, visites=0)]
    r = vc.atteignable(etats, LANE, NOW, grains=2)
    assert r["equite"] == [1]


def test_le_filtre_de_servabilite_suit_la_definition_du_module(monkeypatch):
    """Compatibilite avec le #27059 (lane myia-ai-01:CoursIA, PR ouverte) : ce
    tirage elargit la notion de servable aux ecarts de recul (COUVERTE,
    RELACHEE, MERGEE). Sans le shim, le filtre de `ordonner` ecarterait du
    tour des issues que ce tirage entend servir.
    """
    e = _etat(numero=1, ecart="COUVERTE")
    assert tr._servable(e) is False   # avant le #27059 : un ecart dur n'est pas servi
    monkeypatch.setattr(tr, "servable",
                        lambda x: x.ecart is None or x.ecart in ("COUVERTE", "RELACHEE", "MERGEE"),
                        raising=False)
    assert tr._servable(e) is True
