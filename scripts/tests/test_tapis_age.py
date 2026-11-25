"""L'ORDRE D'AGE du tapis : les issues anciennes d'abord (mandat du 22/11).

Verbatim du mandat : « le tapis devrait pouvoir piocher les issues
anciennes prioritairement sur les plus recentes, meme si celles qui n'ont
jamais ete visitees peuvent etre traitees parmi la tete du tapis. Si ca ne
fonctionne pas, alors on mettra les nouvelles issues en fin de tapis. »

Ce que ces tests prouvent, sur un pool SYNTHETIQUE :

- la **cle** de l'ordre d'age : la bande des fraiches passe devant tout (fin
  de file), la jamais visitée passe devant, puis la plus ancienne ;
- la **consolidation** (revue ai-01 du 22/11) : elle passe devant la
  non-consolidation de meme bande, et elle echappe a la bande des fraiches ;
- la **selection** sert les issues anciennes, et non les numeros situes
  au-dessus de l'ancre (l'inversion mesuree le 22/11 : 0 issue anterieure
  au 01/11 dans les 60 premiers grains d'un pool de 455) ;
- l'**exclusion** : un numero servi et non decide n'est pas re-servi ;
- le **tour** : quand plus rien n'est servable, la file est rendue et le
  tour recommence ;
- les **conteneurs** gardent la rotation par numero.

Aucun test ne touche le reseau : les modules sont purs.
"""
from __future__ import annotations

import json
import sys
from datetime import UTC, datetime, timedelta
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from coordination import (tapis_age, tapis_ancre, tapis_etat,  # noqa: E402
                          tapis_leger, tapis_rotation)

pytestmark = pytest.mark.usefixtures("forbid_shell_escape")

MAINTENANT = datetime(2026, 11, 22, 9, 0, tzinfo=UTC)
LANE = "myia-ai-01:CoursIA-2"


class _Grain:
    """Un grain minimal : l'ordre d'age lit le numero, la creation, les visites."""

    def __init__(self, numero: int, age_j: float = 30.0, visites: int = 0,
                 conteneur: bool = False, consolidation: bool = False,
                 famille: int = 0, cle_service: str = ""):
        self.numero = numero
        self.titre = f"issue {numero}"
        self.cree_le = (MAINTENANT - timedelta(days=age_j)).isoformat()
        self.visites = visites
        self.visites_total = visites
        self.conteneur = conteneur
        self.consolidation = consolidation
        self.famille = famille
        #: La CLE DE SERVICE (19/11) : la date de la derniere PR qui couvre le
        #: grain. Vide = aucune PR ne le couvre, l'anciennete tombe alors sur
        #: la creation.
        self.cle_service = cle_service
        self.notes: list[str] = []


def _ages(grains: list[_Grain]) -> list[_Grain]:
    return tapis_age.trier(grains, MAINTENANT)


# --- la cle ------------------------------------------------------------------

def test_la_bande_des_fraises_passe_devant_tout():
    """Une issue de moins de 72 h va en FIN de file, meme si elle est
    jamais visitée : le mandat dit « on mettra les nouvelles issues en fin
    de tapis »."""
    ancienne = _Grain(1, age_j=30.0, visites=0)
    fraiche = _Grain(2, age_j=1.0, visites=0)
    assert _ages([fraiche, ancienne])[0] is ancienne, \
        "la plus ancienne passe avant la fraiche"
    assert _ages([fraiche, ancienne])[-1] is fraiche, \
        "la fraiche va en fin de file"


def test_la_jamais_visitee_passe_devant():
    """Le mandat du 16/11 : 0 visite avant 1 visite."""
    visitee = _Grain(1, age_j=30.0, visites=3)
    jamais = _Grain(2, age_j=29.0, visites=0)
    assert _ages([visitee, jamais])[0] is jamais


def test_la_plus_ancienne_passe_devant():
    """A egalite de visite, la plus ancienne d'abord."""
    recente = _Grain(1, age_j=10.0, visites=1)
    ancienne = _Grain(2, age_j=40.0, visites=1)
    assert _ages([recente, ancienne])[0] is ancienne


def test_la_cle_ne_depend_que_de_l_age_de_creation():
    """La cle est la CREATION, pas la derniere visite : une cle qui bouge
    a chaque tour ne ferme jamais le tour (echec mesure le 19/11)."""
    g = _Grain(1, age_j=30.0, visites=2)
    assert tapis_age.cle(g, MAINTENANT)[:4] == (0, 1, 1, g.cree_le)
    assert tapis_age.age_h(g, MAINTENANT) == pytest.approx(30 * 24, rel=1e-3)


# --- la consolidation (revue ai-01 du 22/11) ---------------------------------

def test_la_consolidation_passe_devant_la_non_consolidation():
    """Le mandat du cycle : « priorite consolidation ET anciennete ». A
    bande egale, la consolidation passe devant."""
    conso = _Grain(1, age_j=10.0, consolidation=True)
    autre = _Grain(2, age_j=20.0)
    assert _ages([autre, conso])[0] is conso, \
        "la consolidation passe devant, meme plus recente"


def test_une_consolidation_fraiche_echappe_a_la_bande():
    """Une consolidation ouverte AUJOURD'HUI doit pouvoir passer en tete :
    elle echappe a la bande des moins de 72 h."""
    conso_fraiche = _Grain(1, age_j=0.5, consolidation=True)
    ancienne = _Grain(2, age_j=40.0)
    assert _ages([ancienne, conso_fraiche])[0] is conso_fraiche, \
        "la consolidation fraiche n'attend pas la fin de la bande"


def test_la_famille_dune_racine_consolidation_est_heritee():
    """Une issue dont la FAMILLE porte le label `consolidation` en est une
    aussi (la regle de `tapis_avantages.est_consolidation`)."""
    membre = _Grain(7, age_j=5.0, famille=900)
    assert tapis_age.est_consolidation(membre, {900}) is True
    assert tapis_age.est_consolidation(membre, {901}) is False, \
        "une autre racine ne donne pas la consolidation"


def test_la_selection_sert_la_consolidation_en_tete():
    """De bout en bout : le bloc servi commence par la consolidation, et
    la fraiche non-consolidation part en queue."""
    grains = [_Grain(1, age_j=0.5), _Grain(2, age_j=1.0),
              _Grain(3, age_j=40.0), _Grain(4, age_j=30.0, consolidation=True)]
    ages = tapis_age.trier(grains, MAINTENANT)
    bloc, _ = tapis_rotation.bloc(grains, [], 2, 2, LANE, MAINTENANT,
                                   ancres={"grains": {"ancre": 0}},
                                   ages_g=ages, exclus_g=set())
    assert [g.numero for g in bloc] == [4, 3], \
        "la consolidation d'abord, puis la plus ancienne"


# --- la selection ------------------------------------------------------------

def test_la_selection_sert_les_issues_anciennes():
    """Le contre-exemple de l'inversion mesuree le 22/11 : le bloc ne doit
    pas etre la tranche des numeros situes au-dessus de l'ancre."""
    grains = [_Grain(100, age_j=1.0), _Grain(200, age_j=60.0),
              _Grain(300, age_j=40.0), _Grain(400, age_j=20.0)]
    ages = _ages(grains)
    bloc, rapport = tapis_rotation.bloc(grains, [], 2, 2, LANE, MAINTENANT,
                                        ancres={"grains": {"ancre": 150}},
                                        ages_g=ages, exclus_g=set())
    assert [g.numero for g in bloc] == [200, 300], \
        "les deux plus anciennes, pas les numeros au-dessus de l'ancre"
    assert rapport["ordre"] == "age"


def test_les_numeros_deja_servis_sont_laises_de_cote():
    """Un numero servi et non decide attend son verdict : il n'est pas
    re-servi au tirage suivant."""
    grains = [_Grain(200, age_j=60.0), _Grain(300, age_j=40.0),
              _Grain(400, age_j=20.0)]
    ages = _ages(grains)
    bloc, _ = tapis_rotation.bloc(grains, [], 2, 2, LANE, MAINTENANT,
                                   ages_g=ages, exclus_g={200})
    assert [g.numero for g in bloc] == [300, 400]


def test_la_vague_suivante_prend_le_bloc_suivant():
    """La vague 1 ne ressert pas la vague 0 : elle decale dans l'ordre
    d'age."""
    grains = [_Grain(n, age_j=60.0 - n / 100.0) for n in (200, 300, 400, 500)]
    ages = _ages(grains)
    v0, _ = tapis_rotation.bloc(grains, [], 2, 2, LANE, MAINTENANT,
                                ages_g=ages, exclus_g=set())
    v1, _ = tapis_rotation.bloc(grains, [], 2, 2, LANE, MAINTENANT,
                                bloc_suivant=1, ages_g=ages, exclus_g=set())
    assert {g.numero for g in v0} & {g.numero for g in v1} == set()


def test_sans_age_la_selection_reste_la_rotation_par_numero():
    """Les conteneurs gardent la rotation par numero : leur tour reste
    lisible, et ils sont peu nombreux."""
    grains = [_Grain(100), _Grain(200), _Grain(300)]
    bloc, rapport = tapis_rotation.bloc(grains, [], 2, 2, LANE, MAINTENANT,
                                        ancres={"grains": {"ancre": 100}})
    assert [g.numero for g in bloc] == [200, 300]
    assert rapport["ordre"] == "numero"


# --- l'exclusion et le tour --------------------------------------------------

def test_un_numero_servi_et_decide_redevient_servable(tmp_path, monkeypatch):
    """Le verdict vide l'attente : l'issue peut etre re-servie plus tard
    (elle a ete visitée, elle ne bloque plus la tete)."""
    monkeypatch.setenv(tapis_etat.ENV_ETAT, str(tmp_path))
    etat = tapis_ancre.proposer(LANE, "grains", [7, 8], [])
    assert 7 in etat["grains"]["attente"], "le servi attend son verdict"
    etat = tapis_ancre.avancer(LANE, {7})
    assert 7 not in etat["grains"]["attente"], \
        "un numero decide sort de la file : il redevient servable"
    assert etat["grains"]["attente"].get(8) is False, \
        "l'autre attend toujours son verdict"


def test_un_numero_servi_et_non_decide_survit_au_curseur(tmp_path, monkeypatch):
    """Le curseur ne retire plus de la file un numero qui attend son
    verdict : sans cela, une issue ancienne servie par age (donc sous
    l'ancre) etait re-servie a chaque tirage."""
    monkeypatch.setenv(tapis_etat.ENV_ETAT, str(tmp_path))
    tapis_ancre.proposer(LANE, "grains", [7, 8], [])
    etat = tapis_ancre.avancer(LANE, {9})
    assert 7 in etat["grains"]["attente"], \
        "un numero en attente de verdict n'est pas retire par le curseur"


def test_un_tour_couvert_redonne_la_file(tmp_path, monkeypatch):
    """Quand plus rien n'est servable, la file est rendue et le tour
    recommence."""
    monkeypatch.setenv(tapis_etat.ENV_ETAT, str(tmp_path))
    tapis_ancre.proposer(LANE, "grains", [7, 8], [])
    etat = tapis_ancre.proposer(LANE, "grains", [9, 10], [], reinit=True)
    assert set(etat["grains"]["attente"]) == {9, 10}, \
        "la file rend les anciens et prend les nouveaux"


# --- LE TIRAGE REEL : LE VIEUX STOCK (dispatch du coordinateur, 22/11) -----
#
# « le tapis rapide doit aussi tirer du vieux stock (non_visites, par ex.
# #1203), avec un test qui le prouve sur un pool synthetique ».

def _noeud(n: int, cree: str) -> dict:
    return {"number": n, "title": f"Grain {n}", "createdAt": cree,
            "updatedAt": cree, "labels": {"nodes": []}}


def _run_faux(nodes: list[dict]):
    """Un faux `run` : metadonnees (GraphQL), citations (vide), PRs (vides)."""
    def run(argv, timeout):
        requete = " ".join(argv)
        if "graphql" in requete:
            return json.dumps({"data": {"repository": {"issues": {
                "pageInfo": {"hasNextPage": False, "endCursor": "c"},
                "nodes": nodes}}}})
        if argv[0] == "git":
            return ""
        return "[]"
    return run


def test_le_tirage_sert_le_vieux_stock():
    """Sur un pool SYNTHETIQUE, le tapis sert d'abord le vieux stock : une
    issue ancienne jamais visitee (#1203) passe devant les issues fraiches,
    qui attendent la fin de file (le mandat du 22/11)."""
    vieux = [_noeud(1203, "2025-01-15T00:00:00Z"),
             _noeud(1204, "2025-02-20T00:00:00Z")]
    frais = [_noeud(9000 + k, "2026-11-22T00:00:00Z") for k in range(5)]
    classe = tapis_leger.classer(LANE, MAINTENANT, 45, "graine",
                                  Path(__file__).resolve().parents[2],
                                  _run_faux(vieux + frais))
    # L'ancre est posee sur les numeros frais : c'est l'inversion mesuree
    # (la tete de numero sert ce qui vient d'etre cree).
    ancres = {"grains": {"ancre": 9000}}
    frais_n = {9000 + k for k in range(5)}
    # Le contre-exemple : la rotation par numero sert les issues fraiches.
    sans_age, _ = tapis_rotation.bloc(classe["grains"], [], 2, 2, LANE,
                                      MAINTENANT, ancres=ancres)
    assert {g.numero for g in sans_age} & frais_n, (
        "la rotation par numero sert les fraiches -- c'est l'inversion")
    ages, exclus, _ = tapis_age.tour(classe["grains"], ancres, MAINTENANT,
                                      classe["conteneurs"])
    bloc, rapport = tapis_rotation.bloc(classe["grains"], [], 2, 2, LANE,
                                        MAINTENANT, ancres=ancres,
                                        ages_g=ages, exclus_g=exclus)
    servis = {g.numero for g in bloc}
    assert {1203, 1204} <= servis, "le vieux stock passe en tete"
    assert not (servis & frais_n), (
        "les issues fraiches attendent la fin de file")
    assert rapport["ordre"] == "age"


# --- LE TEMOIN CONTROLE DE L'ORDRE (#28114) ---------------------------------
#
# Mission du coordinateur (25/11 08:15Z, DM `ai01-0815-picker-contrat`) :
# « une consolidation ADMISSIBLE passe avant un grain ordinaire plus ancien,
# puis la rotation visite le reste SANS AFFAMER LA FILE ».
#
# Les deux moities sont verifiees ici, sur un pool SYNTHETIQUE et un etat de
# lane dans un `tmp_path` : aucun reseau, aucune horloge machine. Le temoin
# est **contrrole** : il pose lui-meme les dates, les labels et l'etat de
# l'ancre, et il mesure ce que le picker rend -- il ne se contente pas de
# relire un ordre theorique.
#
# Ce fichier est le **foyer de l'ordre** (`coordination.tapis_age`) : c'est
# aussi la PR qui porte cet ordre (#27393, la cle de service) qui accueille
# le temoin -- pas un chantier a cote.

#: La consolidation ADMISSIBLE (label `consolidation` seul).
CONSO = 7101
#: La consolidation NON admissible (label `pause`) : elle doit disparaitre.
CONSO_PAUSE = 7102
#: Six grains ordinaires ages : de 200 a 100 jours.
VIEUX = tuple(range(7200, 7206))
#: Deux grains ordinaires frais : ils attendent la fin de file.
FRAIS = (7300, 7301)
#: Le format de date des metadonnees.
_JOUR = "%Y-%m-%dT%H:%M:%SZ"


def _meta(n: int, titre: str, cree: str, labels: tuple[str, ...] = ()) -> dict:
    """Une issue en metadonnees : la forme que rend `gh_selection.metadonnee`."""
    return {"number": n, "title": titre, "created_at": cree, "updated_at": cree,
            "labels": list(labels)}


def _run_pool(metas: list[dict]):
    """Le faux `run` : le pool en metadonnees, aucune PR, aucune citation."""
    nodes = [{"number": m["number"], "title": m["title"],
              "createdAt": m["created_at"], "updatedAt": m["updated_at"],
              "labels": {"nodes": [{"name": lab} for lab in m["labels"]]}}
             for m in metas]
    page = json.dumps({"data": {"repository": {"issues": {
        "pageInfo": {"hasNextPage": False, "endCursor": "c"},
        "nodes": nodes}}}})

    def run(argv, timeout):
        requete = " ".join(argv)
        if "issue(number:" in requete:
            return json.dumps({"data": {"repository": {}}})
        if "graphql" in requete:
            return page
        if argv[0] == "git":
            return ""
        return "[]"  # aucune PR ouverte
    return run


def _pool_temoin() -> list[dict]:
    """Le pool du temoin : une consolidation admissible, une consolidation en
    PAUSE (non admissible), six grains ordinaires ages, deux frais."""
    pool = [
        _meta(CONSO, "Consolidation admissible",
              (MAINTENANT - timedelta(days=1)).strftime(_JOUR),
              labels=("consolidation",)),
        _meta(CONSO_PAUSE, "Consolidation en pause",
              (MAINTENANT - timedelta(days=1)).strftime(_JOUR),
              labels=("consolidation", "pause")),
    ]
    for k, n in enumerate(VIEUX):
        pool.append(_meta(n, f"Grain ordinaire {n}",
                          (MAINTENANT - timedelta(days=200 - 20 * k)).strftime(_JOUR)))
    for n in FRAIS:
        pool.append(_meta(n, f"Grain frais {n}",
                          (MAINTENANT - timedelta(days=1)).strftime(_JOUR)))
    return pool


def _tirer(lane: str, pool: list[dict], monkeypatch, tmp_path,
           grains: int = 1) -> list[int]:
    """Un tirage sur le pool donne, l'ancre de la lane dans `tmp_path`.

    L'etat de lane est **persistant** d'un tirage a l'autre : c'est lui qui
    fait tourner la rotation (un numero servi attend son verdict, il n'est
    donc pas re-servi au tirage suivant).
    """
    monkeypatch.setenv(tapis_etat.ENV_ETAT, str(tmp_path))
    rapport, code = tapis_leger.tirage(lane, grains, MAINTENANT, 45, "graine",
                                       Path("."), _run_pool(pool))
    assert code == 0, "le tirage rend un rapport, pas un echec"
    return [g["numero"] for g in rapport["grains"]]


def test_le_temoin_controle_la_consolidation_admissible_passe_devant_le_grain_ordinaire_plus_ancien(tmp_path, monkeypatch):
    """Le temoin, premiere moitie : une consolidation **admissible** passe
    devant un grain ordinaire **plus ancien** (200 j).

    L'admissibilite est **discriminee**, pas supposee : la meme pool porte
    une consolidation en PAUSE (label `pause`), qui n'est **jamais** servie.
    Le grain servi en tete est donc admissible par ses DONNEES, et non par
    hasard.
    """
    pool = _pool_temoin()
    servis = _tirer(LANE, pool, monkeypatch, tmp_path)
    assert servis, "le tirage rend une file non vide"
    assert servis[0] == CONSO, (
        "la consolidation admissible passe devant le grain ordinaire de 200 j")
    assert VIEUX[0] in servis, \
        "le grain ordinaire le plus ancien est servi lui aussi"
    assert CONSO_PAUSE not in servis, \
        "la consolidation en pause n'est pas admissible : elle n'est pas servie"


def test_le_temoin_controle_la_rotation_visite_le_reste_du_pool_sans_affamer_la_file(tmp_path, monkeypatch):
    """Le temoin, seconde moitie : la rotation VISITE LE RESTE du pool, et
    la file ne s'AFFAME jamais.

    La fenetre vaut 3 grains : trois tirages successifs couvrent les 9
    grains servables. Un numero servi attend son verdict, il n'est donc pas
    re-servi au tirage suivant -- c'est cette exclusion qui fait tourner la
    rotation. Le tirage suivant, une fois le pool couvert, **rend la file** et
    recommence : la lane n'est jamais laissee sans grain.
    """
    pool = _pool_temoin()
    servables = {m["number"] for m in pool if "pause" not in m["labels"]}
    assert len(servables) == 9, "le pool servable compte 9 grains"
    tours = []
    for _ in range(4):
        servis = _tirer(LANE, pool, monkeypatch, tmp_path)
        assert servis, "la file ne s'affame pas : chaque tirage rend des grains"
        tours.append(set(servis))
    assert tours[0] == {CONSO, VIEUX[0], VIEUX[1]}, \
        "la consolidation d'abord, puis les plus anciens"
    vus = set().union(*tours[:3])
    assert vus == servables, \
        "la rotation visite le reste du pool, sans en laisser de cote"
    assert not (tours[0] & tours[1]) and not (tours[1] & tours[2]), \
        "un numero servi attend son verdict : il n'est pas re-servi"
    assert tours[3] == tours[0], \
        "le tour recommence : la file est rendue, la lane n'est pas laissee vide"


def test_la_cle_de_service_ne_casse_pas_la_priorite_de_consolidation():
    """La CLE DE SERVICE (#27393) remplace la creation dans la cle de l'ordre.

    Un grain **recemment servi** n'est plus un grain ancien : il part en fin
    de file, meme s'il est vieux. Mais la **consolidation** garde la tete :
    elle echappe a la bande des frais, meme servie recemment.
    """
    service = (MAINTENANT - timedelta(days=2)).isoformat()
    conso = _Grain(1, age_j=200.0, consolidation=True, cle_service=service)
    ancien = _Grain(2, age_j=200.0)
    servi = _Grain(3, age_j=200.0, cle_service=service)
    ages = _ages([servi, ancien, conso])
    assert ages[0] is conso, \
        "la consolidation reste en tete, meme servie recemment"
    assert ages[-1] is servi, \
        "un grain recemment servi part en fin de file"
    assert tapis_age.cle(conso, MAINTENANT)[3] == service, \
        "la cle de service est le departage a classe egale"
