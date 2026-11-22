"""L'ORDRE D'AGE du tapis : les issues anciennes d'abord (mandat du 22/11).

Verbatim du mandat : « le tapis devrait pouvoir piocher les issues
anciennes prioritairement sur les plus recentes, meme si celles qui n'ont
jamais ete visitees peuvent etre traitees parmi la tete du tapis. Si ca ne
fonctionne pas, alors on mettra les nouvelles issues en fin de tapis. »

Ce que ces tests prouvent, sur un pool SYNTHETIQUE :

- la **cle** de l'ordre d'age : la bande des fraiches passe devant tout (fin
  de file), la jamais visitée passe devant, puis la plus ancienne ;
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

import sys
from datetime import UTC, datetime, timedelta
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from coordination import tapis_age, tapis_ancre, tapis_etat, tapis_rotation  # noqa: E402

pytestmark = pytest.mark.usefixtures("forbid_shell_escape")

MAINTENANT = datetime(2026, 11, 22, 9, 0, tzinfo=UTC)
LANE = "myia-ai-01:CoursIA-2"


class _Grain:
    """Un grain minimal : l'ordre d'age lit le numero, la creation, les visites."""

    def __init__(self, numero: int, age_j: float = 30.0, visites: int = 0,
                 conteneur: bool = False):
        self.numero = numero
        self.titre = f"issue {numero}"
        self.cree_le = (MAINTENANT - timedelta(days=age_j)).isoformat()
        self.visites = visites
        self.visites_total = visites
        self.conteneur = conteneur
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
    assert tapis_age.cle(g, MAINTENANT)[:3] == (0, 1, g.cree_le)
    assert tapis_age.age_h(g, MAINTENANT) == pytest.approx(30 * 24, rel=1e-3)


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
