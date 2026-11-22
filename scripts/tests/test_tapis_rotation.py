"""La ROTATION par NUMERO : le tour se ferme, meme quand le classement bouge.

Ce que ces tests prouvent :

- le bloc **publie** les numeros qu'il visite et ceux qu'il ne visite pas :
  chaque numero du pool sort avec un verdict (visite / non visite) -- la
  derniere qualification par numero se mesure la (revue du 19/11, #27242) ;
- un **reclassement entre deux tours** (le classement change, l'ordre des
  numeros non) ne fait pas servir deux fois le meme numero : c'est le
  contre-exemple de la revue -- deux blocs de taille 2 sur [A, B, C, D] puis
  [C, D, A, B] servent A et B deux fois et jamais C, D ;
- le tour se ferme en `ceil(pool / taille)` tours, et le **delai max** publie
  borne la duree de ce tour ;
- la **sortie courte** publie le delai max et les numeros non visites.

Aucun test ne touche le reseau : le module est pur, et la sortie courte est
construite a la main.
"""
from __future__ import annotations

import sys
from datetime import UTC, datetime
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from coordination import tapis_ancre, tapis_etat, tapis_leger, tapis_rotation  # noqa: E402

pytestmark = pytest.mark.usefixtures("forbid_shell_escape")

MAINTENANT = datetime(2026, 11, 19, 7, 50, tzinfo=UTC)
LANE = "myia-ai-01:CoursIA-2"


class _Grain:
    """Un grain minimal : la rotation ne lit que son numero.

    `visites` simule le **classement** (ce que la lane a deja visite) :
    le reclassement entre deux tours change ce classement, pas les numeros.
    """

    def __init__(self, numero: int, visites: int = 0):
        self.numero = numero
        self.titre = f"issue {numero}"
        self.visites = visites
        self.conteneur = False
        self.notes: list[str] = []


def _grains(paires: list[tuple[int, int]]) -> list[_Grain]:
    return [_Grain(n, v) for n, v in paires]


def test_le_bloc_publie_les_numeros_visites_et_non_visites():
    grains = _grains([(11, 5), (12, 4), (13, 3), (14, 2)])
    bloc, rapport = tapis_rotation.bloc(grains, [], 4, 2, LANE, MAINTENANT)

    assert len(bloc) == 2, "le bloc sert `taille` grains"
    assert rapport["visites"] == sorted(g.numero for g in bloc)
    non_visites = rapport["non_visites"]
    assert set(rapport["visites"]) | set(non_visites) == {11, 12, 13, 14}, \
        "chaque numero du pool sort avec un verdict"
    assert not set(rapport["visites"]) & set(non_visites), \
        "un numero ne peut etre ni visite ni non visite"


def test_un_reclassement_entre_deux_tours_ne_sert_pas_deux_fois_le_meme_numero():
    """Le contre-exemple de la revue : le classement bouge, les numeros non.

    Tour 0 : classement par visites decroissant. Tour 1 : classement
    reordonne -- si la rotation suivait la POSITION, A et B seraient servis
    deux fois et C, D jamais.
    """
    tour0 = _grains([(1, 5), (2, 4), (3, 3), (4, 2)])
    tour1 = _grains([(4, 9), (1, 8), (3, 7), (2, 6)])

    _, r0 = tapis_rotation.bloc(tour0, [], 4, 2, LANE, MAINTENANT)
    _, r1 = tapis_rotation.bloc(tour1, [], 4, 2, LANE, MAINTENANT, bloc_suivant=1)

    vus = r0["visites"] + r1["visites"]
    assert len(vus) == len(set(vus)), "aucun numero servi deux fois"
    assert set(vus) == {1, 2, 3, 4}, "le tour se ferme"


def test_le_tour_se_ferme_en_ceil_pool_sur_taille_tours():
    pool = [(n, n) for n in range(1, 7)]
    grains = _grains(pool)
    vus: list[int] = []
    for tour in range(3):
        _, rapport = tapis_rotation.bloc(grains, [], 6, 2, LANE, MAINTENANT,
                                         bloc_suivant=tour)
        vus += rapport["visites"]
    assert sorted(vus) == [n for n, _ in pool], "chaque numero du pool est servi"
    assert len(vus) == len(set(vus)), "une seule fois"


def test_le_delai_max_publie_borne_la_duree_du_tour():
    grains = _grains([(n, n) for n in range(1, 7)])
    _, rapport = tapis_rotation.bloc(grains, [], 6, 2, LANE, MAINTENANT)
    assert rapport["delai_max_h"] == tapis_rotation.HEURES_TRANCHE * rapport["blocs"]
    assert rapport["ordre"] == "numero"


def _rapport_minimal(fenetre: dict) -> dict:
    return {
        "lecture": {"issues": 6, "selection_s": 0.1, "budget_s": 60.0,
                    "phases": {"citations_s": 0.1, "prs_s": 0.1}},
        "lane": LANE, "maintenant": "2026-11-19T07:50:00Z",
        "grains": [], "vos_prs": [], "fenetre": fenetre,
        "qualification": {"organe": "test", "quand": "maintenant", "ecarts": 0},
    }


def test_la_sortie_courte_publie_le_delai_max_et_les_numeros_non_visites():
    grains = _grains([(n, n) for n in range(1, 7)])
    _, fenetre = tapis_rotation.bloc(grains, [], 6, 2, LANE, MAINTENANT)
    texte = tapis_leger.texte(_rapport_minimal(fenetre))

    assert "delai max" in texte, "le delai max est publie"
    assert "non visite" in texte, "les numeros non visites sont publies"
    for n in fenetre["non_visites"]:
        assert f"#{n}" in texte, f"le numero {n} non visite est nomme"


def test_le_bloc_vide_ne_publie_aucun_numero_non_visite():
    _, rapport = tapis_rotation.bloc([], [], 0, 2, LANE, MAINTENANT)
    assert rapport["visites"] == []
    assert rapport["non_visites"] == []


# --- L'ANCRE : le tour se ferme meme quand le pool change (19/11) ----------

def test_une_cloture_ne_saute_pas_de_numero():
    """Le temoin du peer (19/11) : pool 1..8, blocs de 2, offset 0.

    Une rotation qui avance par POSITION sert {1,2}, puis -- #1 cloture --
    {4,5}, {6,7}, {8,2} : **#3 reste ouverte et n'a jamais ete visitee**.
    L'ANCRE (le dernier numero qualifie) ferme le tour : #3 est servie.
    """
    grains = _grains([(n, 0) for n in range(1, 9)])
    _, r0 = tapis_rotation.bloc(grains, [], 8, 2, LANE, MAINTENANT,
                                ancres={"grains": 0})
    assert r0["visites"] == [1, 2], "l'ancre 0 demarre au plus petit numero"
    ancre = r0["ancres_proposees"]["grains"]
    assert ancre == 2, "l'ancre candidate est le dernier numero visite"

    restants = _grains([(n, 0) for n in range(2, 9)])  # #1 est cloturee
    vus = set(r0["visites"])
    for _ in range(4):
        _, r = tapis_rotation.bloc(restants, [], 7, 2, LANE, MAINTENANT,
                                   ancres={"grains": ancre})
        vus |= set(r["visites"])
        ancre = r["ancres_proposees"]["grains"]
    assert 3 in vus, "#3 est encore ouverte : elle doit etre servie"


def test_le_tour_se_ferme_avec_l_ancre_meme_apres_une_cloture():
    """Un tour complet : chaque numero encore ouvert est servi UNE fois."""
    grains = _grains([(n, 0) for n in range(1, 9)])
    _, r = tapis_rotation.bloc(grains, [], 8, 2, LANE, MAINTENANT,
                                ancres={"grains": 0})
    ancre = r["ancres_proposees"]["grains"]
    vus = list(r["visites"])
    for _ in range(3):
        _, r = tapis_rotation.bloc(grains, [], 8, 2, LANE, MAINTENANT,
                                   ancres={"grains": ancre})
        vus += r["visites"]
        ancre = r["ancres_proposees"]["grains"]
    assert sorted(vus) == list(range(1, 9)), "chaque numero est servi"
    assert len(vus) == len(set(vus)), "une seule fois"


def test_une_arrivee_est_servie_sans_sauter_le_tour():
    """Un numero qui arrive entre deux tranches n'ecarte pas le suivant."""
    grains = _grains([(n, 0) for n in range(1, 5)])
    _, r = tapis_rotation.bloc(grains, [], 4, 2, LANE, MAINTENANT,
                                ancres={"grains": 0})
    ancre = r["ancres_proposees"]["grains"]
    avec_arrivee = _grains([(n, 0) for n in range(1, 6)])  # #5 est arrive
    _, r2 = tapis_rotation.bloc(avec_arrivee, [], 5, 2, LANE, MAINTENANT,
                                ancres={"grains": ancre})
    assert r2["visites"] == [3, 4], "la tranche continue apres l'ancre"
    assert r2["ancres_proposees"]["grains"] == 4


def test_la_priorite_est_visible_a_la_sortie_du_bloc():
    """La rotation choisit QUOI servir ; l'ordre de PRIORITE reste visible.

    Le classement d'entree (la priorite) est 3, 1, 4, 2 : le bloc doit
    rendre ces numeros DANS cet ordre, pas dans l'ordre des numeros.
    """
    grains = _grains([(3, 9), (1, 8), (4, 7), (2, 6)])
    bloc, _ = tapis_rotation.bloc(grains, [], 4, 4, LANE, MAINTENANT,
                                   ancres={"grains": 0})
    assert [g.numero for g in bloc] == [3, 1, 4, 2], \
        "la priorite d'entree est l'ordre rendu"


def test_une_ancre_inconnue_ne_s_acquitte_pas(tmp_path, monkeypatch):
    """Un fichier d'ancre illisible ne vaut pas zero : il vaut inconnu."""
    monkeypatch.setenv(tapis_ancre.ENV_ETAT, str(tmp_path))
    inconnu = {"grains": {"ancre": None, "tour": 0, "attente": {},
                          "inconnus": {}, "primaire": []},
               "conteneurs": {"ancre": None, "tour": 0, "attente": {},
                              "inconnus": {}, "primaire": []}}
    assert tapis_ancre.lire("myia-ai-01:CoursIA-2") == inconnu
    chemin = tapis_etat.chemin_etat("myia-ai-01:CoursIA-2")
    chemin.parent.mkdir(parents=True, exist_ok=True)
    chemin.write_text("{pas du json", encoding="utf-8")
    assert tapis_ancre.lire("myia-ai-01:CoursIA-2") == inconnu
    assert tapis_ancre.position([1, 2, 3], None) == 0
    assert tapis_ancre.position([1, 2, 3], 2) == 2
    assert tapis_ancre.position([1, 2, 3], 9) == 0, "le tour a boucle"
