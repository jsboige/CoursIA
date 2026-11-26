"""Le grain NON TENTE : ni verdict, ni refus -- et pour autant un trou.

Ce que ces tests prouvent :

- une qualification **PARTIELLE** (un grain propose, jamais qualifie) ne
  **fige** pas le curseur : la tranche suivante n'est pas la meme, et les
  numeros suivants du pool sont servis (contre-exemple mesure le 19/11 :
  pool 1..6, ancre 2, tranche [3, 4], seul 4 qualifie -> la tranche [3, 4]
  revenait a l'identique sur quatre cycles, 5 et 6 n'etaient JAMAIS
  proposes) ;
- le grain non tente est **parque sous son propre code** (`NON_TENTE`),
  distinct de `FIL_ILLISIBLE` (la lecture impossible) et de tout verdict
  terminal ;
- il **revient au service** par la file de reprise : il n'est ni acquitte
  ni perdu ;
- la voie des **vagues** passe la preuve par le diff, comme la voie
  nominative : sans elle, l'ecart `LIVREE` reposerait sur le seul
  marqueur du fil.

Aucun test ne touche le reseau : l'etat est ecrit dans un repertoire
temporaire, et la preuve de la voie vagues est un stub.
"""
from __future__ import annotations

import sys
from datetime import UTC, datetime
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from coordination import tapis_ancre, tapis_composition, tapis_etat  # noqa: E402
from coordination import tapis_non_tente  # noqa: E402
from coordination import tapis_vagues, tapis_verdict  # noqa: E402

pytestmark = pytest.mark.usefixtures("forbid_shell_escape")

MAINTENANT = datetime(2026, 11, 19, 12, 0, tzinfo=UTC)
LANE = "test:non-tente"


class _Grain:
    """Un grain minimal : la rotation ne lit que son numero."""

    def __init__(self, numero: int):
        self.numero = numero
        self.titre = f"issue {numero}"
        self.visites = 0
        self.conteneur = False
        self.notes: list[str] = []


def _grains(numeros: list[int]) -> list[_Grain]:
    return [_Grain(n) for n in numeros]


def _tour(lane: str, nums: list[int], taille: int = 2):
    """Propose la tranche d'apres l'ancre, et rend cette tranche.

    Un numero propose mais non confirme est **non tente** : il n'apparait
    ni dans les confirmes ni dans les ecartees.
    """
    from coordination import tapis_tranche  # noqa: PLC0415 - import local

    etat = tapis_ancre.lire(lane)
    tranche = tapis_tranche.tranche(nums, etat["grains"]["ancre"], taille)
    tapis_ancre.proposer(lane, "grains", tranche)
    return tranche


def test_le_curseur_ne_fige_pas_sur_un_grain_non_tente(tmp_path, monkeypatch):
    """Le contre-exemple du peer : la tranche ne doit pas revenir a l'identique."""
    monkeypatch.setenv(tapis_ancre.ENV_ETAT, str(tmp_path))
    nums = [1, 2, 3, 4, 5, 6]

    # Tour 1 : [1, 2] qualifie en entier -> l'ancre passe a 2.
    _tour(LANE, nums)
    tapis_ancre.avancer(LANE, terminaux={1, 2})
    assert tapis_ancre.lire(LANE)["grains"]["ancre"] == 2

    # Tour 2 : la tranche [3, 4] est proposee, seul 4 est qualifie.
    _tour(LANE, nums)
    etat = tapis_ancre.avancer(LANE, terminaux={4})
    assert etat["grains"]["ancre"] == 4, (
        "le curseur ne doit pas s'arreter sur un grain propose mais non "
        "qualifie : sinon la meme tranche revient et le pool ne progresse pas")

    # Tour 3 : la tranche suivante est [5, 6] -- pas [3, 4] a nouveau.
    from coordination import tapis_tranche  # noqa: PLC0415 - import local

    suivante = tapis_tranche.tranche(nums, etat["grains"]["ancre"], 2)
    assert suivante == [5, 6], f"tranche attendue [5, 6], obtenue {suivante}"


def test_le_grain_non_tente_est_parque_sous_son_code(tmp_path, monkeypatch):
    """`NON_TENTE` est distinct de `FIL_ILLISIBLE` et d'un verdict terminal."""
    monkeypatch.setenv(tapis_ancre.ENV_ETAT, str(tmp_path))
    nums = [1, 2, 3, 4, 5, 6]

    _tour(LANE, nums)
    tapis_ancre.avancer(LANE, terminaux={1, 2})
    _tour(LANE, nums)
    etat = tapis_ancre.avancer(LANE, terminaux={4})

    inc = etat["grains"]["inconnus"]
    assert 3 in inc, "le grain non tente doit etre parke, pas perdu"
    assert inc[3]["code"] == tapis_non_tente.NON_TENTE
    assert inc[3]["code"] != "FIL_ILLISIBLE", (
        "un grain non tente n'est pas un fil illisible : rien n'a ete lu")
    assert 4 not in inc, "un grain qualifie n'est pas parke"


def test_le_grain_non_tente_revient_au_service(tmp_path, monkeypatch):
    """Le grain non tente n'est ni acquitte ni perdu : il revient par la reprise."""
    monkeypatch.setenv(tapis_ancre.ENV_ETAT, str(tmp_path))
    nums = [1, 2, 3, 4, 5, 6]

    _tour(LANE, nums)
    tapis_ancre.avancer(LANE, terminaux={1, 2})
    _tour(LANE, nums)
    etat = tapis_ancre.avancer(LANE, terminaux={4})

    grains = _grains(nums)
    bloc, _conteneurs, _primaires, reprises = tapis_composition.compose(
        grains, [], 2, 0, etat["grains"]["ancre"], None,
        etat["grains"]["inconnus"], {}, 0, 0)
    assert 3 in reprises["grains"], (
        "le grain non tente doit revenir au service : il n'est ni acquitte "
        "ni perdu")
    assert 3 in [g.numero for g in bloc]


def test_un_fil_illisible_garde_son_code(tmp_path, monkeypatch):
    """Le refus de lecture reste distinct : il porte SON code."""
    monkeypatch.setenv(tapis_ancre.ENV_ETAT, str(tmp_path))
    nums = [1, 2, 3, 4]

    _tour(LANE, nums)
    etat = tapis_ancre.avancer(
        LANE, terminaux={1},
        inconnus={2: {"code": "FIL_ILLISIBLE", "motif": "fil illisible"}})
    inc = etat["grains"]["inconnus"]
    assert inc[2]["code"] == "FIL_ILLISIBLE"
    assert inc[2]["code"] != tapis_non_tente.NON_TENTE


def test_la_voie_vagues_passe_la_preuve_du_diff(monkeypatch):
    """La voie vagues qualifie avec la preuve, comme la voie nominative."""
    capture: dict = {}

    def _qualifier(*args, **kwargs):
        capture.update(kwargs)
        return ([], {}, [], False, 0, {})

    def _bloc(*args, **kwargs):
        return (_grains([1, 2]), {"bloc": 1, "blocs": 1,
                                  "primaires": {"grains": [1, 2],
                                                "conteneurs": []},
                                  "reprises": {"grains": [], "conteneurs": []}})

    monkeypatch.setattr(tapis_vagues.tq, "qualifier", _qualifier)
    monkeypatch.setattr(tapis_vagues.tapis_rotation, "bloc", _bloc)

    tapis_vagues.vagues(_grains([1, 2]), [], LANE, MAINTENANT, 45, [], None,
                        8, max_vagues=1, taille=2)

    preuve = capture.get("preuve")
    assert preuve is not None, (
        "la voie vagues doit passer la preuve par le diff : sans elle, "
        "l'ecart LIVREE repose sur le seul marqueur du fil")
    assert callable(preuve)


# --- LA GARANTIE DE VISITE : un parke finit par etre relu (19/11) ----------

def _tour_complet(lane: str, grains: list, taille: int, budget: int):
    """Un tour reel : le bloc, la proposition, la qualification du budget.

    Rend `(lot, qualifies)` : le lot rendu par la rotation, et les numeros
    que la lane qualifie (les `budget` premiers du lot -- c'est ainsi
    qu'une lane qui n'a qu'un candidat par tour se comporte).
    """
    from coordination import tapis_rotation  # noqa: PLC0415 - import local

    ancres = tapis_ancre.lire(lane)
    bloc, fenetre = tapis_rotation.bloc(grains, [], len(grains), taille, lane,
                                         MAINTENANT, ancres=ancres)
    tapis_ancre.proposer(lane, "grains", fenetre["primaires"]["grains"],
                          fenetre["reprises"]["grains"])
    nums = [g.numero for g in bloc]
    qualifies = nums[:budget]
    tapis_ancre.avancer(lane, terminaux=set(qualifies))
    return nums, qualifies


def test_le_lot_alterne_la_primaire_et_la_reprise(tmp_path, monkeypatch):
    """Le lot ne laisse pas les reprises en queue : une tranche bornee les voit.

    C'est le defaut mesure par le peer (19/11) : les numeros 2, 4 et 6,
    parkes derriere la primaire, n'etaient JAMAIS lus quand la lane ne
    qualifiait qu'un candidat par tour.
    """
    monkeypatch.setenv(tapis_ancre.ENV_ETAT, str(tmp_path))
    nums = [1, 2, 3, 4, 5, 6]

    _tour(lane := LANE, nums)
    tapis_ancre.avancer(lane, terminaux={1, 2})
    _tour(lane, nums)
    etat = tapis_ancre.avancer(lane, terminaux={4})

    grains = _grains(nums)
    bloc, _c, _p, reprises = tapis_composition.compose(
        grains, [], 2, 0, etat["grains"]["ancre"], None,
        etat["grains"]["inconnus"], {}, 0, 0)
    nums_lot = [g.numero for g in bloc]
    reprises_lot = [n for n in nums_lot if n in reprises["grains"]]
    assert reprises_lot, "la reprise doit figurer dans le lot"
    assert nums_lot.index(reprises_lot[0]) <= 1, (
        "une reprise en queue du lot n'est jamais lue quand la lane ne "
        f"qualifie qu'un candidat par tour : lot={nums_lot}")


def test_la_phase_alterne_le_sens_du_lot(tmp_path, monkeypatch):
    """Un tour sur deux, la reprise passe DEVANT la primaire.

    C'est le prix de la garantie de visite : avec un budget de lecture d'un
    seul candidat, il faut que la reprise passe devant un tour sur deux.
    """
    from coordination import tapis_rotation  # noqa: PLC0415 - import local

    monkeypatch.setenv(tapis_ancre.ENV_ETAT, str(tmp_path))
    nums = [1, 2, 3, 4, 5, 6]
    grains = _grains(nums)

    _tour(lane := LANE, nums)
    tapis_ancre.avancer(lane, terminaux={1, 2})
    _tour(lane, nums)
    tapis_ancre.avancer(lane, terminaux={4})

    premiers, reprises_lot = [], []
    for _ in range(2):
        ancres = tapis_ancre.lire(lane)
        bloc, fenetre = tapis_rotation.bloc(grains, [], len(grains), 2, lane,
                                             MAINTENANT, ancres=ancres)
        premiers.append([g.numero for g in bloc][0])
        reprises_lot.append(set(fenetre["reprises"]["grains"]))
        tapis_ancre.proposer(lane, "grains", fenetre["primaires"]["grains"],
                              fenetre["reprises"]["grains"])

    assert premiers[0] != premiers[1], (
        "le sens du lot doit alterner : sinon la reprise n'est jamais "
        f"relue, lot={premiers}")
    assert premiers[0] in reprises_lot[0] or premiers[1] in reprises_lot[1], (
        "un des deux tours doit passer la reprise devant la primaire "
        f"(premiers={premiers}, reprises={reprises_lot})")


def test_chaque_parque_est_relu_enfin(tmp_path, monkeypatch):
    """LA GARANTIE DE VISITE : sur 12 tours, chaque numero est servi.

    Le scenario du peer (19/11) : pool 1..6, taille 2, un seul candidat
    qualifie par tour. Avant l'entrelacement, les numeros 2, 4 et 6
    restaient parques derriere la primaire et n'etaient JAMAIS servis.
    """
    monkeypatch.setenv(tapis_ancre.ENV_ETAT, str(tmp_path))
    nums = [1, 2, 3, 4, 5, 6]
    grains = _grains(nums)

    servis: list[int] = []
    for _ in range(12):
        _lot, qualifies = _tour_complet(LANE, grains, 2, 1)
        servis.extend(qualifies)

    manquants = sorted(set(nums) - set(servis))
    assert not manquants, (
        f"des numeros parkes n'ont jamais ete relus : {manquants} "
        f"(servis : {sorted(set(servis))})")


def test_l_etat_porte_le_commit_du_code(tmp_path, monkeypatch):
    """L'etat est lie au code qui l'a ecrit : deux etats ne sont comparables
    que s'ils viennent du meme commit."""
    from coordination import tapis_etat_commit  # noqa: PLC0415 - import local

    monkeypatch.setenv(tapis_ancre.ENV_ETAT, str(tmp_path))
    _tour(lane := LANE, [1, 2])
    etat = tapis_ancre.lire(lane)
    attendu = tapis_etat_commit.commit()
    assert etat["grains"]["commit"] == attendu, (
        "l'etat doit porter le commit du code qui l'a ecrit : sans lui, "
        "comparer deux etats de semantiques differentes n'a pas de sens")
    assert etat["grains"]["phase"] >= 1, (
        "la phase compte les propositions : elle commande l'alternance")


def test_une_qualification_hors_tranche_ne_fait_pas_avancer_le_curseur(
        tmp_path, monkeypatch):
    """TEMOIN (review du peer, 19/11) : l'avance est BORNEE au lot.

    Une qualification nominative du seul 999 faisait avancer les ancres des
    primaires pendantes [1, 2] et [100, 101] : le curseur annoncait une
    couverture que personne n'avait mesuree. Les primaires restent en
    attente ; seule une qualification qui les TOUCHE les fait avancer.
    """
    monkeypatch.setenv(tapis_ancre.ENV_ETAT, str(tmp_path))
    tapis_ancre.proposer(LANE, "grains", [1, 2])
    tapis_ancre.proposer(LANE, "conteneurs", [100, 101])
    tapis_verdict.avancer(LANE, {999: object()}, {}, {999})
    etat = tapis_ancre.lire(LANE)
    assert etat["grains"]["ancre"] is None, "les primaires pendantes ne bougent pas"
    assert etat["conteneurs"]["ancre"] is None
    assert 1 in etat["grains"]["attente"] and 2 in etat["grains"]["attente"]
    assert 100 in etat["conteneurs"]["attente"]
    # Le CONTRE-TEMOIN : un lot qui TOUCHE la tranche fait avancer le curseur,
    # mais jusqu'au dernier numero pris en charge -- et PAS au-dela.
    tapis_verdict.avancer(LANE, {1: object()}, {}, {1})
    etat = tapis_ancre.lire(LANE)
    assert etat["grains"]["ancre"] == 1, (
        "la tranche en charge avance le curseur jusqu'au dernier numero "
        f"pris en charge (ancre={etat['grains']['ancre']})")


def test_le_lot_proprietaire_borne_le_curseur(tmp_path, monkeypatch):
    """TEMOIN (revue du peer, 19/11) : le LOT fait la loi, pas le chevauchement.

    Primaire pendante [1, 2], appel nominatif lot={1} : le chevauchement
    rendait la tranche "en charge", puis 2 etait **parque** et le curseur
    sautait a 2 -- une couverture que personne n'avait mesuree. Le lot
    PROPRIETAIRE commande : le curseur s'arrete a 1, et 2 reste en attente
    (ni decide, ni refuse, ni parke).
    """
    monkeypatch.setenv(tapis_ancre.ENV_ETAT, str(tmp_path))
    tapis_ancre.proposer(LANE, "grains", [1, 2])
    tapis_verdict.avancer(LANE, {1: object()}, {}, {1})
    etat = tapis_ancre.lire(LANE)
    assert etat["grains"]["ancre"] == 1, (
        "le curseur s'arrete au dernier numero que le lot a pris en charge "
        f"(ancre={etat['grains']['ancre']})")
    assert 2 not in etat["grains"]["inconnus"], (
        "un numero que le lot ne prend pas en charge n'est pas parke : "
        "rien n'a ete decide sur lui")
    assert 2 in etat["grains"]["attente"], "il reste en attente"


def test_une_primaire_parquee_etrangere_ne_fait_pas_avancer_le_curseur(
        tmp_path, monkeypatch):
    """TEMOIN (revue du peer, 19/11) : la reprise ne porte pas le curseur.

    Une primaire deja **parquee** (refus de lecture), etrangere a la tranche
    du tour, ne doit pas faire avancer le curseur : avant, la branche "n in
    inc" precedait le test de charge, et le curseur sautait sur un numero
    que personne n'avait servi.
    """
    monkeypatch.setenv(tapis_ancre.ENV_ETAT, str(tmp_path))
    # Tour 1 : la primaire [10, 11] est proposee.
    tapis_ancre.proposer(LANE, "grains", [10, 11])
    # Tour 2 : une autre tranche est proposee ; le lot prend 10 en charge
    # et la lecture echoue : 10 est parque, sous SON code de refus.
    tapis_ancre.proposer(LANE, "grains", [20])
    tapis_verdict.avancer(LANE, {}, {10: {"numero": 10, "code": "FIL_ILLISIBLE",
                                           "motif": "fil illisible"}}, {10})
    etat = tapis_ancre.lire(LANE)
    assert etat["grains"]["ancre"] is None, "le refus ne fait pas avancer"
    assert etat["grains"]["inconnus"][10]["code"] == "FIL_ILLISIBLE"
    # Tour 3 : la primaire [10, 11] revient, et le lot ne la touche pas.
    tapis_ancre.proposer(LANE, "grains", [10, 11])
    tapis_verdict.avancer(LANE, {999: object()}, {}, {999})
    etat = tapis_ancre.lire(LANE)
    assert etat["grains"]["ancre"] is None, (
        "une primaire etrangere deja parquee ne fait pas avancer le curseur "
        f"(ancre={etat['grains']['ancre']})")
    assert etat["grains"]["inconnus"][10]["code"] == "FIL_ILLISIBLE", (
        "son code de refus est preserve")
