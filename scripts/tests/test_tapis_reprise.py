"""La FILE DE REPRISE des numeros illisibles (`coordination/tapis_retry.py`).

Ce que ces tests prouvent :

- une tranche **entierement illisible** ne fige pas la rotation : le
  curseur passe par-dessus les illisibles, les autres restent servis
  (cas critique du peer, 19/11) ;
- les illisibles reviennent par une file de reprise **BOYNEE** : ils sont
  servis a nouveau, et la file ne grossit pas indefiniment ;
- un illisible qui finit par etre decide quitte la file.

Aucun test ne touche le reseau : la machine a etat est pure.
"""
from __future__ import annotations

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from coordination import tapis_ancre, tapis_retry, tapis_rotation, tapis_verdict  # noqa: E402

pytestmark = pytest.mark.usefixtures("forbid_shell_escape")

LANE = "myia-ai-01:CoursIA-2"


class _Grain:
    """Un grain minimal : la rotation ne lit que son numero."""

    def __init__(self, numero: int):
        self.numero = numero
        self.titre = f"issue {numero}"
        self.visites = 0
        self.conteneur = False
        self.notes: list[str] = []


def _illisible(n: int) -> dict:
    return {"numero": n, "code": "FIL_ILLISIBLE", "motif": "fil illisible"}


def test_une_tranche_entierement_inconnue_ne_gele_pas_les_autres(tmp_path, monkeypatch):
    """Le cas critique du peer (19/11) : #1 et #2 illisibles, #3..#6 lisibles.

    Les deux illisibles ne sont pas decides : ils sont PARKEs, et le
    curseur passe par-dessus. Les autres restent servis -- c'est la
    couverture qui compte, pas le verdict d'une lecture.
    """
    monkeypatch.setenv(tapis_ancre.ENV_ETAT, str(tmp_path))
    nums = list(range(1, 7))
    tapis_ancre.proposer(LANE, "grains", [1, 2])
    tapis_verdict.avancer(LANE, {}, {1: _illisible(1), 2: _illisible(2)})

    etat = tapis_ancre.lire(LANE)
    assert etat["grains"]["ancre"] == 2, "le curseur passe par-dessus les illisibles"
    assert set(etat["grains"]["inconnus"]) == {1, 2}, "les deux sont PARKEs"
    tranche = tapis_ancre.tranche(nums, etat["grains"]["ancre"], 2, 0)
    assert tranche == [3, 4], "#3..#6 restent servis"


def test_les_inconnus_reviennent_par_la_file_de_reprise(tmp_path, monkeypatch):
    """La file de reprise est le canal de retour des illisibles."""
    monkeypatch.setenv(tapis_ancre.ENV_ETAT, str(tmp_path))
    tapis_ancre.proposer(LANE, "grains", [1, 2])
    tapis_verdict.avancer(LANE, {}, {1: _illisible(1), 2: _illisible(2)})
    inc = tapis_ancre.lire(LANE)["grains"]["inconnus"]
    assert tapis_retry.a_retry(inc, 4) == [1, 2], "les deux reviennent"
    assert tapis_retry.a_retry(inc, 1) == [1], "la reprise est bornee par le bloc"


def test_le_bloc_sert_les_inconnus_en_plus_de_la_tranche(tmp_path, monkeypatch):
    """Le bloc du tour servi les illisibles : ils reviennent en service."""
    monkeypatch.setenv(tapis_ancre.ENV_ETAT, str(tmp_path))
    tapis_ancre.proposer(LANE, "grains", [1, 2])
    tapis_verdict.avancer(LANE, {}, {1: _illisible(1), 2: _illisible(2)})
    grains = [_Grain(n) for n in range(1, 7)]
    bloc, rapport = tapis_rotation.bloc(grains, [], 6, 2, LANE,
                                         __import__("datetime").datetime.now(),
                                         ancres=tapis_ancre.lire(LANE))
    servis = {g.numero for g in bloc}
    assert {1, 2} <= servis, "les illisibles sont servis a nouveau"
    assert 3 in servis or 4 in servis, "la tranche continue en meme temps"


def test_la_file_de_reprise_est_bornee(tmp_path, monkeypatch):
    """La file ne grossit pas indefiniment : le plus ancien est rendu."""
    monkeypatch.setenv(tapis_ancre.ENV_ETAT, str(tmp_path))
    nombres = list(range(1, tapis_retry.MAX_REPRISES + 6))
    tapis_ancre.proposer(LANE, "grains", nombres)
    tapis_verdict.avancer(LANE, {}, {n: _illisible(n) for n in nombres})
    inc = tapis_ancre.lire(LANE)["grains"]["inconnus"]
    assert len(inc) == tapis_retry.MAX_REPRISES, "la file est bornee"
    assert max(inc) == nombres[-1], "les plus recents sont gardes"


def test_un_inconnu_decide_quitte_la_file(tmp_path, monkeypatch):
    """Un illisible qui finit par etre lu quitte la file de reprise."""
    monkeypatch.setenv(tapis_ancre.ENV_ETAT, str(tmp_path))
    tapis_ancre.proposer(LANE, "grains", [1, 2])
    tapis_verdict.avancer(LANE, {}, {1: _illisible(1), 2: _illisible(2)})
    assert set(tapis_ancre.lire(LANE)["grains"]["inconnus"]) == {1, 2}
    tapis_verdict.avancer(LANE, {1: object()}, {})
    assert 1 not in tapis_ancre.lire(LANE)["grains"]["inconnus"], \
        "un numero decide n'est plus a re-proposer"
