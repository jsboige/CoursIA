"""#22983 -- la phase claims du tapis est servie par l'instantane local.

Le transport batch de ``check_claims`` (lancement de
``check_lane_claim.py`` en sous-processus) est RETIRE : le LECTEUR est
importe dans le processus du tapis et alimente par l'instantane local
(``scripts/coordination/gh_snapshot.py``). La fenetre de service reste ce
qu'elle etait -- c'est la SOURCE des claims qui change.

Ce fichier verrouille le nouveau contrat :

1. le transport historique n'existe plus : ses symboles ont disparu du
   module ;
2. ``check_claims`` ne lance AUCUN sous-processus, dans les deux modes ;
3. le mode STRICT est fail-CLOSED : sans instantane servant la fenetre,
   aucun grain n'est servi ;
4. le mode STRICT ne rafraichit PAS l'instantane -- le rafraichissement
   est la phase reseau, qui precede le tirage.

Aucun reseau : tout lancement d'enfant est refuse par un faux qui echoue.
"""

import argparse
import sys
import types
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "coordination"))

import check_lane_claim as clc  # noqa: E402
import pick_idle_grain as pig  # noqa: E402


def _aucun_enfant(monkeypatch):
    """Fait echouer tout lancement d'enfant Python ou de `gh`."""

    def refuse(*a, **k):
        pytest.fail("un sous-processus a ete lance : le transport est retire")

    monkeypatch.setattr(pig.subprocess, "run", refuse)
    monkeypatch.setattr(pig, "_run_bounded", refuse)


def _instantane_faux(monkeypatch, *, sert=True):
    """Faux module d'instantane : `refresh` echoue, `serves` repond."""
    fake = types.ModuleType("coordination.gh_snapshot")

    def _refresh(*a, **k):
        pytest.fail("l'instantane a ete rafraichi pendant le tirage")

    fake.refresh = _refresh
    fake.load_snapshot = lambda repo: {"issues": {}, "comments": {}}
    fake.serves = lambda snapshot, numbers, ttl_seconds=None: sert
    monkeypatch.setitem(sys.modules, "coordination.gh_snapshot", fake)
    monkeypatch.setattr(clc, "set_snapshot", lambda snap: None)
    monkeypatch.setattr(clc, "_snapshot_issue_payload",
                        lambda issue: {"number": int(issue)})
    monkeypatch.setattr(
        clc, "check_issues_batch",
        lambda issues, lane, **kw: {"results": {i: {"code": "FREE",
                                                     "human": "libre"}
                                                for i in issues}})
    return fake


def test_grains_50_la_fenetre_de_service_depasse_70():
    """Le critere de sortie du dispatch : a --grains 50 la fenetre vaut
    300 numeros, pas 70 -- ancrage mecanique de l'objectif."""
    args = argparse.Namespace(grains=50)
    window = pig.belt_service_window(args, 10_000)
    assert window == 300
    assert window > 70


def test_le_transport_historique_est_retire():
    """Les symboles du transport `subprocess` ont disparu du module.

    Un transport qui reviendrait reparerait le fail-OPEN qu'il portait :
    c'est donc un invariant de NON-REGRESSION, pas unePreference.
    """
    for name in ("_check_claims_one_batch", "_check_claims_sliced",
                 "BELT_CLAIMS_WORKERS", "BELT_CLAIMS_SLICE_MIN"):
        assert not hasattr(pig, name), (
            f"{name} existe encore : le transport `subprocess` de "
            "check_lane_claim.py n'est pas retire")
    # Le fail-OPEN par mur de temps n'a plus de code : `UNCHECKED` n'a
    # qu'un producteur, et ce producteur etait le transport.
    assert not hasattr(pig, "CLAIM_CODE_UNCHECKED")


def test_check_claims_ne_lance_aucun_sous_processus(monkeypatch):
    """Les DEUX modes servent leurs verdicts sans lancer d'enfant."""
    _aucun_enfant(monkeypatch)
    monkeypatch.setattr(pig, "_build_open_prs_cache_for_belt",
                        lambda lane: None)
    monkeypatch.setattr(
        pig, "_claims_in_process",
        lambda numbers, lane, cache=None, **kw: {
            n: (pig.CLAIM_CODE_FREE, "libre") for n in numbers})

    for strict in (False, True):
        verdicts = pig.check_claims([4001, 4002, 4003], "lane",
                                    strict_snapshot=strict)
        assert set(verdicts) == {4001, 4002, 4003}
        assert verdicts[4001][0] == pig.CLAIM_CODE_FREE


def test_strict_est_fail_closed_quand_l_instantane_ne_sert_pas(monkeypatch):
    """Instantane absent => `BLOCKED` partout, donc AUCUN grain servi."""
    _aucun_enfant(monkeypatch)
    monkeypatch.setattr(pig, "_claims_in_process",
                        lambda numbers, lane, cache=None, **kw: None)

    verdicts = pig.check_claims([5001, 5002], "lane", strict_snapshot=True)

    assert set(verdicts) == {5001, 5002}
    for code, human in verdicts.values():
        assert code == pig.CLAIM_CODE_BLOCKED
        assert human == pig.CLAIM_HUMAN_SNAPSHOT_ABSENT


def test_hors_strict_rend_error_quand_la_voie_en_processus_echoue(monkeypatch):
    """Hors STRICT, il n'y a plus de repli : le verdict est muet (`ERROR`).

    C'est la MEME classe que rendait l'echec du transport retire, et
    jamais `FREE` : un grain dont le claim n'a pas ete lu ne doit pas
    pouvoir passer pour libre.
    """
    _aucun_enfant(monkeypatch)
    monkeypatch.setattr(pig, "_build_open_prs_cache_for_belt",
                        lambda lane: None)
    monkeypatch.setattr(pig, "_claims_in_process",
                        lambda numbers, lane, cache=None, **kw: None)

    verdicts = pig.check_claims([6001, 6002], "lane")

    for code, _ in verdicts.values():
        assert code == pig.CLAIM_CODE_ERROR


def test_le_mode_strict_ne_rafraichit_pas_l_instantane(monkeypatch):
    """Le tirage ne complete pas a la volee : l'instantane est lu tel quel.

    Le rafraichissement est la PHASE RESEAU, qui precede le tirage ; la
    lecture du critere « 0 appel gh pendant le tirage » tient donc
    structurellement, pas par-hasard.
    """
    _instantane_faux(monkeypatch, sert=True)

    verdicts = pig._claims_in_process([7001, 7002], "lane", None,
                                      local_only=True)

    assert verdicts is not None
    assert set(verdicts) == {7001, 7002}
    assert verdicts[7001][0] == pig.CLAIM_CODE_FREE


def test_le_mode_strict_refuse_une_fenetre_non_servie(monkeypatch):
    """Instantane qui ne sert pas la fenetre => None (fail-CLOSED)."""
    _instantane_faux(monkeypatch, sert=False)

    assert pig._claims_in_process([8001], "lane", None,
                                  local_only=True) is None
