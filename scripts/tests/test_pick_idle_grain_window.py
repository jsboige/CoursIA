"""#21882 -- la phase claims du tapis tient la fenetre de service complete.

Le transport batch de ``check_claims`` coute ~1,06 s/numero en serie
(mesure du 2026-11-01 : n=48 -> 62,5 s, taux marginal) : a ``--grains 50``
la fenetre de service porte 300 numeros et la phase claims seule durait
plus que le mur du tapis entier -- la lane ne rendait aucun grain. Le fix
est un decoupage en tranches paralleles bornees (``BELT_CLAIMS_WORKERS``,
6 par defaut, 1 = chemin serie d'avant).

Valide par ses FAUX NEGATIFS : le cas qui compte n'est pas « les verdicts
sont rendus » (le chemin serie le faisait deja), c'est « une tranche qui
echoue n'emporte pas les autres » et « le chemin serie reste atteignable »
-- sinon le fix echange un mur de temps contre un defaut de silence, et un
``BELT_CLAIMS_WORKERS=1`` casse le repli operatoire.

Aucun reseau : le subprocess est shunte par ``_run_bounded`` (convention
des tests du tapis, cf. ``test_gh_snapshot_22630.py``).
"""
import argparse
import json
import sys
import threading
import time
import types
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import pick_idle_grain as pig


#: Le seuil de decoupage du module, fige ici : un test qui le lirait depuis
#: le module testerait la constante contre elle-meme.
SLICE_MIN = 24
WORKERS = 6


def _batch_payload(nums, code_of):
    return json.dumps({"results": {str(n): {"code": code_of(n),
                                            "human": "stub"}
                                   for n in nums},
                       "total_wall": 0, "phases": {}})


def _stub_batch(calls, threads, sleep_s=0.05, raise_on=None):
    """Rend un ``_run_bounded`` qui enregistre chaque appel (numeros de la
    tranche, thread) et repond un batch JSON valide. ``raise_on`` leve pour
    toute tranche contenant un numero qui satisfait le predicat."""
    lock = threading.Lock()

    def _fake(cmd, timeout=None, env=None):
        nums = [int(x) for x in cmd[4:]]
        with lock:
            calls.append(nums)
            threads.add(threading.get_ident())
        time.sleep(sleep_s)  # force le recouvrement des tranches
        if raise_on is not None and any(raise_on(n) for n in nums):
            raise RuntimeError("gh down")
        return types.SimpleNamespace(
            returncode=0,
            stdout=_batch_payload(nums, lambda n: "BLOCKED" if n % 10 == 4
                                  else "FREE"),
            stderr="")

    return _fake


def _no_network(monkeypatch):
    monkeypatch.setattr(pig, "_build_open_prs_cache_for_belt",
                        lambda lane: None)
    monkeypatch.setattr(pig, "_pass_snapshot_enabled", lambda: False)


def test_grains_50_la_fenetre_de_service_depasse_70():
    """Le critere de sortie du dispatch : a --grains 50 la fenetre vaut
    300 numeros, pas 70 -- ancrage mecanique de l'objectif."""
    args = argparse.Namespace(grains=50)
    window = pig.belt_service_window(args, 10_000)
    assert window == 300
    assert window > 70


def test_check_claims_decoupe_au_dela_du_seuil(monkeypatch):
    """30 numeros >= SLICE_MIN : WORKERS tranches egales, recouvrement
    reel (plusieurs threads), 30 verdicts dans l'ordre d'entree."""
    _no_network(monkeypatch)
    calls: list[list[int]] = []
    threads: set[int] = set()
    monkeypatch.setattr(pig, "_run_bounded", _stub_batch(calls, threads))
    numbers = list(range(3001, 3031))
    verdicts = pig.check_claims(numbers, "lane")
    assert sorted(len(c) for c in calls) == [5] * WORKERS
    assert len(threads) >= 2, ("les tranches doivent se recouvrir, pas "
                               "s'executer en sequence")
    assert list(verdicts.keys()) == numbers
    assert verdicts[3004][0] == pig.CLAIM_CODE_BLOCKED
    assert verdicts[3001][0] == pig.CLAIM_CODE_FREE


def test_check_claims_serie_en_dessous_du_seuil(monkeypatch):
    """Un petit tirage ne paie pas l'overhead du pool : un seul appel
    batch complet, comportement d'avant #21882."""
    _no_network(monkeypatch)
    calls: list[list[int]] = []
    threads: set[int] = set()
    monkeypatch.setattr(pig, "_run_bounded", _stub_batch(calls, threads))
    verdicts = pig.check_claims([4001, 4002, 4003], "lane")
    assert calls == [[4001, 4002, 4003]]
    assert len(threads) == 1
    assert set(verdicts) == {4001, 4002, 4003}


def test_check_claims_workers_1_force_la_serie(monkeypatch):
    """``BELT_CLAIMS_WORKERS=1`` (repli operatoire) ramene le chemin
    historique : un seul subprocess, meme pour 60 numeros."""
    _no_network(monkeypatch)
    monkeypatch.setattr(pig, "BELT_CLAIMS_WORKERS", 1)
    calls: list[list[int]] = []
    threads: set[int] = set()
    monkeypatch.setattr(pig, "_run_bounded", _stub_batch(calls, threads))
    numbers = list(range(5001, 5061))
    verdicts = pig.check_claims(numbers, "lane")
    assert calls == [numbers]
    assert list(verdicts.keys()) == numbers


def test_fenetre_large_bypass_la_voie_en_processus(monkeypatch):
    """#21882 -- la voie en processus (#22630) hydrate ses payloads en SERIE
    (~1 s/numero) : a l'echelle de la fenetre de service elle dure plus que
    le mur du tapis toute seule (mesure : 295 s pour 300 numeros, mur a
    240 s). Au-dela du seuil, elle est remplacee par les tranches -- meme
    avec l'instantane actif."""
    calls: list[list[int]] = []
    threads: set[int] = set()
    monkeypatch.setattr(pig, "_build_open_prs_cache_for_belt",
                        lambda lane: None)
    monkeypatch.setattr(pig, "_pass_snapshot_enabled", lambda: True)
    monkeypatch.setattr(pig, "_claims_in_process",
                        lambda numbers, lane, cache=None: (
                            {n: (pig.CLAIM_CODE_FREE, "in-process")
                             for n in numbers}))
    monkeypatch.setattr(pig, "_run_bounded", _stub_batch(calls, threads))
    numbers = list(range(8001, 8031))
    verdicts = pig.check_claims(numbers, "lane")
    # La voie en processus N'A PAS servi : ses verdicts marker "in-process"
    # sont absents, ceux des tranches (stub) sont la.
    assert all(h != "in-process" for _, h in verdicts.values())
    assert len(threads) >= 2
    assert list(verdicts.keys()) == numbers


def test_petite_fenetre_garde_la_voie_en_processus(monkeypatch):
    """Sous le seuil, l'instantane actif reste prioritaire (regime rentable
    de la voie #22630) : decouper 3 numeros serait de l'overhead."""
    monkeypatch.setattr(pig, "_build_open_prs_cache_for_belt",
                        lambda lane: None)
    monkeypatch.setattr(pig, "_pass_snapshot_enabled", lambda: True)
    monkeypatch.setattr(pig, "_claims_in_process",
                        lambda numbers, lane, cache=None: (
                            {n: (pig.CLAIM_CODE_FREE, "in-process")
                             for n in numbers}))
    monkeypatch.setattr(pig, "_run_bounded", _stub_batch([], set()))
    verdicts = pig.check_claims([8101, 8102], "lane")
    assert all(h == "in-process" for _, h in verdicts.values())


def test_tranche_en_echec_n_emporte_pas_les_autres(monkeypatch):
    """Un subprocess qui leve rend ERROR pour SA tranche seulement :
    fail-OPEN borne, les autres tranches gardent leurs verdicts. 30
    numeros, 3 workers -> tranches de 10 ; la tranche du milieu (6011)
    est celle qui leve."""
    _no_network(monkeypatch)
    monkeypatch.setattr(pig, "BELT_CLAIMS_WORKERS", 3)
    calls: list[list[int]] = []
    threads: set[int] = set()
    monkeypatch.setattr(pig, "_run_bounded",
                        _stub_batch(calls, threads,
                                    raise_on=lambda n: n == 6014))
    numbers = list(range(6001, 6031))
    verdicts = pig.check_claims(numbers, "lane")
    errors = {n for n, (code, _) in verdicts.items()
              if code == pig.CLAIM_CODE_ERROR}
    assert errors == set(range(6011, 6021)), (
        "seule la tranche fautive est en ERROR, pas ses voisines")
    assert len(verdicts) == len(numbers)
    # Les tranches saines gardent leur verdict du stub : 6004 et 6024
    # (% 10 == 4) sont BLOCKED, les autres FREE.
    assert verdicts[6004][0] == pig.CLAIM_CODE_BLOCKED
    assert verdicts[6001][0] == pig.CLAIM_CODE_FREE


def test_sliced_supporte_un_transport_qui_leve_tout_seul(monkeypatch):
    """Garde externe : meme si ``_check_claims_one_batch`` levait (il ne
    doit pas -- il attrape tout en interne), la tranche est isolee par
    l'appelant et la reunion reste complete et ordonnee."""
    real = pig._check_claims_one_batch

    def _wrapper(numbers, lane, env):
        if 7004 in numbers:
            raise RuntimeError("hors contrat")
        return real(numbers, lane, env)

    monkeypatch.setattr(pig, "_check_claims_one_batch", _wrapper)
    monkeypatch.setattr(pig, "_build_open_prs_cache_for_belt",
                        lambda lane: None)
    monkeypatch.setattr(pig, "_run_bounded",
                        _stub_batch([], set(), sleep_s=0))
    numbers = list(range(7001, 7031))
    verdicts = pig._check_claims_sliced(numbers, "lane", {})
    assert len(verdicts) == len(numbers)
    # WORKERS tranches de 5 : 7001..7005 est la tranche fautive entiere.
    assert {n for n, (c, _) in verdicts.items()
            if c == pig.CLAIM_CODE_ERROR} == set(range(7001, 7006))
    assert list(verdicts.keys()) == numbers
