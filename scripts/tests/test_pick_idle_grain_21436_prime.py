"""#21436 -- le priming de l'instantane respecte le mur de temps du tapis.

Defaut mesure (po-2023, 30/10/2026, quatre executions consecutives) : la phase
``pick_with_replacements start`` s'ouvrait a t=35 s en annoncant « 205 s
restants », puis plus aucune ligne ; le run etait tue a 240 s sans avoir servi
un seul grain. Cause : ``prime(...)`` -- un ``gh api`` par issue de tete, en
serie -- s'executait AVANT que ``deadline`` ne soit installe, donc le budget
etait calcule puis ignore.

Ces tests verrouillent les trois comportements du correctif, sans reseau :

1. **sans budget** (``time_budget_s=None``), le priming est inchange : un seul
   appel, toute la fenetre de service, aucune troncature rapportee ;
2. **mur deja tombe** (``time_budget_s=0``), le priming n'emet AUCUN appel et
   la troncature est **rapportee** (``prime_truncated``), pas tu ;
3. **budget confortable**, le priming avance par tranches mais va au bout :
   la cle ``prime_truncated`` est **absente** -- un ``0`` et une cle absente ne
   disent pas la meme chose.
"""

import types

import pytest

import pick_idle_grain as pig

LANE = "myia-po-2023:CoursIA"


def _args(grains=2):
    """Args minimum lus par la boucle du tapis (cf #19390)."""
    return types.SimpleNamespace(grains=grains, include_delivered=True,
                                 lane=LANE)


def _make_item(number):
    return {
        "number": number,
        "klass": "grain",
        "age": 10,
        "idle": 10,
        "genre": "docs",
        "labels": [],
        "title": f"issue #{number}",
        "created_at": "2026-08-01T00:00:00Z",
        "last_delivery_stamp": None,
    }


def _free_claims(items):
    return {it["number"]: (pig.CLAIM_CODE_FREE, "libre") for it in items}


class _PrimeRecorder:
    """Sonde de priming qui enregistre les numeros recus, par appel."""

    def __init__(self):
        self.calls = []

    def __call__(self, repo, numbers):
        self.calls.append(list(numbers))

    @property
    def flat(self):
        return [n for call in self.calls for n in call]


def _run(pool, prime, time_budget_s):
    return pig.belt_pick_with_replacements(
        pool, _free_claims(pool), _args(), probe_budget=8,
        snapshot_prime=prime, time_budget_s=time_budget_s)


def test_sans_budget_le_priming_reste_dun_seul_appel():
    """``time_budget_s=None`` = comportement d'avant le correctif."""
    pool = [_make_item(1000 + i) for i in range(20)]
    prime = _PrimeRecorder()

    _picks, _withheld, state = _run(pool, prime, None)

    assert len(prime.calls) == 1, "sans mur, le priming ne se decoupe pas"
    assert prime.flat == [1000 + i for i in range(20)]
    assert "prime_truncated" not in state


def test_mur_deja_tombe_ne_prime_rien_et_rapporte_la_troncature():
    """Budget nul : aucun appel reseau, et la troncature est comptee."""
    pool = [_make_item(2000 + i) for i in range(20)]
    prime = _PrimeRecorder()

    _picks, _withheld, state = _run(pool, prime, 0.0)

    assert prime.calls == [], "le mur tombe avant le premier appel"
    assert state["prime_truncated"] == 20
    # NB : `time_budget_hit` n'est PAS affirme ici. Il se pose quand la boucle
    # atteint une surface couteuse (`counted_probe`, verif de claim hors
    # fenetre). Ce pool a ses claims pre-resolus et `include_delivered=True`,
    # donc la boucle ne lit jamais `expired()` : le drapeau resterait False
    # sans que le mur soit en cause. La troncature du priming, elle, est
    # directement observable et c'est ce que ce test verrouille.


def test_budget_confortable_prime_par_tranches_jusquau_bout():
    """Le decoupage ne doit pas devenir une troncature silencieuse."""
    pool = [_make_item(3000 + i) for i in range(20)]
    prime = _PrimeRecorder()

    _picks, _withheld, state = _run(pool, prime, 600.0)

    assert prime.flat == [3000 + i for i in range(20)]
    assert len(prime.calls) > 1, "l'avance se fait par tranches"
    assert "prime_truncated" not in state


def test_le_priming_ne_consomme_pas_tout_le_budget(monkeypatch):
    """Le priming est borne a la MOITIE du reste : la boucle garde de quoi servir.

    Une horloge pilotee fait avancer le temps a chaque tranche : le priming
    doit s'arreter a sa propre echeance et laisser le mur principal intact.
    """
    pool = [_make_item(4000 + i) for i in range(70)]
    prime = _PrimeRecorder()

    clock = {"t": 1000.0}

    def fake_monotonic():
        return clock["t"]

    class _TickPrime(_PrimeRecorder):
        def __call__(self, repo, numbers):
            super().__call__(repo, numbers)
            clock["t"] += 10.0  # chaque tranche coute 10 s simulees

    tick_prime = _TickPrime()
    monkeypatch.setattr(pig.time, "monotonic", fake_monotonic)

    # Budget de 100 s : moitie = 50 s, soit 5 tranches de 8 = 40 issues.
    _picks, _withheld, state = _run(pool, tick_prime, 100.0)

    # #22983 -- la fenetre du priming n'est plus « les 70 positions de
    # tete » en dur : c'est la fenetre que la boucle de service va
    # parcourir (`belt_service_window`), donc la troncature se compte sur
    # CETTE fenetre. Le mur, lui, reste borne a la moitie du reste.
    window = pig.belt_service_window(_args(), len(pool))
    assert state["prime_truncated"] == window - len(tick_prime.flat)
    assert state["prime_truncated"] > 0, "le priming doit s'arreter avant la fenetre"
    assert clock["t"] < 1000.0 + 100.0, "le priming ne mange pas le mur"


if __name__ == "__main__":
    raise SystemExit(pytest.main([__file__, "-q"]))
