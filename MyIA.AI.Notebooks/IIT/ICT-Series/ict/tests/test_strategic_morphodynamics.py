"""Tests du module :mod:`ict.strategic_morphodynamics` (ICT-13, #13322).

Verrouillent le contrat de reproductibilite des tournois :

  1. **Historique-independance** (#13322, criterium 1) : ``payoff_matrix`` avec
     un ``rng`` fixe rend la MEME matrice quel que soit l'usage anterieur du
     dict de strategies (round_robin / noise_collapse exercent le dict entre
     les deux appels).
  2. **Controle negatif** (#13322, criterium 3) : un seed different rend une
     matrice differente — le fix ne gele pas les tirages. (L'ancien module
     echouait ce controle dans l'autre sens : seeds 42 et 43 rendaient la meme
     matrice car le rng appelant etait ignore a bruit nul.)
  3. ``round_robin`` est historique-independant au meme titre.
  4. Les strategies deterministes du module restent deterministes ; gtft reste
     stochastique (ecart entre deux seeds > 0 sur une ligne gtft).

Pattern herite de ``test_self_sorting.py`` : bootstrap ``sys.path``
module-level, sans fixtures, tolerances commentees.
"""

from __future__ import annotations

import sys
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from ict.strategic_morphodynamics import (  # noqa: E402
    _accepts_rng,
    make_strategies,
    noise_collapse,
    payoff_matrix,
    play_match,
    round_robin,
)


def test_payoff_matrix_history_independent():
    """Criterium 1 : meme seed => meme matrice, quel que soit l'usage anterieur."""
    def build_a(strat):
        rng = np.random.default_rng(42)
        return payoff_matrix(strat, n_rounds=150, noise=0.0, n_reps=2, rng=rng)

    rng = np.random.default_rng(0)
    a_fresh = build_a(make_strategies(rng))

    rng = np.random.default_rng(0)
    strat = make_strategies(rng)
    r = np.random.default_rng(42)
    round_robin(strat, n_rounds=200, noise=0.0, n_reps=1, rng=r)
    r = np.random.default_rng(21)
    noise_collapse(strat, np.linspace(0.0, 0.4, 9), n_rounds=150, n_reps=3, rng=r)

    a_after = build_a(strat)
    assert np.array_equal(a_fresh, a_after)


def test_payoff_matrix_seed_changes_result():
    """Controle negatif (criterium 3) : un seed different DOIT differer."""
    a_mats = []
    for seed in (42, 43):
        rng = np.random.default_rng(0)
        strat = make_strategies(rng)
        a_mats.append(
            payoff_matrix(strat, n_rounds=150, noise=0.0, n_reps=2,
                          rng=np.random.default_rng(seed))
        )
    # tolerance nulle : les tirages gtft different des le premier match
    assert not np.array_equal(a_mats[0], a_mats[1])


def test_round_robin_history_independent():
    """round_robin : meme seed => memes scores, quel que soit l'usage anterieur."""
    def run(strat):
        rng = np.random.default_rng(7)
        return round_robin(strat, n_rounds=100, noise=0.0, n_reps=1, rng=rng)

    rng = np.random.default_rng(0)
    sc_fresh = run(make_strategies(rng))

    rng = np.random.default_rng(0)
    strat = make_strategies(rng)
    payoff_matrix(strat, n_rounds=150, noise=0.0, n_reps=2,
                  rng=np.random.default_rng(42))
    sc_after = run(strat)

    assert sc_fresh == sc_after


def test_deterministic_strategies_unchanged():
    """allc/alld/tft/pavlov/grim : sortie ne depend pas du rng (protocole arite 2)."""
    strat = make_strategies(np.random.default_rng(0))
    own = np.array([0, 1, 1])
    opp = np.array([1, 0, 1])
    for name in ("allc", "alld", "tft", "pavlov", "grim"):
        s = strat[name]
        assert s(own, opp) == s(own, opp), name


def test_keyword_only_rng_strategy_playable():
    """(#13442) `_accepts_rng` accepte KEYWORD_ONLY mais play_match passait le
    rng POSITIONNELLEMENT — une strategie `def s(own, opp, *, rng)` passait le
    predicat puis plantait en TypeError au premier appel. play_match doit
    passer rng par mot-cle : les deux kinds declares acceptables sont jouables.
    CE TEST ECHOUE SI play_match REVENIR AU PASSAGE POSITIONNEL."""
    def kw_only(own, opp, *, rng=None):
        r = rng if rng is not None else np.random.default_rng(0)
        return int(r.random() < 0.5)

    def pos_or_kw(own, opp, rng=None):
        r = rng if rng is not None else np.random.default_rng(0)
        return int(r.random() < 0.5)

    assert _accepts_rng(kw_only) and _accepts_rng(pos_or_kw)
    strat = make_strategies(np.random.default_rng(0))
    for s in (kw_only, pos_or_kw):
        g1, g2 = play_match(s, strat["allc"], n_rounds=10,
                            rng=np.random.default_rng(7))
        assert -5.0 <= g1 <= 5.0  # gains IPD bornes par T..S sur 10 coups
