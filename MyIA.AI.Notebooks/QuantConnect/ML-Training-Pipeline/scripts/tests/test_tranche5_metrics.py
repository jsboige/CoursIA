"""Tranche 5 (#19016) : validate_xrp_dt.sharpe delegue a strategy_metrics ;

ecarts de baselines.sharpe_from_returns (ddof dependant du conteneur) et de
m11i._max_drawdown_pct (espace log) documentes et pinnes.

La serie de controle est celle du body de la PR : rng(42), 500 rendements
quotidiens ~ N(5e-4, 1e-2). validate_xrp_dt importe torch (chaine
train_rl_dt) : sa classe passe par ``pytest.importorskip`` -- elle tourne sur
les workers GPU, pas dans la CI sans torch (meme contrainte que
test_validate_xrp_dt_foldwise.py, docstring « CPU-only, no torch import »).
"""

import sys
from pathlib import Path

import numpy as np
import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

import strategy_metrics  # noqa: E402
from baselines import sharpe_from_returns  # noqa: E402
from m11i_max_dd_analysis import _max_drawdown_pct  # noqa: E402


def _control_series() -> np.ndarray:
    rng = np.random.default_rng(42)
    return rng.normal(5e-4, 1e-2, 500)


def _old_epsilon_sharpe(returns: np.ndarray, periods: int = 252) -> float:
    """Formule d'avant la tranche 5 : denominateur ``sd + 1e-12``."""
    if len(returns) < 2:
        return 0.0
    mu = float(np.mean(returns))
    sd = float(np.std(returns, ddof=1)) + 1e-12
    return mu / sd * np.sqrt(periods)


class TestXrpSharpeDelegation:
    """validate_xrp_dt.sharpe : garde locale, formule de l'organe."""

    def test_matches_organ_formula_on_control_series(self):
        torch = pytest.importorskip("torch")  # noqa: F841
        from validate_xrp_dt import sharpe

        r = _control_series()
        expected = float(np.mean(r) / np.std(r, ddof=1) * np.sqrt(252))
        assert sharpe(r) == pytest.approx(expected, rel=1e-12)
        assert sharpe(r) == pytest.approx(
            float(strategy_metrics.sharpe(r, periods_per_year=252)), rel=1e-15
        )

    def test_epsilon_removal_bound_on_control_series(self):
        torch = pytest.importorskip("torch")  # noqa: F841
        from validate_xrp_dt import sharpe

        r = _control_series()
        new = sharpe(r)
        old = _old_epsilon_sharpe(r)
        sd = float(np.std(r, ddof=1))
        # L'epsilon additif d'avant la tranche 5 etait negligeable pour un
        # ecart-type reel : l'ecart relatif est de l'ordre de 1e-12 / sd
        # (marge 1.05 pour l'arrondi flottant des deux chemins de calcul).
        assert abs(old - new) / abs(new) <= 1.05 * (1e-12 / sd)

    def test_periods_passthrough(self):
        torch = pytest.importorskip("torch")  # noqa: F841
        from validate_xrp_dt import sharpe

        r = _control_series()
        assert sharpe(r, periods=365) == pytest.approx(
            sharpe(r) * np.sqrt(365.0 / 252.0), rel=1e-12
        )

    def test_short_series_returns_zero(self):
        torch = pytest.importorskip("torch")  # noqa: F841
        from validate_xrp_dt import sharpe

        assert sharpe(np.array([])) == 0.0
        assert sharpe(np.array([0.01])) == 0.0

    def test_constant_series_named_change(self):
        """Ecart nomme de la tranche 5 : serie constante non nulle.

        Avant : epsilon additif -> valeur finie enorme (mu / 1e-12).
        Apres : convention de l'organe -> inf (Sharpe non defini, pas 0.0).
        """
        torch = pytest.importorskip("torch")  # noqa: F841
        from validate_xrp_dt import sharpe

        r = np.full(50, 0.01)
        assert np.isinf(sharpe(r))
        assert _old_epsilon_sharpe(r) > 1e10  # l'ancienne valeur finie etait enorme


class TestBaselinesEcartPinned:
    """Defaut connu, nomme par #19016, pinne en attendant le grain de suivi.

    sharpe_from_returns ne delegue pas : son ddof depend du conteneur. Ces
    tests pinnent le comportement ACTUEL pour que le rejeu du grain
    d'harmonisation ait un avant/apres nomme.
    """

    def test_container_ddof_divergence(self):
        import pandas as pd

        r = _control_series()
        v_series = sharpe_from_returns(pd.Series(r))  # .std() -> ddof=1
        v_array = sharpe_from_returns(np.asarray(r, dtype=float))  # .std() -> ddof=0
        n = len(r)
        # Le meme rendement, deux Sharpe selon le conteneur : le chemin
        # ndarray (ddof=0) sous-estime l'ecart-type, donc SURestime le Sharpe.
        assert v_series != v_array
        assert v_array / v_series == pytest.approx(np.sqrt(n / (n - 1)), rel=1e-9)

    def test_series_path_matches_organ(self):
        """Le chemin pd.Series est deja ddof=1 : il coincide avec l'organe."""
        import pandas as pd

        r = _control_series()
        expected = float(strategy_metrics.sharpe(r))
        assert sharpe_from_returns(pd.Series(r)) == pytest.approx(expected, rel=1e-12)

    def test_zero_std_returns_zero_not_inf(self):
        r = np.full(50, 0.01)
        assert sharpe_from_returns(r) == 0.0

    def test_empty_returns_zero(self):
        assert sharpe_from_returns(np.array([])) == 0.0


class TestM11iEcartPinned:
    """_max_drawdown_pct : espace log, fraction positive -- equivalence nommee."""

    def test_log_space_equivalence_with_organ(self):
        rng = np.random.default_rng(7)
        log_returns = rng.normal(2e-4, 1e-2, 300)
        pct = _max_drawdown_pct(log_returns)
        organ = -strategy_metrics.max_drawdown(np.exp(log_returns) - 1.0)
        assert pct == pytest.approx(organ, rel=1e-12, abs=1e-15)

    def test_positive_fraction(self):
        rng = np.random.default_rng(7)
        log_returns = rng.normal(-1e-4, 2e-2, 300)
        assert _max_drawdown_pct(log_returns) >= 0.0
