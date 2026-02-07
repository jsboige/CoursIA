"""
QuantConnect AI Trading Series - Shared Python Libraries

Ce package contient les utilitaires partagés pour tous les notebooks Python.

Modules:
    - features: Feature engineering pour ML
    - indicators: Indicateurs techniques personnalisés
    - ml_utils: Utilitaires ML (training, persistence, metrics)
    - plotting: Visualisations standardisées
    - backtest_helpers: Helpers pour configuration backtests

Usage:
    from shared.features import calculate_returns, add_technical_features
    from shared.ml_utils import train_classifier, save_to_objectstore
    from shared.plotting import plot_backtest_results
"""

__version__ = "1.0.0"
__author__ = "CoursIA - QuantConnect AI Trading Series"

# Imports de convenance
try:
    from . import features
    from . import indicators
    from . import ml_utils
    from . import plotting
    from . import backtest_helpers
except ImportError:
    # Modules pas encore créés, ignore silencieusement
    pass

__all__ = [
    'features',
    'indicators',
    'ml_utils',
    'plotting',
    'backtest_helpers'
]
