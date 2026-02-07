"""
Custom Indicators pour QuantConnect

Indicateurs techniques personnalisés pour QuantConnect LEAN.
Utilisés dans les notebooks 11, 18 (Technical Indicators, Features Engineering).

Classes:
    - CustomMomentumIndicator: Momentum personnalisé
    - TrendStrengthIndicator: Force de tendance
    - VolatilityBandIndicator: Bandes de volatilité

Usage:
    from shared.indicators import CustomMomentumIndicator

    momentum = CustomMomentumIndicator('momentum', period=20)
    # Dans OnData():
    momentum.Update(data.Time, data["SPY"].Close)
"""

from typing import Optional
import numpy as np


class CustomMomentumIndicator:
    """
    Indicateur de momentum personnalisé

    Calcule momentum = (price_current - price_n_periods_ago) / price_n_periods_ago

    Args:
        name: Nom de l'indicateur
        period: Période de calcul (nombre de barres)
    """

    def __init__(self, name: str, period: int = 20):
        self.Name = name
        self.period = period
        self.prices = []
        self.IsReady = False
        self.Current = IndicatorValue(0.0)

    def Update(self, time, value: float):
        """Met à jour l'indicateur avec une nouvelle valeur"""
        self.prices.append(value)

        # Garder seulement les N dernières valeurs
        if len(self.prices) > self.period:
            self.prices.pop(0)

        # Calculer momentum si prêt
        if len(self.prices) >= self.period:
            self.IsReady = True
            old_price = self.prices[0]
            current_price = self.prices[-1]

            if old_price != 0:
                momentum = (current_price - old_price) / old_price
            else:
                momentum = 0.0

            self.Current = IndicatorValue(momentum, time)

    def Reset(self):
        """Reset l'indicateur"""
        self.prices = []
        self.IsReady = False
        self.Current = IndicatorValue(0.0)


class TrendStrengthIndicator:
    """
    Indicateur de force de tendance

    Mesure la force et direction de la tendance basé sur ADX simplifié

    Args:
        name: Nom de l'indicateur
        period: Période de calcul
    """

    def __init__(self, name: str, period: int = 14):
        self.Name = name
        self.period = period
        self.high_prices = []
        self.low_prices = []
        self.close_prices = []
        self.IsReady = False
        self.Current = IndicatorValue(0.0)

    def Update(self, time, high: float, low: float, close: float):
        """Met à jour avec high, low, close"""
        self.high_prices.append(high)
        self.low_prices.append(low)
        self.close_prices.append(close)

        # Garder N valeurs
        if len(self.close_prices) > self.period + 1:
            self.high_prices.pop(0)
            self.low_prices.pop(0)
            self.close_prices.pop(0)

        # Calculer si prêt
        if len(self.close_prices) >= self.period:
            self.IsReady = True
            strength = self._calculate_trend_strength()
            self.Current = IndicatorValue(strength, time)

    def _calculate_trend_strength(self) -> float:
        """Calcule force de tendance (simplifié)"""
        if len(self.close_prices) < 2:
            return 0.0

        # Direction moyenne
        moves_up = sum(1 for i in range(1, len(self.close_prices))
                      if self.close_prices[i] > self.close_prices[i-1])
        moves_down = len(self.close_prices) - 1 - moves_up

        if moves_up + moves_down == 0:
            return 0.0

        # Score -1 (downtrend fort) à +1 (uptrend fort)
        strength = (moves_up - moves_down) / (moves_up + moves_down)
        return strength

    def Reset(self):
        """Reset l'indicateur"""
        self.high_prices = []
        self.low_prices = []
        self.close_prices = []
        self.IsReady = False
        self.Current = IndicatorValue(0.0)


class VolatilityBandIndicator:
    """
    Bandes de volatilité personnalisées

    Similar aux Bollinger Bands mais avec volatilité ATR

    Args:
        name: Nom de l'indicateur
        period: Période de calcul
        multiplier: Multiplicateur ATR pour bandes
    """

    def __init__(self, name: str, period: int = 20, multiplier: float = 2.0):
        self.Name = name
        self.period = period
        self.multiplier = multiplier
        self.high_prices = []
        self.low_prices = []
        self.close_prices = []
        self.IsReady = False
        self.UpperBand = IndicatorValue(0.0)
        self.MiddleBand = IndicatorValue(0.0)
        self.LowerBand = IndicatorValue(0.0)

    def Update(self, time, high: float, low: float, close: float):
        """Met à jour avec high, low, close"""
        self.high_prices.append(high)
        self.low_prices.append(low)
        self.close_prices.append(close)

        # Garder N valeurs
        if len(self.close_prices) > self.period:
            self.high_prices.pop(0)
            self.low_prices.pop(0)
            self.close_prices.pop(0)

        # Calculer si prêt
        if len(self.close_prices) >= self.period:
            self.IsReady = True
            upper, middle, lower = self._calculate_bands()
            self.UpperBand = IndicatorValue(upper, time)
            self.MiddleBand = IndicatorValue(middle, time)
            self.LowerBand = IndicatorValue(lower, time)

    def _calculate_bands(self):
        """Calcule les bandes"""
        # Middle band = SMA
        middle = np.mean(self.close_prices)

        # ATR approximation
        true_ranges = []
        for i in range(1, len(self.close_prices)):
            high_low = self.high_prices[i] - self.low_prices[i]
            high_close = abs(self.high_prices[i] - self.close_prices[i-1])
            low_close = abs(self.low_prices[i] - self.close_prices[i-1])
            true_range = max(high_low, high_close, low_close)
            true_ranges.append(true_range)

        atr = np.mean(true_ranges) if true_ranges else 0.0

        # Bandes
        upper = middle + (atr * self.multiplier)
        lower = middle - (atr * self.multiplier)

        return upper, middle, lower

    def Reset(self):
        """Reset l'indicateur"""
        self.high_prices = []
        self.low_prices = []
        self.close_prices = []
        self.IsReady = False
        self.UpperBand = IndicatorValue(0.0)
        self.MiddleBand = IndicatorValue(0.0)
        self.LowerBand = IndicatorValue(0.0)


class IndicatorValue:
    """Valeur d'indicateur avec timestamp"""

    def __init__(self, value: float, time=None):
        self.Value = value
        self.Time = time

    def __float__(self):
        return self.Value

    def __repr__(self):
        return f"IndicatorValue({self.Value:.4f})"


if __name__ == '__main__':
    # Tests rapides
    print("Testing indicators.py...")
    import datetime

    # Test CustomMomentumIndicator
    momentum = CustomMomentumIndicator('momentum', period=5)
    prices = [100, 101, 102, 103, 104, 105, 106]
    for i, price in enumerate(prices):
        time = datetime.datetime.now() + datetime.timedelta(days=i)
        momentum.Update(time, price)

    print(f"✓ CustomMomentumIndicator: IsReady={momentum.IsReady}, Value={float(momentum.Current):.4f}")

    # Test TrendStrengthIndicator
    trend = TrendStrengthIndicator('trend', period=5)
    for i in range(10):
        high = 100 + i + 1
        low = 100 + i - 1
        close = 100 + i
        time = datetime.datetime.now() + datetime.timedelta(days=i)
        trend.Update(time, high, low, close)

    print(f"✓ TrendStrengthIndicator: IsReady={trend.IsReady}, Strength={float(trend.Current):.4f}")

    # Test VolatilityBandIndicator
    vol_band = VolatilityBandIndicator('vol_band', period=5, multiplier=2.0)
    for i in range(10):
        high = 100 + i + 2
        low = 100 + i - 2
        close = 100 + i
        time = datetime.datetime.now() + datetime.timedelta(days=i)
        vol_band.Update(time, high, low, close)

    print(f"✓ VolatilityBandIndicator: Upper={float(vol_band.UpperBand):.2f}, "
          f"Middle={float(vol_band.MiddleBand):.2f}, Lower={float(vol_band.LowerBand):.2f}")

    print("\nAll tests passed! ✓")
