"""
Ouvre les pages de backtest QuantConnect dans le navigateur.

Usage: python open_backtests.py
"""

import webbrowser

# URLs des 3 backtests lancés
BACKTEST_URLS = {
    'BTC-MACD-ADX (Optimized Window80/Pct5-85)': 'https://www.quantconnect.com/project/19898232/backtests',
    'ETF-Pairs (Optimized Half-Life Filter)': 'https://www.quantconnect.com/project/19865767/backtests',
    'Sector-Momentum (Optimized VIX Filter)': 'https://www.quantconnect.com/project/20216980/backtests'
}

print("🚀 Ouverture des pages de backtest QuantConnect...")
print()

for name, url in BACKTEST_URLS.items():
    print(f"📊 {name}")
    print(f"   {url}")
    webbrowser.open(url)
    print()

print("✅ Pages ouvertes dans votre navigateur par défaut")
print()
print("Instructions:")
print("1. Attendre que les backtests terminent (5-15 min chacun)")
print("2. Chercher 'Optimized' dans la liste des backtests")
print("3. Cliquer sur le backtest pour voir les résultats")
print("4. Noter: Sharpe Ratio, Total Return, Max Drawdown")
print()
print("Ou lancer: python check_backtests.py (surveillance auto)")
