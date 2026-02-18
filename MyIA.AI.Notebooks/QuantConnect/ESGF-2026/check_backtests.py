#!/usr/bin/env python3
"""
Script de surveillance des backtests QuantConnect.

Usage: python check_backtests.py

Vérifie périodiquement le statut des 3 backtests lancés:
- BTC-MACD-ADX (19898232)
- ETF-Pairs (19865767)
- Sector-Momentum (20216980)
"""

import requests
import json
import time
from datetime import datetime

ACCESS_TOKEN = '5dc8bd3dbebd8ef004d3386b6c3ab288'
HEADERS = {'Authorization': f'Bearer {ACCESS_TOKEN}'}

STRATEGIES = [
    (19898232, 'BTC-MACD-ADX'),
    (19865767, 'ETF-Pairs'),
    (20216980, 'Sector-Momentum')
]

def check_backtests():
    """Check status of all 3 backtests"""
    print("=" * 80)
    print(f"BACKTEST STATUS CHECK - {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    print("=" * 80)
    print()

    for project_id, name in STRATEGIES:
        url = f'https://www.quantconnect.com/api/v2/projects/{project_id}/backtests'

        try:
            resp = requests.get(url, headers=HEADERS)
            if resp.status_code == 200:
                data = resp.json()
                backtests = data.get('backtests', [])

                if backtests:
                    latest = backtests[0]
                    bt_id = latest.get('backtestId', 'N/A')
                    bt_name = latest.get('name', 'N/A')
                    bt_status = latest.get('status', 'Unknown')
                    bt_completed = latest.get('completed', 'N/A')

                    print(f"📊 {name} (Project {project_id})")
                    print(f"   Nom: {bt_name}")
                    print(f"   Status: {bt_status}")

                    if bt_completed and bt_completed != 'N/A':
                        print(f"   Completed: {bt_completed}")

                        # Try to get performance if completed
                        if bt_status == 'Completed':
                            perf = latest.get('performance', {})
                            if perf:
                                sharpe = perf.get('sharpeRatio', 'N/A')
                                total_return = perf.get('totalReturn', 'N/A')
                                max_dd = perf.get('drawdown', 'N/A')
                                print(f"   Sharpe: {sharpe}")
                                print(f"   Return: {total_return}")
                                print(f"   Max DD: {max_dd}")

                    print(f"   URL: https://www.quantconnect.com/project/{project_id}/backtest/{bt_id[:16]}")
                else:
                    print(f"⚠️  {name}: No backtests found")
            else:
                print(f"❌ {name}: API Error {resp.status_code}")
        except Exception as e:
            print(f"❌ {name}: {e}")

        print()

def main():
    """Monitor backtests every 60 seconds"""
    print("🚀 Starting backtest monitoring...")
    print("Press Ctrl+C to stop\n")

    try:
        check_backtests()

        print("\n⏳ Monitoring every 60 seconds...")
        while True:
            time.sleep(60)
            print()
            check_backtests()
    except KeyboardInterrupt:
        print("\n\n👋 Monitoring stopped.")

if __name__ == "__main__":
    main()
