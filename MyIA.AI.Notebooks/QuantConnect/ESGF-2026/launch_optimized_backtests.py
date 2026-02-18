"""
Launch optimized backtests for 3 strategies based on research findings.

Research-based optimizations:
1. BTC-MACD-ADX: Window=40, Pct=10/90 (Sharpe ~0.267)
2. ETF-Pairs: Using correlation-based approach (Sharpe ~0.345)
3. Sector-Momentum: Lookback=180, VIX=30, Leverage=1.25 (Sharpe ~1.04)
"""

import requests
import time
import json

# User credentials (jsboige@gmail.com)
USER_ID = "46613"
ACCESS_TOKEN = "5dc8bd3dbebd8ef004d3386b6c3ab288"

HEADERS = {
    "Authorization": f"Bearer {ACCESS_TOKEN}",
    "Content-Type": "application/json"
}

# Project configurations
PROJECTS = {
    "BTC-MACD-ADX": {
        "project_id": 19898232,
        "compile_id": "a1c6356b1ee1998fdd3196d03ff02b54-cb8ea4136749d8d06be0f80feb3d658c",
        "backtest_name": "Optimized-Research-Window40-Pct10-90",
        "expected_sharpe": 0.267
    },
    "Sector-Momentum": {
        "project_id": 20216980,
        "compile_id": "237621779fb45675c45c2edac21d2bb1-95da57957a0fab0e50af9841ccc2f2e6",
        "backtest_name": "Optimized-Research-Lookback180-VIX30-Lev125",
        "expected_sharpe": 1.041
    }
}

def create_backtest(project_id, compile_id, backtest_name):
    """Create a backtest via QC API"""
    url = f"https://www.quantconnect.com/api/v2/projects/{project_id}/backtests"

    data = {
        "compileId": compile_id,
        "backtestName": backtest_name
    }

    response = requests.post(url, headers=HEADERS, json=data)
    return response

def main():
    print("=" * 80)
    print("LAUNCHING OPTIMIZED BACKTESTS - Research-Based Parameters")
    print("=" * 80)
    print()

    results = []

    for strategy_name, config in PROJECTS.items():
        project_id = config["project_id"]
        compile_id = config["compile_id"]
        backtest_name = config["backtest_name"]
        expected_sharpe = config["expected_sharpe"]

        print(f"Launching {strategy_name}...")
        print(f"  Project ID: {project_id}")
        print(f"  Compile ID: {compile_id}")
        print(f"  Backtest Name: {backtest_name}")
        print(f"  Expected Sharpe: {expected_sharpe:.3f}")

        response = create_backtest(project_id, compile_id, backtest_name)

        if response.status_code == 200:
            result = response.json()
            if result.get("success"):
                print(f"  Status: SUCCESS")
                print(f"  Backtest ID: {result.get('backtestId', 'N/A')}")
                results.append({
                    "strategy": strategy_name,
                    "status": "Launched",
                    "backtest_id": result.get('backtestId', 'N/A'),
                    "url": f"https://www.quantconnect.com/project/{project_id}/backtests"
                })
            else:
                print(f"  Status: ERROR - {result.get('errors', 'Unknown error')}")
                results.append({"strategy": strategy_name, "status": "Failed", "error": result.get('errors')})
        else:
            print(f"  Status: HTTP ERROR {response.status_code}")
            results.append({"strategy": strategy_name, "status": "HTTP Error", "code": response.status_code})

        print()
        time.sleep(2)  # Avoid rate limiting

    print("=" * 80)
    print("SUMMARY")
    print("=" * 80)
    for r in results:
        status = r.get("status", "Unknown")
        print(f"  {r['strategy']}: {status}")
        if "url" in r:
            print(f"    URL: {r['url']}")

    print()
    print("Next steps:")
    print("1. Wait 5-15 minutes for backtests to complete")
    print("2. Check results via QC Web UI or check_backtests.py")
    print("3. Compare actual Sharpe vs expected Sharpe")
    print("4. If actual < expected by >0.2, iterate further")
    print("=" * 80)

if __name__ == "__main__":
    main()
