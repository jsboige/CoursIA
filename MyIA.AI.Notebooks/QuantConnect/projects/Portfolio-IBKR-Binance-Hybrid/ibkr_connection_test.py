"""
IBKR Connection Test via IB Gateway
====================================
Prerequisites:
1. IB Gateway installed and running (or TWS)
2. IB Gateway configured: Edit > Global Configuration > API > Settings
   - Enable ActiveX and Socket Clients = YES
   - Socket port: 4002 (paper) or 4001 (live) for IB Gateway
   - Allow connections from: 127.0.0.1
3. 2FA device available for first login

Usage:
    python ibkr_connection_test.py [--paper] [--live]
"""
import os
import sys
import argparse
from pathlib import Path

try:
    from dotenv import load_dotenv
except ImportError:
    print("Installing python-dotenv...")
    os.system(f"{sys.executable} -m pip install python-dotenv")
    from dotenv import load_dotenv

try:
    from ib_insync import IB, util
except ImportError:
    print("ERROR: ib_insync not installed. Run: pip install ib_insync")
    sys.exit(1)


def load_credentials():
    """Load IBKR credentials from .env file."""
    env_path = Path(__file__).parent / ".env"
    if not env_path.exists():
        print(f"ERROR: .env file not found at {env_path}")
        print("Create it from .env.template with your IBKR credentials")
        sys.exit(1)

    load_dotenv(env_path)
    username = os.getenv("IBKR_USERNAME", "")
    password = os.getenv("IBKR_PASSWORD", "")

    if not username or not password:
        print("ERROR: IBKR_USERNAME or IBKR_PASSWORD not set in .env")
        sys.exit(1)

    return username, password


def test_connection(host="127.0.0.1", port=4002, client_id=1):
    """Test connection to IB Gateway."""
    print(f"Connecting to IB Gateway at {host}:{port} (clientId={client_id})...")
    ib = IB()

    try:
        ib.connect(host, port, clientId=client_id)
        print(f"SUCCESS: Connected to IB Gateway!")
        print(f"  Server version: {ib.client.serverVersion()}")
        conn_time = getattr(ib.client, 'connTime', None)
        if conn_time and callable(conn_time):
            print(f"  Connection time: {conn_time()}")

        # Test: request account summary
        print("\nRequesting account summary...")
        summary = ib.accountSummary()
        if summary:
            print(f"  Account data received: {len(summary)} items")
            for item in summary[:5]:
                print(f"    {item.tag}: {item.value} {item.currency}")
        else:
            print("  No account summary (may need to log in first via IB Gateway UI)")

        # Test: request some market data
        print("\nTesting market data request (SPY)...")
        from ib_insync import Stock
        spy = Stock("SPY", "SMART", "USD")
        ib.qualifyContracts(spy)
        ticker = ib.reqMktData(spy, "", True, False)
        ib.sleep(2)
        print(f"  SPY last price: {ticker.last}")
        print(f"  SPY bid/ask: {ticker.bid} / {ticker.ask}")

        ib.disconnect()
        print("\nConnection test PASSED!")
        return True

    except Exception as e:
        print(f"\nCONNECTION FAILED: {e}")
        print("\nTroubleshooting:")
        print("  1. Is IB Gateway running? Check system tray.")
        print("  2. Is API enabled? Edit > Global Configuration > API > Settings")
        print("  3. Is the correct port? Paper=4002, Live=4001 (IB Gateway)")
        print("  4. Did you complete the 2FA on first login?")
        print("  5. Firewall blocking? Allow port 4002/4001.")
        return False


def main():
    parser = argparse.ArgumentParser(description="IBKR Connection Test")
    parser.add_argument("--paper", action="store_true", default=True, help="Paper trading (default)")
    parser.add_argument("--live", action="store_true", help="Live trading")
    parser.add_argument("--host", default="127.0.0.1", help="IB Gateway host")
    parser.add_argument("--port", type=int, default=None, help="Override port")
    parser.add_argument("--client-id", type=int, default=1, help="Client ID")
    args = parser.parse_args()

    if args.port:
        port = args.port
    elif args.live:
        port = 4001
    else:
        port = 4002

    print("=" * 50)
    print("IBKR Connection Test")
    print("=" * 50)
    print(f"Mode: {'LIVE' if args.live else 'PAPER'}")
    print(f"Target: {args.host}:{port}")
    print()

    # Load credentials for reference
    username, _ = load_credentials()
    print(f"IBKR user: {username}")
    print()

    success = test_connection(args.host, port, args.client_id)
    sys.exit(0 if success else 1)


if __name__ == "__main__":
    main()
