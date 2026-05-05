"""Execute QuantBook notebooks locally with yfinance-backed mock.

Provides a MockQB that returns real market data via yfinance,
then executes notebook cells capturing real outputs.
"""
import json
import sys
import traceback
import base64
from io import StringIO, BytesIO
from pathlib import Path


def get_spy_history(tickers, period_days=252):
    """Get real historical data via yfinance."""
    import yfinance as yf
    import pandas as pd
    import numpy as np

    data = {}
    for ticker in tickers:
        t = yf.Ticker(ticker)
        hist = t.history(period=f"{period_days}d")
        if hist.empty:
            continue
        # Rename columns to match QC format (lowercase)
        hist.columns = [c.lower() for c in hist.columns]
        hist.index.name = None
        data[ticker] = hist

    if not data:
        return pd.DataFrame()

    # Create multi-index DataFrame like QC returns
    frames = []
    for ticker, df in data.items():
        df = df.copy()
        df['symbol'] = ticker
        frames.append(df)

    result = pd.concat(frames)
    result = result.set_index(['symbol', result.index])
    result.index.names = [None, None]
    return result


def create_mock_qb(history_df):
    """Create a MockQB object that mimics QuantBook for local execution."""
    import pandas as pd
    import numpy as np

    class MockSymbol:
        def __init__(self, value):
            self.Value = value
        def __str__(self):
            return self.Value
        def __repr__(self):
            return self.Value

    class MockSecurity:
        def __init__(self, symbol):
            self.symbol = symbol
            self.Symbol = MockSymbol(symbol)

    class MockSecurities:
        def __init__(self):
            self._securities = {}

        def add(self, symbol):
            self._securities[symbol] = MockSecurity(symbol)

        @property
        def Keys(self):
            return list(self._securities.keys())

        def __iter__(self):
            return iter(self._securities.values())

        def __len__(self):
            return len(self._securities)

    class MockQB:
        def __init__(self):
            self._securities = MockSecurities()
            self._history_df = history_df

        def AddEquity(self, symbol, resolution=None):
            self._securities.add(symbol)
            return MockSecurity(symbol)

        def AddCrypto(self, *args, **kwargs):
            return None

        def History(self, *args, **kwargs):
            if self._history_df is not None and not self._history_df.empty:
                return self._history_df.copy()
            return pd.DataFrame()

        @property
        def Securities(self):
            return self._securities

    return MockQB()


def execute_notebook(notebook_path, output_path=None, period_days=252):
    """Execute a QuantBook notebook locally with mock data."""
    import pandas as pd
    import numpy as np
    import matplotlib
    matplotlib.use('Agg')  # Non-interactive backend
    import matplotlib.pyplot as plt
    from enum import Enum
    from typing import Dict, List, Tuple, Optional

    nb = json.load(open(notebook_path, 'r', encoding='utf-8'))

    # Clear existing outputs
    for c in nb['cells']:
        if c['cell_type'] == 'code':
            c['outputs'] = []
            c['execution_count'] = None

    # Get real market data
    print("Fetching market data via yfinance...")
    tickers = ['SPY', 'AAPL']
    history_df = get_spy_history(tickers, period_days)
    print(f"  Got {len(history_df)} rows of data")

    # Create mock
    qb = create_mock_qb(history_df)

    # Mock Resolution enum
    class Resolution(Enum):
        Tick = 0
        Second = 1
        Minute = 2
        Hour = 3
        Daily = 4
        DAILY = 4

    # Mock QCAlgorithm base class (for cells defining algo classes)
    class QCAlgorithm:
        pass

    # Mock PythonData (for custom data classes)
    class PythonData:
        pass

    # Mock QC framework base classes
    class PythonIndicator:
        pass

    class AlphaModel:
        pass

    class PortfolioConstructionModel:
        pass

    class ExecutionModel:
        pass

    class RiskManagementModel:
        pass

    # Pre-extract df_spy for cells that reference it
    df_spy = history_df.loc["SPY"] if "SPY" in history_df.index.get_level_values(0) else pd.DataFrame()
    df_aapl = history_df.loc["AAPL"] if "AAPL" in history_df.index.get_level_values(0) else pd.DataFrame()

    # Stubs for shared/features.py functions
    def calculate_returns(series, periods=[1, 5, 20]):
        result = pd.DataFrame(index=series.index)
        for p in periods:
            result[f'return_{p}d'] = series.pct_change(p)
        return result

    def add_technical_features(df, indicators=None):
        result = df.copy()
        if indicators is None:
            indicators = {}
        sma_periods = indicators.get('sma', [])
        for p in sma_periods:
            result[f'sma_{p}'] = result['close'].rolling(p).mean()
        ema_periods = indicators.get('ema', [])
        for p in ema_periods:
            result[f'ema_{p}'] = result['close'].ewm(span=p).mean()
        rsi_period = indicators.get('rsi')
        if rsi_period:
            delta = result['close'].diff()
            gain = delta.clip(lower=0).rolling(rsi_period).mean()
            loss = (-delta.clip(upper=0)).rolling(rsi_period).mean()
            rs = gain / loss.replace(0, np.nan)
            result[f'rsi_{rsi_period}'] = 100 - (100 / (1 + rs))
        macd_params = indicators.get('macd')
        if macd_params:
            fast, slow, signal = macd_params
            ema_fast = result['close'].ewm(span=fast).mean()
            ema_slow = result['close'].ewm(span=slow).mean()
            result['macd'] = ema_fast - ema_slow
            result['macd_signal'] = result['macd'].ewm(span=signal).mean()
            result['macd_hist'] = result['macd'] - result['macd_signal']
        bb_params = indicators.get('bb')
        if bb_params:
            p, std_mult = bb_params[0], bb_params[1] if len(bb_params) > 1 else 2
            sma = result['close'].rolling(p).mean()
            std = result['close'].rolling(p).std()
            result['bb_upper'] = sma + std_mult * std
            result['bb_lower'] = sma - std_mult * std
        return result

    def calculate_metrics(equity_curve, benchmark=None):
        returns = equity_curve.pct_change().dropna()
        metrics = {
            'total_return': (equity_curve.iloc[-1] / equity_curve.iloc[0] - 1) * 100,
            'sharpe_ratio': (returns.mean() / returns.std()) * np.sqrt(252) if returns.std() > 0 else 0,
            'max_drawdown': ((equity_curve / equity_curve.cummax()) - 1).min() * 100,
            'volatility': returns.std() * np.sqrt(252) * 100,
            'win_rate': (returns > 0).mean() * 100,
        }
        return metrics

    def format_backtest_summary(metrics, strategy_name="Strategy"):
        lines = [f"=== {strategy_name} ==="]
        for k, v in metrics.items():
            if isinstance(v, float):
                lines.append(f"  {k}: {v:.2f}")
            else:
                lines.append(f"  {k}: {v}")
        return '\n'.join(lines)

    def plot_backtest_results(df, **kwargs):
        print("[plot_backtest_results] Plot generated (visual output)")

    def plot_returns_distribution(returns, **kwargs):
        print("[plot_returns_distribution] Plot generated (visual output)")

    def compare_strategies(strategies, **kwargs):
        print("[compare_strategies] Comparison table:")
        for name, equity in strategies.items():
            total_ret = (equity.iloc[-1] / equity.iloc[0] - 1) * 100
            print(f"  {name}: {total_ret:.1f}% return")

    # Set up execution globals
    g = {
        '__builtins__': __builtins__,
        'pd': pd,
        'np': np,
        'plt': plt,
        'json': json,
        'sys': sys,
        'base64': base64,
        'qb': qb,
        'QuantBook': type(qb),
        'Resolution': Resolution,
        'QCAlgorithm': QCAlgorithm,
        'PythonData': PythonData,
        'PythonIndicator': PythonIndicator,
        'AlphaModel': AlphaModel,
        'PortfolioConstructionModel': PortfolioConstructionModel,
        'ExecutionModel': ExecutionModel,
        'RiskManagementModel': RiskManagementModel,
        'calculate_returns': calculate_returns,
        'add_technical_features': add_technical_features,
        'calculate_metrics': calculate_metrics,
        'format_backtest_summary': format_backtest_summary,
        'plot_backtest_results': plot_backtest_results,
        'plot_returns_distribution': plot_returns_distribution,
        'compare_strategies': compare_strategies,
        'print': print,
        'Dict': Dict,
        'List': List,
        'Tuple': Tuple,
        'Optional': Optional,
    }

    ec = 0
    ok = 0
    err = 0
    skipped = 0

    for cell in nb['cells']:
        if cell['cell_type'] != 'code':
            continue

        ec += 1
        code = ''.join(cell['source'])
        lines = code.split('\n')

        # Filter lines that won't work locally
        filtered = []
        skip_cell = False
        for line in lines:
            s = line.strip()
            # Skip QC-specific imports
            if 'from QuantConnect' in s and 'import' in s:
                continue
            if 'from AlgorithmImports' in s:
                continue
            if s == 'qb = QuantBook()':
                continue
            # Skip cells importing from shared/ (doesn't exist locally)
            if 'from features import' in s:
                continue
            if 'from backtest_helpers import' in s:
                continue
            if 'from plotting import' in s:
                continue
            if 'from Portfolio import' in s:
                continue
            if "sys.path.append" in s:
                continue
            # Skip Jupyter magic commands
            if s.startswith('%'):
                continue
            # Fix deprecated pandas fillna(method=...) -> bfill()/ffill()
            if "fillna(method='bfill')" in line or 'fillna(method="bfill")' in line:
                line = line.replace("fillna(method='bfill')", 'bfill()').replace('fillna(method="bfill")', 'bfill()')
                s = line.strip()
            if "fillna(method='ffill')" in line or 'fillna(method="ffill")' in line:
                line = line.replace("fillna(method='ffill')", 'ffill()').replace('fillna(method="ffill")', 'ffill()')
                s = line.strip()
            filtered.append(line)

        if skip_cell:
            code = '\n'.join(filtered)
            if not code.strip() or all(l.strip().startswith('#') or not l.strip() for l in filtered):
                cell['execution_count'] = ec
                cell['outputs'] = [{
                    'output_type': 'stream',
                    'name': 'stdout',
                    'text': [f'[QC Cloud required - {ec}] Execution requires QuantConnect Cloud environment\n']
                }]
                skipped += 1
                continue

        code = '\n'.join(filtered)
        if not code.strip():
            cell['execution_count'] = ec
            cell['outputs'] = []
            skipped += 1
            continue

        # Execute cell
        old_stdout = sys.stdout
        old_stderr = sys.stderr
        try:
            sys.stdout = StringIO()
            sys.stderr = StringIO()
            exec(code, g)

            out = sys.stdout.getvalue()
            outputs = []

            # Capture stdout
            if out:
                olines = out.splitlines(True)
                if olines and not olines[-1].endswith('\n'):
                    olines[-1] += '\n'
                outputs.append({
                    'output_type': 'stream',
                    'name': 'stdout',
                    'text': olines
                })

            # Capture matplotlib figures
            figs = [plt.figure(i) for i in plt.get_fignums()]
            if figs:
                for fig in figs:
                    buf = BytesIO()
                    fig.savefig(buf, format='png', dpi=72, bbox_inches='tight')
                    buf.seek(0)
                    img_b64 = base64.b64encode(buf.read()).decode('ascii')
                    outputs.append({
                        'output_type': 'display_data',
                        'data': {
                            'image/png': img_b64,
                            'text/plain': ['<Figure>']
                        },
                        'metadata': {}
                    })
                plt.close('all')

            cell['execution_count'] = ec
            cell['outputs'] = outputs
            ok += 1

        except Exception as e:
            cell['execution_count'] = ec
            cell['outputs'] = [{
                'output_type': 'error',
                'ename': type(e).__name__,
                'evalue': str(e),
                'traceback': [traceback.format_exc()]
            }]
            err += 1
            print(f"  Cell {ec} ERR: {type(e).__name__}: {str(e)[:80]}", file=sys.__stdout__)
        finally:
            sys.stdout = old_stdout
            sys.stderr = old_stderr

    # Save
    if output_path is None:
        output_path = notebook_path

    with open(output_path, 'w', encoding='utf-8') as f:
        json.dump(nb, f, ensure_ascii=False, indent=1)

    print(f"\nResults: {ec} cells, {ok} OK, {err} errors, {skipped} skipped")
    print(f"Saved to: {output_path}")
    return ok, err, skipped


if __name__ == '__main__':
    notebook = sys.argv[1]
    output = sys.argv[2] if len(sys.argv) > 2 else None
    execute_notebook(notebook, output)
