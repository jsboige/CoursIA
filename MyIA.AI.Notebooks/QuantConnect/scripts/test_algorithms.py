"""
QuantConnect Algorithms Backtest Runner

Lance des backtests automatisés sur les algorithmes QuantConnect (via LEAN CLI ou MCP).

Usage:
    python test_algorithms.py --algorithm MovingAverageCrossover.py --start 2020-01-01 --end 2023-12-31
    python test_algorithms.py --language python --all --report output/report.html
    python test_algorithms.py --algorithm algorithms/python/MLDirectionalRF.py --quick

Arguments:
    --algorithm     : Chemin vers l'algorithme (fichier .py ou .cs)
    --language      : Langage (python ou csharp)
    --all           : Tester tous les algorithmes du langage
    --start         : Date de début backtest (YYYY-MM-DD)
    --end           : Date de fin backtest (YYYY-MM-DD)
    --quick         : Backtest rapide (1 an, résolution daily)
    --report        : Générer rapport HTML
    --mode          : Mode d'exécution (lean-cli, mcp, cloud)

Examples:
    python test_algorithms.py --algorithm MovingAverageCrossover.py --quick
    python test_algorithms.py --language python --all --report output/python_report.html
"""

import json
import sys
import os
from pathlib import Path
from typing import Dict, List, Optional, Tuple
from datetime import datetime, timedelta
import subprocess
import time

# Ajouter le répertoire racine au path
script_dir = Path(__file__).parent.parent.parent.parent
sys.path.insert(0, str(script_dir))


class AlgorithmTester:
    """Testeur d'algorithmes QuantConnect"""

    def __init__(self, mode: str = 'lean-cli', verbose: bool = True):
        """
        Args:
            mode: 'lean-cli' (local), 'mcp' (via MCP QuantConnect), 'cloud' (API QC)
            verbose: Affichage détaillé
        """
        self.mode = mode
        self.verbose = verbose
        self.results = []

    def log(self, message: str, level: str = 'INFO'):
        """Log message"""
        if self.verbose:
            timestamp = datetime.now().strftime('%H:%M:%S')
            prefix = {
                'INFO': 'ℹ',
                'SUCCESS': '✓',
                'ERROR': '✗',
                'WARNING': '⚠',
                'RUN': '▶'
            }.get(level, ' ')
            print(f"[{timestamp}] {prefix} {message}")

    def test_algorithm(self,
                      algorithm_path: Path,
                      start_date: str,
                      end_date: str,
                      language: str = 'python',
                      quick: bool = False) -> Dict[str, any]:
        """
        Teste un algorithme avec un backtest

        Args:
            algorithm_path: Chemin vers l'algorithme (.py ou .cs)
            start_date: Date de début (YYYY-MM-DD)
            end_date: Date de fin (YYYY-MM-DD)
            language: 'python' ou 'csharp'
            quick: Backtest rapide (1 an au lieu de la période complète)

        Returns:
            {
                'algorithm': str,
                'language': str,
                'status': 'success' | 'failed',
                'backtest_id': str,
                'metrics': {...},
                'error': str (si failed),
                'duration': float (secondes)
            }
        """
        self.log(f"Testing {algorithm_path.name} ({language})", 'RUN')

        start_time = time.time()

        # Ajuster dates si quick mode
        if quick:
            end_dt = datetime.now()
            start_dt = end_dt - timedelta(days=365)
            start_date = start_dt.strftime('%Y-%m-%d')
            end_date = end_dt.strftime('%Y-%m-%d')
            self.log(f"Quick mode : {start_date} to {end_date}", 'INFO')

        # Exécuter selon le mode
        if self.mode == 'lean-cli':
            result = self._test_with_lean_cli(algorithm_path, start_date, end_date, language)
        elif self.mode == 'mcp':
            result = self._test_with_mcp(algorithm_path, start_date, end_date, language)
        else:  # cloud
            result = self._test_with_cloud_api(algorithm_path, start_date, end_date, language)

        duration = time.time() - start_time
        result['duration'] = duration

        # Log résultat
        if result['status'] == 'success':
            self.log(
                f"✓ {algorithm_path.name} - Sharpe: {result['metrics'].get('sharpe_ratio', 'N/A'):.2f}, "
                f"Return: {result['metrics'].get('total_return', 'N/A'):.2%} "
                f"({duration:.1f}s)",
                'SUCCESS'
            )
        else:
            self.log(f"✗ {algorithm_path.name} - {result.get('error', 'Unknown error')}", 'ERROR')

        self.results.append(result)
        return result

    def _test_with_lean_cli(self, algorithm_path: Path, start_date: str,
                           end_date: str, language: str) -> Dict[str, any]:
        """Teste avec LEAN CLI local"""
        try:
            # Créer projet temporaire si nécessaire
            project_name = algorithm_path.stem

            # Commande LEAN backtest
            cmd = [
                'lean', 'backtest',
                str(algorithm_path.parent),
                '--data-provider-historical', 'Local',
                '--start', start_date,
                '--end', end_date
            ]

            self.log(f"Running: {' '.join(cmd)}", 'INFO')

            # Exécuter
            process = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=300  # 5 minutes max
            )

            if process.returncode != 0:
                return {
                    'algorithm': str(algorithm_path),
                    'language': language,
                    'status': 'failed',
                    'error': process.stderr or 'Unknown error',
                    'metrics': {}
                }

            # Parser résultats
            output = process.stdout
            metrics = self._parse_lean_output(output)

            return {
                'algorithm': str(algorithm_path),
                'language': language,
                'status': 'success',
                'backtest_id': 'local',
                'metrics': metrics
            }

        except subprocess.TimeoutExpired:
            return {
                'algorithm': str(algorithm_path),
                'language': language,
                'status': 'failed',
                'error': 'Timeout (>5 minutes)',
                'metrics': {}
            }
        except Exception as e:
            return {
                'algorithm': str(algorithm_path),
                'language': language,
                'status': 'failed',
                'error': str(e),
                'metrics': {}
            }

    def _test_with_mcp(self, algorithm_path: Path, start_date: str,
                      end_date: str, language: str) -> Dict[str, any]:
        """Teste avec MCP QuantConnect"""
        # TODO: Implémenter via MCP API quand disponible
        self.log("MCP mode pas encore implémenté, utiliser lean-cli", 'WARNING')
        return {
            'algorithm': str(algorithm_path),
            'language': language,
            'status': 'failed',
            'error': 'MCP mode not implemented yet',
            'metrics': {}
        }

    def _test_with_cloud_api(self, algorithm_path: Path, start_date: str,
                            end_date: str, language: str) -> Dict[str, any]:
        """Teste avec API QuantConnect Cloud"""
        # TODO: Implémenter via API QuantConnect
        self.log("Cloud API mode pas encore implémenté, utiliser lean-cli", 'WARNING')
        return {
            'algorithm': str(algorithm_path),
            'language': language,
            'status': 'failed',
            'error': 'Cloud API mode not implemented yet',
            'metrics': {}
        }

    def _parse_lean_output(self, output: str) -> Dict[str, float]:
        """Parse sortie LEAN CLI pour extraire métriques"""
        metrics = {}

        # Patterns à chercher
        patterns = {
            'sharpe_ratio': r'Sharpe Ratio:\s*([-\d.]+)',
            'total_return': r'Total Net Profit:\s*([-\d.]+)%',
            'max_drawdown': r'Drawdown:\s*([-\d.]+)%',
            'trades': r'Total Trades:\s*(\d+)',
            'win_rate': r'Win Rate:\s*([-\d.]+)%'
        }

        import re
        for metric_name, pattern in patterns.items():
            match = re.search(pattern, output)
            if match:
                try:
                    value = float(match.group(1))
                    if metric_name in ['total_return', 'max_drawdown', 'win_rate']:
                        value = value / 100.0  # Convertir % en décimal
                    metrics[metric_name] = value
                except ValueError:
                    pass

        return metrics

    def test_all(self, algorithms_dir: Path, language: str,
                start_date: str, end_date: str, quick: bool = False) -> List[Dict]:
        """Teste tous les algorithmes d'un répertoire"""
        self.log(f"Testing all {language} algorithms in {algorithms_dir}", 'INFO')

        # Trouver tous les fichiers
        if language == 'python':
            pattern = '*.py'
        else:
            pattern = '*.cs'

        algorithms = list(algorithms_dir.glob(pattern))

        if not algorithms:
            self.log(f"No algorithms found with pattern {pattern}", 'WARNING')
            return []

        self.log(f"Found {len(algorithms)} algorithms to test", 'INFO')

        # Tester chaque algorithme
        for algo_path in sorted(algorithms):
            self.test_algorithm(algo_path, start_date, end_date, language, quick)

        return self.results

    def generate_report(self, output_path: Path):
        """Génère un rapport HTML des résultats"""
        if not self.results:
            self.log("No results to report", 'WARNING')
            return

        html = """
<!DOCTYPE html>
<html>
<head>
    <meta charset="utf-8">
    <title>QuantConnect Algorithms Test Report</title>
    <style>
        body { font-family: Arial, sans-serif; margin: 20px; }
        h1 { color: #0066cc; }
        table { border-collapse: collapse; width: 100%; margin-top: 20px; }
        th, td { border: 1px solid #ddd; padding: 12px; text-align: left; }
        th { background-color: #0066cc; color: white; }
        tr:nth-child(even) { background-color: #f2f2f2; }
        .success { color: green; font-weight: bold; }
        .failed { color: red; font-weight: bold; }
        .metric { text-align: right; }
    </style>
</head>
<body>
    <h1>QuantConnect Algorithms Test Report</h1>
    <p>Generated: {timestamp}</p>
    <p>Total algorithms: {total}, Success: {success}, Failed: {failed}</p>

    <table>
        <thead>
            <tr>
                <th>Algorithm</th>
                <th>Language</th>
                <th>Status</th>
                <th>Sharpe Ratio</th>
                <th>Total Return</th>
                <th>Max Drawdown</th>
                <th>Trades</th>
                <th>Duration (s)</th>
            </tr>
        </thead>
        <tbody>
"""

        for result in self.results:
            algo_name = Path(result['algorithm']).name
            status = result['status']
            status_class = 'success' if status == 'success' else 'failed'
            metrics = result.get('metrics', {})

            html += f"""
            <tr>
                <td>{algo_name}</td>
                <td>{result['language']}</td>
                <td class="{status_class}">{status.upper()}</td>
                <td class="metric">{metrics.get('sharpe_ratio', 'N/A'):.2f if isinstance(metrics.get('sharpe_ratio'), (int, float)) else 'N/A'}</td>
                <td class="metric">{metrics.get('total_return', 'N/A'):.2%} if isinstance(metrics.get('total_return'), (int, float)) else 'N/A'}</td>
                <td class="metric">{metrics.get('max_drawdown', 'N/A'):.2%} if isinstance(metrics.get('max_drawdown'), (int, float)) else 'N/A'}</td>
                <td class="metric">{metrics.get('trades', 'N/A')}</td>
                <td class="metric">{result.get('duration', 0):.1f}</td>
            </tr>
"""

        html += """
        </tbody>
    </table>
</body>
</html>
"""

        # Remplacer placeholders
        total = len(self.results)
        success = sum(1 for r in self.results if r['status'] == 'success')
        failed = total - success

        html = html.format(
            timestamp=datetime.now().strftime('%Y-%m-%d %H:%M:%S'),
            total=total,
            success=success,
            failed=failed
        )

        # Écrire fichier
        output_path.parent.mkdir(parents=True, exist_ok=True)
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write(html)

        self.log(f"Report generated: {output_path}", 'SUCCESS')


def main():
    import argparse

    parser = argparse.ArgumentParser(description='Tester algorithmes QuantConnect')
    parser.add_argument('--algorithm', type=str, help='Chemin vers algorithme')
    parser.add_argument('--language', type=str, choices=['python', 'csharp'],
                       help='Langage (python ou csharp)')
    parser.add_argument('--all', action='store_true', help='Tester tous les algorithmes')
    parser.add_argument('--start', type=str, default='2020-01-01',
                       help='Date de début (YYYY-MM-DD)')
    parser.add_argument('--end', type=str, default='2023-12-31',
                       help='Date de fin (YYYY-MM-DD)')
    parser.add_argument('--quick', action='store_true', help='Backtest rapide (1 an)')
    parser.add_argument('--report', type=str, help='Générer rapport HTML')
    parser.add_argument('--mode', type=str, default='lean-cli',
                       choices=['lean-cli', 'mcp', 'cloud'],
                       help='Mode exécution (lean-cli, mcp, cloud)')
    parser.add_argument('--verbose', action='store_true', help='Affichage détaillé')

    args = parser.parse_args()

    # Validation
    if not args.algorithm and not args.all:
        parser.error("Spécifier --algorithm ou --all")

    if args.all and not args.language:
        parser.error("--all requiert --language")

    print("=" * 70)
    print("QuantConnect Algorithms Backtest Runner")
    print("=" * 70)
    print(f"Mode: {args.mode}")
    print(f"Period: {args.start} to {args.end}")
    print(f"Quick mode: {'Yes' if args.quick else 'No'}")
    print("=" * 70)
    print()

    # Créer tester
    tester = AlgorithmTester(mode=args.mode, verbose=args.verbose or True)

    # Tester
    if args.algorithm:
        # Test single algorithm
        algo_path = Path(args.algorithm).resolve()
        if not algo_path.exists():
            print(f"✗ Algorithm not found: {algo_path}")
            sys.exit(1)

        language = args.language or ('python' if algo_path.suffix == '.py' else 'csharp')

        result = tester.test_algorithm(
            algo_path,
            args.start,
            args.end,
            language=language,
            quick=args.quick
        )

    else:
        # Test all algorithms
        # Trouver répertoire algorithms/python ou algorithms/csharp
        script_parent = Path(__file__).parent.parent
        algorithms_dir = script_parent / 'algorithms' / args.language

        if not algorithms_dir.exists():
            print(f"✗ Algorithms directory not found: {algorithms_dir}")
            sys.exit(1)

        results = tester.test_all(
            algorithms_dir,
            args.language,
            args.start,
            args.end,
            quick=args.quick
        )

    # Générer rapport si demandé
    if args.report:
        report_path = Path(args.report)
        tester.generate_report(report_path)

    # Résumé
    print()
    print("=" * 70)
    print("Summary")
    print("=" * 70)
    total = len(tester.results)
    success = sum(1 for r in tester.results if r['status'] == 'success')
    failed = total - success

    print(f"Total: {total}")
    print(f"✓ Success: {success}")
    print(f"✗ Failed: {failed}")

    if total > 0:
        success_rate = (success / total) * 100
        print(f"Success rate: {success_rate:.1f}%")

    sys.exit(0 if failed == 0 else 1)


if __name__ == '__main__':
    main()
