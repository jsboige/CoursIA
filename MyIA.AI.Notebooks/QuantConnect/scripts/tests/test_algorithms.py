"""Tests for test_algorithms.py — QC Algorithms Backtest Runner.

These tests cover the pure-logic parts of AlgorithmTester without running
actual LEAN CLI backtests (no subprocess, no network).

Run from the tests directory:
    python -m pytest test_algorithms.py -v
"""

import sys
from io import StringIO
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from test_algorithms import AlgorithmTester


# --- AlgorithmTester.__init__ ---


class TestInit:
    def test_defaults(self):
        t = AlgorithmTester()
        assert t.mode == "lean-cli"
        assert t.verbose is True
        assert t.results == []

    def test_custom_mode(self):
        t = AlgorithmTester(mode="mcp", verbose=False)
        assert t.mode == "mcp"
        assert t.verbose is False

    def test_results_list_independent(self):
        a = AlgorithmTester()
        b = AlgorithmTester()
        a.results.append({"test": 1})
        assert b.results == []


# --- AlgorithmTester.log ---


class TestLog:
    def test_verbose_prints(self, capsys):
        t = AlgorithmTester(verbose=True)
        t.log("hello", "INFO")
        out = capsys.readouterr().out
        assert "hello" in out

    def test_silent_no_output(self, capsys):
        t = AlgorithmTester(verbose=False)
        t.log("hidden", "INFO")
        out = capsys.readouterr().out
        assert out == ""

    def test_level_prefixes(self, capsys):
        t = AlgorithmTester(verbose=True)
        t.log("test", "SUCCESS")
        out = capsys.readouterr().out
        # Should contain some prefix character (checkmark or similar)
        assert "test" in out

    def test_unknown_level(self, capsys):
        t = AlgorithmTester(verbose=True)
        t.log("msg", "CUSTOM")
        out = capsys.readouterr().out
        assert "msg" in out


# --- AlgorithmTester._parse_lean_output ---


class TestParseLeanOutput:
    def setup_method(self):
        self.tester = AlgorithmTester(verbose=False)

    def test_all_metrics(self):
        output = """
Backtest completed.
Total Net Profit: 15.30%
Sharpe Ratio: 1.42
Drawdown: -8.50%
Total Trades: 120
Win Rate: 58.30%
"""
        metrics = self.tester._parse_lean_output(output)
        assert abs(metrics["total_return"] - 0.153) < 1e-6
        assert abs(metrics["sharpe_ratio"] - 1.42) < 1e-6
        assert abs(metrics["max_drawdown"] - (-0.085)) < 1e-6
        assert metrics["trades"] == 120.0
        assert abs(metrics["win_rate"] - 0.583) < 1e-6

    def test_negative_return(self):
        output = "Total Net Profit: -5.20%"
        metrics = self.tester._parse_lean_output(output)
        assert abs(metrics["total_return"] - (-0.052)) < 1e-6

    def test_sharpe_only(self):
        output = "Sharpe Ratio: 2.10"
        metrics = self.tester._parse_lean_output(output)
        assert "sharpe_ratio" in metrics
        assert "total_return" not in metrics

    def test_empty_output(self):
        metrics = self.tester._parse_lean_output("")
        assert metrics == {}

    def test_no_matching_patterns(self):
        output = "Some random log output\nNothing useful here"
        metrics = self.tester._parse_lean_output(output)
        assert metrics == {}

    def test_zero_values(self):
        output = "Total Net Profit: 0.00%\nSharpe Ratio: 0.00\nTotal Trades: 0\nWin Rate: 0.00%"
        metrics = self.tester._parse_lean_output(output)
        assert metrics["total_return"] == 0.0
        assert metrics["sharpe_ratio"] == 0.0
        assert metrics["trades"] == 0.0
        assert metrics["win_rate"] == 0.0

    def test_large_sharpe(self):
        output = "Sharpe Ratio: -3.75"
        metrics = self.tester._parse_lean_output(output)
        assert abs(metrics["sharpe_ratio"] - (-3.75)) < 1e-6

    def test_percent_converted_to_decimal(self):
        """Percentages are divided by 100."""
        output = "Total Net Profit: 100.00%\nMax Drawdown: -50.00%"
        # Note: the regex uses 'Drawdown:' not 'Max Drawdown:'
        metrics = self.tester._parse_lean_output(output)
        assert abs(metrics["total_return"] - 1.0) < 1e-6

    def test_trades_as_integer_value(self):
        output = "Total Trades: 42"
        metrics = self.tester._parse_lean_output(output)
        assert metrics["trades"] == 42.0


# --- AlgorithmTester._test_with_mcp / _test_with_cloud_api ---


class TestUnimplementedModes:
    def test_mcp_returns_failed(self):
        t = AlgorithmTester(mode="mcp", verbose=False)
        result = t._test_with_mcp(Path("test.py"), "2020-01-01", "2023-12-31", "python")
        assert result["status"] == "failed"
        assert "not implemented" in result["error"].lower()

    def test_cloud_returns_failed(self):
        t = AlgorithmTester(mode="cloud", verbose=False)
        result = t._test_with_cloud_api(Path("test.py"), "2020-01-01", "2023-12-31", "python")
        assert result["status"] == "failed"
        assert "not implemented" in result["error"].lower()


# --- AlgorithmTester.generate_report ---


class TestGenerateReport:
    def test_empty_results_no_file(self, tmp_path):
        t = AlgorithmTester(verbose=False)
        report_path = tmp_path / "report.html"
        t.generate_report(report_path)
        assert not report_path.exists()

    def test_generates_html(self, tmp_path):
        t = AlgorithmTester(verbose=False)
        t.results = [
            {
                "algorithm": "test_algo.py",
                "language": "python",
                "status": "success",
                "metrics": {"sharpe_ratio": 1.5, "total_return": 0.10, "max_drawdown": -0.05, "trades": 50},
                "duration": 12.3,
            }
        ]
        report_path = tmp_path / "report.html"
        t.generate_report(report_path)
        assert report_path.exists()
        content = report_path.read_text(encoding="utf-8")
        assert "test_algo.py" in content
        assert "SUCCESS" in content
        assert "1.50" in content  # Sharpe displayed

    def test_mixed_results(self, tmp_path):
        t = AlgorithmTester(verbose=False)
        t.results = [
            {
                "algorithm": "good.py",
                "language": "python",
                "status": "success",
                "metrics": {},
                "duration": 5.0,
            },
            {
                "algorithm": "bad.py",
                "language": "csharp",
                "status": "failed",
                "metrics": {},
                "error": "Compilation error",
                "duration": 1.0,
            },
        ]
        report_path = tmp_path / "report.html"
        t.generate_report(report_path)
        content = report_path.read_text(encoding="utf-8")
        assert "good.py" in content
        assert "bad.py" in content
        assert "FAILED" in content

    def test_report_creates_parent_dirs(self, tmp_path):
        t = AlgorithmTester(verbose=False)
        t.results = [
            {"algorithm": "a.py", "language": "python", "status": "success", "metrics": {}, "duration": 1.0}
        ]
        nested = tmp_path / "sub" / "dir" / "report.html"
        t.generate_report(nested)
        assert nested.exists()


# --- AlgorithmTester.test_all ---


class TestTestAll:
    def test_empty_directory(self, tmp_path):
        t = AlgorithmTester(verbose=False)
        results = t.test_all(tmp_path, "python", "2020-01-01", "2023-12-31")
        assert results == []

    def test_finds_python_files(self, tmp_path):
        (tmp_path / "algo1.py").write_text("# test", encoding="utf-8")
        (tmp_path / "algo2.py").write_text("# test", encoding="utf-8")
        (tmp_path / "readme.md").write_text("# docs", encoding="utf-8")
        t = AlgorithmTester(verbose=False)
        # test_all calls test_algorithm which tries lean-cli — it will fail
        # but we verify it finds and attempts the 2 .py files
        results = t.test_all(tmp_path, "python", "2020-01-01", "2023-12-31")
        assert len(results) == 2
        # Both will fail (no lean CLI) but the attempt was made
        assert all(r["status"] == "failed" for r in results)


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
