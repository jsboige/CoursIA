"""Tests for qc-mcp-lite server.py — auth, rate limiting, stats extraction."""

import base64
import hashlib
import json
import time
from collections import deque
from datetime import datetime, timezone
from unittest.mock import MagicMock, patch

import pytest

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent.parent))
from server import (
    API_BASE,
    RATE_LIMIT_MAX,
    RATE_LIMIT_WINDOW,
    _api_post,
    _auth_headers,
    _call_timestamps,
    _extract_stats,
    _get_credentials,
    _rate_limit,
    create_backtest,
    create_compile,
    create_file,
    create_project,
    list_backtests,
    list_projects,
    read_backtest,
    read_compile,
    read_file,
    read_project,
    update_file_contents,
)


# --- _get_credentials ---


class TestGetCredentials:
    def test_valid_credentials(self):
        with patch.dict(
            "os.environ",
            {"QC_API_USER_ID": "12345", "QC_API_ACCESS_TOKEN": "abc123"},
        ):
            uid, tok = _get_credentials()
            assert uid == "12345"
            assert tok == "abc123"

    def test_missing_user_id_raises(self):
        with patch.dict("os.environ", {"QC_API_ACCESS_TOKEN": "abc"}, clear=True):
            with pytest.raises(ValueError, match="QC_API_USER_ID"):
                _get_credentials()

    def test_missing_token_raises(self):
        with patch.dict("os.environ", {"QC_API_USER_ID": "123"}, clear=True):
            with pytest.raises(ValueError, match="QC_API_ACCESS_TOKEN"):
                _get_credentials()

    def test_empty_strings_raise(self):
        with patch.dict(
            "os.environ",
            {"QC_API_USER_ID": "", "QC_API_ACCESS_TOKEN": ""},
            clear=True,
        ):
            with pytest.raises(ValueError):
                _get_credentials()


# --- _auth_headers ---


class TestAuthHeaders:
    def test_contains_authorization_and_timestamp(self):
        with patch.dict(
            "os.environ",
            {"QC_API_USER_ID": "46613", "QC_API_ACCESS_TOKEN": "testtoken"},
        ):
            headers = _auth_headers()
            assert "Authorization" in headers
            assert "Timestamp" in headers
            assert headers["Authorization"].startswith("Basic ")

    def test_sha256_hash_scheme(self):
        """Verify the QC v2 auth: SHA256(token:timestamp) + Basic base64(uid:hash)."""
        uid, token = "46613", "testtoken"
        with patch.dict(
            "os.environ",
            {"QC_API_USER_ID": uid, "QC_API_ACCESS_TOKEN": token},
        ):
            with patch("server.datetime") as mock_dt:
                fixed_ts = 1700000000
                mock_dt.now.return_value = datetime.fromtimestamp(fixed_ts, tz=timezone.utc)
                headers = _auth_headers()

                expected_hash = hashlib.sha256(
                    f"{token}:{fixed_ts}".encode("utf-8")
                ).hexdigest()
                expected_basic = base64.b64encode(
                    f"{uid}:{expected_hash}".encode()
                ).decode()

                assert headers["Authorization"] == f"Basic {expected_basic}"
                assert headers["Timestamp"] == str(fixed_ts)

    def test_different_timestamps_different_hashes(self):
        """Each call produces a different hash (timestamp-based)."""
        with patch.dict(
            "os.environ",
            {"QC_API_USER_ID": "1", "QC_API_ACCESS_TOKEN": "tok"},
        ):
            h1 = _auth_headers()
            h2 = _auth_headers()
            # Unlikely but possible they share the same second — just check format
            assert h1["Authorization"].startswith("Basic ")
            assert h2["Authorization"].startswith("Basic ")


# --- _rate_limit ---


class TestRateLimit:
    def test_allows_up_to_max_calls(self):
        """Should not block the first RATE_LIMIT_MAX calls."""
        global _call_timestamps
        _call_timestamps.clear()
        start = time.time()
        for _ in range(RATE_LIMIT_MAX):
            _rate_limit()
        elapsed = time.time() - start
        assert elapsed < 1.0  # Should be instant, no sleep

    def test_throttles_on_excess(self):
        """11th call within the window should trigger sleep."""
        global _call_timestamps
        _call_timestamps.clear()
        # Pre-fill the deque with RATE_LIMIT_MAX entries
        now = time.time()
        for _ in range(RATE_LIMIT_MAX):
            _call_timestamps.append(now - 1)  # 1s ago

        with patch("server.time.sleep") as mock_sleep:
            _rate_limit()
            mock_sleep.assert_called_once()
            # Sleep duration should be close to remaining window
            call_args = mock_sleep.call_args[0][0]
            assert call_args > 0
            assert call_args <= RATE_LIMIT_WINDOW + 1

    def test_window_expiry(self):
        """Old timestamps should be pruned, allowing new calls."""
        global _call_timestamps
        _call_timestamps.clear()
        # Add an old timestamp that should expire
        _call_timestamps.append(time.time() - RATE_LIMIT_WINDOW - 1)
        with patch("server.time.sleep"):
            _rate_limit()
        # Old one should have been removed
        assert len(_call_timestamps) <= RATE_LIMIT_MAX


# --- _extract_stats ---


class TestExtractStats:
    def test_full_stats(self):
        bt = {
            "backtestId": "abc123",
            "name": "Test Backtest",
            "status": "Completed",
            "created": "2026-01-01",
            "completed": "2026-01-01",
            "tradeableDates": 252,
            "totalOrders": 42,
            "equity": {"start": 100000, "end": 110000},
            "progress": 1.0,
            "statistics": {
                "Sharpe Ratio": "1.234",
                "Compounding Annual Return": "12.5%",
                "Drawdown": "8.3%",
                "Net Profit": "$10,000",
                "Probabilistic Sharpe Ratio": "0.95",
            },
        }
        result = _extract_stats(bt)
        assert result["backtestId"] == "abc123"
        assert result["name"] == "Test Backtest"
        assert result["status"] == "Completed"
        assert result["tradeableDates"] == 252
        assert result["totalOrders"] == 42
        assert result["statistics"]["sharpeRatio"] == "1.234"
        assert result["statistics"]["compoundingAnnualReturn"] == "12.5%"
        assert result["statistics"]["drawdown"] == "8.3%"
        assert result["statistics"]["totalNetProfit"] == "$10,000"
        assert result["statistics"]["probabilisticSharpeRatio"] == "0.95"

    def test_missing_statistics(self):
        bt = {"backtestId": "xyz", "name": "Empty", "status": "Running"}
        result = _extract_stats(bt)
        assert result["statistics"]["sharpeRatio"] == "-"
        assert result["statistics"]["drawdown"] == "-"

    def test_null_statistics(self):
        bt = {"backtestId": "n", "statistics": None}
        result = _extract_stats(bt)
        assert result["statistics"]["sharpeRatio"] == "-"

    def test_partial_statistics(self):
        bt = {
            "backtestId": "p",
            "statistics": {"Sharpe Ratio": "0.5"},
        }
        result = _extract_stats(bt)
        assert result["statistics"]["sharpeRatio"] == "0.5"
        assert result["statistics"]["compoundingAnnualReturn"] == "-"

    def test_missing_top_level_fields(self):
        result = _extract_stats({})
        assert result["backtestId"] == ""
        assert result["tradeableDates"] == 0
        assert result["totalOrders"] == 0

    def test_progress_field(self):
        result = _extract_stats({"progress": 0.5})
        assert result["progress"] == 0.5

    def test_zero_orders(self):
        """totalOrders could be None/0 from QC API."""
        result = _extract_stats({"totalOrders": None})
        assert result["totalOrders"] == 0

    def test_real_qc_payload_orders_not_lost(self):
        """Regression (verified firsthand against QC backtests/read c.332): a
        completed backtest has totalOrders=null at the top level and the real
        count lives in statistics['Total Orders']. The old code read the
        top-level field and reported 0 — a strategy that placed 318 orders was
        falsely diagnosed as 'never traded' (cf issue #6192). statistics is the
        authoritative source."""
        bt = {
            "backtestId": "33286487",
            "name": "1630-DualMomentum-aligned",
            "status": "Completed.",
            "totalOrders": None,  # QC returns null here, NOT the count
            "tradeableDates": 1761,
            "statistics": {
                "Total Orders": "318",
                "Net Profit": "76.088%",
                "Sharpe Ratio": "0.35",
                "Compounding Annual Return": "8.413%",
                "Drawdown": "14.900%",
                "Probabilistic Sharpe Ratio": "1.719%",
            },
            "runtimeStatistics": {
                "Net Profit": "$59,745.60",
                "Return": "76.09 %",
            },
        }
        result = _extract_stats(bt)
        assert result["totalOrders"] == 318  # NOT 0
        assert result["statistics"]["totalNetProfit"] == "76.088%"  # NOT "-"
        assert result["statistics"]["netProfitAbsolute"] == "$59,745.60"
        assert result["statistics"]["sharpeRatio"] == "0.35"

    def test_zero_orders_in_statistics_stays_zero(self):
        """A genuinely 0-trade backtest (statistics['Total Orders']='0' or '-')
        must still report 0 — preserves the real 0-trade signal that the
        regression guard above must not mask."""
        assert _extract_stats(
            {"statistics": {"Total Orders": "0"}}
        )["totalOrders"] == 0
        assert _extract_stats(
            {"statistics": {"Total Orders": "-"}}
        )["totalOrders"] == 0

    def test_total_orders_parses_thousands_separator(self):
        """QC formats large counts with commas ('1,234') — must parse to int."""
        assert _extract_stats(
            {"statistics": {"Total Orders": "1,234"}}
        )["totalOrders"] == 1234

    def test_surfaces_runtime_error(self):
        """A failed backtest must surface error/stacktrace for diagnosis."""
        bt = {
            "backtestId": "fail1",
            "status": "Runtime Error",
            "error": "Unsupported security type: Crypto",
            "stacktrace": "  at PythonException.cs:line 52",
        }
        result = _extract_stats(bt)
        assert result["error"] == "Unsupported security type: Crypto"
        assert result["stacktrace"] == "  at PythonException.cs:line 52"

    def test_no_error_field_when_clean(self):
        """A clean backtest should not carry empty error/stacktrace keys."""
        result = _extract_stats({"backtestId": "ok", "status": "Completed"})
        assert "error" not in result
        assert "stacktrace" not in result

    def test_error_capped_to_1200_chars(self):
        """Oversized error/stacktrace must be capped to bound response size."""
        bt = {
            "backtestId": "big",
            "error": "E" * 5000,
            "stacktrace": "S" * 5000,
        }
        result = _extract_stats(bt)
        assert len(result["error"]) == 1200
        assert len(result["stacktrace"]) == 1200


# --- _api_post ---


class TestApiPost:
    def test_posts_to_correct_url(self):
        with patch.dict(
            "os.environ",
            {"QC_API_USER_ID": "1", "QC_API_ACCESS_TOKEN": "t"},
        ):
            mock_resp = MagicMock()
            mock_resp.json.return_value = {"success": True}
            mock_resp.raise_for_status = MagicMock()

            with patch("requests.post", return_value=mock_resp) as mock_post:
                result = _api_post("/compile/create", {"projectId": 1})
                mock_post.assert_called_once()
                call_url = mock_post.call_args[0][0]
                assert call_url == f"{API_BASE}/compile/create"

    def test_passes_json_body(self):
        with patch.dict(
            "os.environ",
            {"QC_API_USER_ID": "1", "QC_API_ACCESS_TOKEN": "t"},
        ):
            mock_resp = MagicMock()
            mock_resp.json.return_value = {"ok": True}
            mock_resp.raise_for_status = MagicMock()

            with patch("requests.post", return_value=mock_resp) as mock_post:
                _api_post("/test/path", {"key": "value"})
                assert mock_post.call_args.kwargs["json"] == {"key": "value"}

    def test_default_empty_body(self):
        with patch.dict(
            "os.environ",
            {"QC_API_USER_ID": "1", "QC_API_ACCESS_TOKEN": "t"},
        ):
            mock_resp = MagicMock()
            mock_resp.json.return_value = {}
            mock_resp.raise_for_status = MagicMock()

            with patch("requests.post", return_value=mock_resp) as mock_post:
                _api_post("/test")
                assert mock_post.call_args.kwargs["json"] == {}

    def test_timeout_120(self):
        with patch.dict(
            "os.environ",
            {"QC_API_USER_ID": "1", "QC_API_ACCESS_TOKEN": "t"},
        ):
            mock_resp = MagicMock()
            mock_resp.json.return_value = {}
            mock_resp.raise_for_status = MagicMock()

            with patch("requests.post", return_value=mock_resp) as mock_post:
                _api_post("/test")
                assert mock_post.call_args.kwargs["timeout"] == 120

    def test_surfaces_qc_api_failure(self):
        """QC returns HTTP 200 + success:false + errors — must raise, not return."""
        with patch.dict(
            "os.environ",
            {"QC_API_USER_ID": "1", "QC_API_ACCESS_TOKEN": "t"},
        ):
            mock_resp = _mock_api_response(
                {"success": False, "errors": ["Compile is not in a ready state"]}
            )
            with patch("requests.post", return_value=mock_resp):
                with pytest.raises(RuntimeError, match="Compile is not in a ready state"):
                    _api_post("/backtests/create")

    def test_success_true_does_not_raise(self):
        """An explicit success:true must pass through untouched."""
        with patch.dict(
            "os.environ",
            {"QC_API_USER_ID": "1", "QC_API_ACCESS_TOKEN": "t"},
        ):
            mock_resp = _mock_api_response({"success": True, "compileId": "c1"})
            with patch("requests.post", return_value=mock_resp):
                result = _api_post("/compile/create", {"projectId": 1})
            assert result["compileId"] == "c1"

    def test_missing_success_key_does_not_raise(self):
        """Legacy endpoints without a 'success' key must pass through."""
        with patch.dict(
            "os.environ",
            {"QC_API_USER_ID": "1", "QC_API_ACCESS_TOKEN": "t"},
        ):
            mock_resp = _mock_api_response({"projects": [{"projectId": 1}]})
            with patch("requests.post", return_value=mock_resp):
                result = _api_post("/projects/read")
            assert result["projects"][0]["projectId"] == 1


# --- Tool functions (mocked API) ---
# These all need env vars because _api_post -> _auth_headers -> _get_credentials.
# We patch requests.post AND set dummy env vars.

_DUMMY_ENV = {"QC_API_USER_ID": "test", "QC_API_ACCESS_TOKEN": "testtoken"}


def _mock_api_response(json_data: dict) -> MagicMock:
    """Create a mock response with json() and raise_for_status()."""
    mock = MagicMock()
    mock.json.return_value = json_data
    mock.raise_for_status = MagicMock()
    return mock


@patch.dict("os.environ", _DUMMY_ENV)
class TestCreateCompile:
    def test_returns_compile_id(self):
        mock_resp = _mock_api_response({"compileId": "abc-123", "state": "InQueue"})
        with patch("requests.post", return_value=mock_resp):
            result = create_compile(999)
            assert result["compileId"] == "abc-123"
            assert result["state"] == "InQueue"
            assert result["projectId"] == 999


@patch.dict("os.environ", _DUMMY_ENV)
class TestReadCompile:
    def test_returns_state_and_errors(self):
        mock_resp = _mock_api_response({"compileId": "xyz", "state": "BuildSuccess", "errors": []})
        with patch("requests.post", return_value=mock_resp):
            result = read_compile(1, "xyz")
            assert result["state"] == "BuildSuccess"
            assert result["errors"] == []

    def test_returns_build_errors(self):
        mock_resp = _mock_api_response({"state": "BuildError", "errors": ["CS0103: name 'x' not found"]})
        with patch("requests.post", return_value=mock_resp):
            result = read_compile(1, "c1")
            assert result["state"] == "BuildError"
            assert len(result["errors"]) == 1


@patch.dict("os.environ", _DUMMY_ENV)
class TestCreateBacktest:
    def test_returns_backtest_id(self):
        mock_resp = _mock_api_response({"backtest": {"backtestId": "bt-001", "status": "In Queue"}})
        with patch("requests.post", return_value=mock_resp):
            result = create_backtest(1, "comp-1", "test-bt")
            assert result["backtestId"] == "bt-001"

    def test_with_parameters(self):
        mock_resp = _mock_api_response({"backtest": {"backtestId": "bt-002", "status": "In Queue"}})
        with patch("requests.post", return_value=mock_resp) as mock_post:
            create_backtest(1, "c1", "bt", parameters={"lookback": 20})
            body = mock_post.call_args.kwargs["json"]
            assert body["parameters"] == {"lookback": 20}

    def test_surfaces_qc_rejection_not_empty_id(self):
        """Regression: a rejected create must raise the QC error, NOT return
        an empty backtestId (which previously forced blind retries)."""
        mock_resp = _mock_api_response(
            {"success": False, "errors": ["Backtest name already exists"]}
        )
        with patch("requests.post", return_value=mock_resp):
            with pytest.raises(RuntimeError, match="Backtest name already exists"):
                create_backtest(1, "c1", "bt")


@patch.dict("os.environ", _DUMMY_ENV)
class TestReadBacktest:
    def test_extracts_stats_from_response(self):
        mock_resp = _mock_api_response({
            "backtest": {
                "backtestId": "bt-1",
                "name": "Test",
                "status": "Completed",
                "progress": 1.0,
                "statistics": {
                    "Sharpe Ratio": "1.5",
                    "Compounding Annual Return": "15%",
                    "Drawdown": "10%",
                },
            }
        })
        with patch("requests.post", return_value=mock_resp):
            result = read_backtest(1, "bt-1")
            assert result["statistics"]["sharpeRatio"] == "1.5"
            assert result["statistics"]["compoundingAnnualReturn"] == "15%"

    def test_handles_missing_backtest_key(self):
        """QC API sometimes returns data without 'backtest' wrapper."""
        mock_resp = _mock_api_response({"backtestId": "bt-2", "status": "Running", "progress": 0.5})
        with patch("requests.post", return_value=mock_resp):
            result = read_backtest(1, "bt-2")
            assert result["backtestId"] == "bt-2"
            assert result["status"] == "Running"


@patch.dict("os.environ", _DUMMY_ENV)
class TestListBacktests:
    def test_lists_backtests(self):
        mock_resp = _mock_api_response({
            "backtests": [
                {"backtestId": "b1", "name": "Test1", "created": "2026-01-01", "status": "Completed"},
                {"backtestId": "b2", "name": "Test2", "created": "2026-01-02", "status": "Running"},
            ]
        })
        with patch("requests.post", return_value=mock_resp):
            result = list_backtests(1)
            assert result["count"] == 2
            assert result["backtests"][0]["backtestId"] == "b1"

    def test_limits_to_20(self):
        backtests = [{"backtestId": f"b{i}", "name": f"T{i}", "created": "", "status": ""} for i in range(30)]
        mock_resp = _mock_api_response({"backtests": backtests})
        with patch("requests.post", return_value=mock_resp):
            result = list_backtests(1)
            assert result["count"] == 30  # Total count
            assert len(result["backtests"]) == 20  # Capped at 20


@patch.dict("os.environ", _DUMMY_ENV)
class TestCreateProject:
    def test_returns_project_id(self):
        mock_resp = _mock_api_response({
            "projects": [{"projectId": 23456789, "name": "MyClone", "organizationId": "org1"}]
        })
        with patch("requests.post", return_value=mock_resp) as mock_post:
            result = create_project("MyClone", "Py")
            assert result["projectId"] == 23456789
            assert result["name"] == "MyClone"
            body = mock_post.call_args.kwargs["json"]
            assert body["name"] == "MyClone"
            assert body["language"] == "Py"

    def test_defaults_language_python(self):
        mock_resp = _mock_api_response({
            "projects": [{"projectId": 1, "name": "X", "organizationId": "o"}]
        })
        with patch("requests.post", return_value=mock_resp) as mock_post:
            create_project("X")
            body = mock_post.call_args.kwargs["json"]
            assert body["language"] == "Py"

    def test_surfaces_qc_rejection_not_empty_id(self):
        """Regression (cf create_backtest success:false guard): a rejected
        create must raise the QC error, NOT return projectId=0 silently — a
        zero id would block every subsequent create_file/backtest on a
        non-existent project and force blind retries."""
        mock_resp = _mock_api_response(
            {"success": False, "errors": ["Project name already exists"]}
        )
        with patch("requests.post", return_value=mock_resp):
            with pytest.raises(RuntimeError, match="Project name already exists"):
                create_project("dup")


@patch.dict("os.environ", _DUMMY_ENV)
class TestListProjects:
    def test_lists_projects(self):
        mock_resp = _mock_api_response({
            "projects": [
                {"projectId": 1, "name": "Proj1", "created": "2026-01-01", "language": "Python", "organizationId": "org1"},
            ]
        })
        with patch("requests.post", return_value=mock_resp):
            result = list_projects()
            assert result["count"] == 1
            assert result["projects"][0]["projectId"] == 1

    def test_limits_to_30(self):
        projects = [{"projectId": i, "name": f"P{i}", "created": "", "language": "", "organizationId": ""} for i in range(50)]
        mock_resp = _mock_api_response({"projects": projects})
        with patch("requests.post", return_value=mock_resp):
            result = list_projects()
            assert result["count"] == 50
            assert len(result["projects"]) == 30

    def test_total_reflects_pre_filter_count(self):
        """total = raw QC count (before name filter), count = filtered count."""
        projects = [
            {"projectId": 1, "name": "EMA-Cross", "created": "", "language": "", "organizationId": ""},
            {"projectId": 2, "name": "Momentum", "created": "", "language": "", "organizationId": ""},
        ]
        mock_resp = _mock_api_response({"projects": projects})
        with patch("requests.post", return_value=mock_resp):
            result = list_projects(name_contains="ema")
        assert result["total"] == 2
        assert result["count"] == 1
        assert result["projects"][0]["name"] == "EMA-Cross"

    def test_filter_case_insensitive(self):
        projects = [
            {"projectId": 1, "name": "FRAMEWORK_TrendWeather", "created": "", "language": "", "organizationId": ""},
            {"projectId": 2, "name": "Other", "created": "", "language": "", "organizationId": ""},
        ]
        mock_resp = _mock_api_response({"projects": projects})
        with patch("requests.post", return_value=mock_resp):
            result = list_projects(name_contains="trendweather")
        assert result["count"] == 1
        assert result["projects"][0]["projectId"] == 1


@patch.dict("os.environ", _DUMMY_ENV)
class TestReadProject:
    def test_reads_single_project(self):
        long_content = "print('hello world, this is more than 200 chars' + 'x' * 200)"
        mock_resp = _mock_api_response({
            "projects": [{
                "projectId": 42,
                "name": "MyProject",
                "description": "Test project",
                "language": "Python",
                "organizationId": "org1",
                "files": [{"name": "main.py", "content": long_content}],
            }]
        })
        with patch("requests.post", return_value=mock_resp):
            result = read_project(42)
            assert result["projectId"] == 42
            assert result["name"] == "MyProject"
            assert len(result["files"]) == 1
            # Content is truncated to 200 chars
            assert len(result["files"][0]["content"]) <= 200


@patch.dict("os.environ", _DUMMY_ENV)
class TestReadFile:
    def test_reads_specific_file(self):
        mock_resp = _mock_api_response({
            "files": [{"name": "main.py", "content": "print('hello')"}]
        })
        with patch("requests.post", return_value=mock_resp):
            result = read_file(1, "main.py")
            assert result["name"] == "main.py"
            assert result["content"] == "print('hello')"

    def test_reads_all_files(self):
        mock_resp = _mock_api_response({
            "files": [
                {"name": "main.py", "content": "code1"},
                {"name": "alpha.py", "content": "code2" * 100},
            ]
        })
        with patch("requests.post", return_value=mock_resp):
            result = read_file(1)
            assert result["count"] == 2
            assert result["files"][1]["size"] > 0


@patch.dict("os.environ", _DUMMY_ENV)
class TestUpdateFile:
    def test_update_file_contents(self):
        mock_resp = _mock_api_response({"success": True})
        with patch("requests.post", return_value=mock_resp) as mock_post:
            result = update_file_contents(1, "main.py", "new content")
            assert result["success"] is True
            assert result["name"] == "main.py"
            body = mock_post.call_args.kwargs["json"]
            assert body["content"] == "new content"


@patch.dict("os.environ", _DUMMY_ENV)
class TestCreateFile:
    def test_create_file(self):
        mock_resp = _mock_api_response({"success": True})
        with patch("requests.post", return_value=mock_resp) as mock_post:
            result = create_file(1, "new_file.py", "# new file")
            assert result["success"] is True
            body = mock_post.call_args.kwargs["json"]
            assert body["name"] == "new_file.py"
            assert body["content"] == "# new file"

    def test_create_file_empty_content(self):
        mock_resp = _mock_api_response({"success": True})
        with patch("requests.post", return_value=mock_resp) as mock_post:
            result = create_file(1, "empty.py")
            assert result["success"] is True
            body = mock_post.call_args.kwargs["json"]
            assert body["content"] == ""
