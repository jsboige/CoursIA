"""Tests for exec_single_cell.py — single cell execution helpers."""

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).parent.parent))
from exec_single_cell import _source, _is_dotnet_bootstrap


# --- _source ---


class TestSource:
    def test_list_source_joined(self):
        cell = {"source": ["line1\n", "line2\n", "line3"]}
        assert _source(cell) == "line1\nline2\nline3"

    def test_string_source_passthrough(self):
        cell = {"source": "x = 1\ny = 2"}
        assert _source(cell) == "x = 1\ny = 2"

    def test_empty_list(self):
        cell = {"source": []}
        assert _source(cell) == ""

    def test_single_item_list(self):
        cell = {"source": ["only line"]}
        assert _source(cell) == "only line"

    def test_missing_source_key(self):
        cell = {}
        with pytest.raises(KeyError):
            _source(cell)


# --- _is_dotnet_bootstrap ---


class TestIsDotnetBootstrap:
    def test_normal_execute_result_not_bootstrap(self):
        output = {
            "output_type": "execute_result",
            "data": {"text/plain": "42"},
            "metadata": {},
        }
        assert _is_dotnet_bootstrap(output) is False

    def test_normal_stream_not_bootstrap(self):
        output = {
            "output_type": "stream",
            "name": "stdout",
            "text": "hello",
        }
        assert _is_dotnet_bootstrap(output) is False

    def test_dotnet_interactive_div_detected(self):
        output = {
            "output_type": "display_data",
            "data": {
                "text/html": "<div class='dotnet-interactive-this-cell'>port info</div>",
            },
            "metadata": {},
        }
        assert _is_dotnet_bootstrap(output) is True

    def test_http_port_detected(self):
        output = {
            "output_type": "execute_result",
            "data": {
                "text/html": "<div>HttpPort=44528</div>",
            },
            "metadata": {},
        }
        assert _is_dotnet_bootstrap(output) is True

    def test_html_as_list(self):
        output = {
            "output_type": "display_data",
            "data": {
                "text/html": ["<div>", "dotnet-interactive-this-cell", "</div>"],
            },
            "metadata": {},
        }
        assert _is_dotnet_bootstrap(output) is True

    def test_normal_html_not_bootstrap(self):
        output = {
            "output_type": "display_data",
            "data": {
                "text/html": "<h1>Results</h1>",
            },
            "metadata": {},
        }
        assert _is_dotnet_bootstrap(output) is False

    def test_error_output_not_bootstrap(self):
        output = {
            "output_type": "error",
            "ename": "RuntimeError",
            "evalue": "fail",
            "traceback": [],
        }
        assert _is_dotnet_bootstrap(output) is False

    def test_no_data_key(self):
        output = {
            "output_type": "display_data",
            "metadata": {},
        }
        assert _is_dotnet_bootstrap(output) is False

    def test_html_as_empty_list(self):
        output = {
            "output_type": "display_data",
            "data": {"text/html": []},
            "metadata": {},
        }
        assert _is_dotnet_bootstrap(output) is False
