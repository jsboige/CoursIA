"""Tests for scripts/notebook_tools/exec_single_cell.py — single-cell executor.

Tests focus on pure functions: _source, _is_dotnet_bootstrap, collect_outputs.
No live kernel required — kernel client is mocked for collect_outputs tests.
"""

import queue
import sys
from pathlib import Path
from unittest.mock import MagicMock

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from exec_single_cell import _source, _is_dotnet_bootstrap, collect_outputs


# ---------------------------------------------------------------------------
# _source
# ---------------------------------------------------------------------------

class TestSource:
    def test_list_source(self):
        """List of strings is joined."""
        cell = {"source": ["print('hello')\n", "x = 1\n"]}
        assert _source(cell) == "print('hello')\nx = 1\n"

    def test_string_source(self):
        """Plain string source is returned as-is."""
        cell = {"source": "print('hello')\nx = 1\n"}
        assert _source(cell) == "print('hello')\nx = 1\n"

    def test_empty_list_source(self):
        """Empty list returns empty string."""
        cell = {"source": []}
        assert _source(cell) == ""

    def test_empty_string_source(self):
        """Empty string returns empty string."""
        cell = {"source": ""}
        assert _source(cell) == ""

    def test_single_line_list(self):
        """Single-element list."""
        cell = {"source": ["x = 42"]}
        assert _source(cell) == "x = 42"

    def test_multiline_string(self):
        """Multi-line string source."""
        src = "line1\nline2\nline3"
        cell = {"source": src}
        assert _source(cell) == src

    def test_missing_source_key(self):
        """Missing source key raises KeyError."""
        cell = {}
        with pytest.raises(KeyError):
            _source(cell)


# ---------------------------------------------------------------------------
# _is_dotnet_bootstrap
# ---------------------------------------------------------------------------

class TestIsDotnetBootstrap:
    def test_display_data_with_dotnet_interactive(self):
        """display_data containing dotnet-interactive marker = bootstrap."""
        output = {
            "output_type": "display_data",
            "data": {"text/html": '<div class="dotnet-interactive-this-cell">...</div>'},
        }
        assert _is_dotnet_bootstrap(output) is True

    def test_display_data_with_httpport(self):
        """display_data containing HttpPort = bootstrap."""
        output = {
            "output_type": "display_data",
            "data": {"text/html": "<div>HttpPort: 44528</div>"},
        }
        assert _is_dotnet_bootstrap(output) is True

    def test_execute_result_with_bootstrap(self):
        """execute_result with dotnet marker = bootstrap."""
        output = {
            "output_type": "execute_result",
            "data": {"text/html": '<div class="dotnet-interactive-this-cell">'},
        }
        assert _is_dotnet_bootstrap(output) is True

    def test_display_data_normal(self):
        """display_data without dotnet markers = not bootstrap."""
        output = {
            "output_type": "display_data",
            "data": {"text/html": "<p>Hello world</p>"},
        }
        assert _is_dotnet_bootstrap(output) is False

    def test_stream_output(self):
        """stream output is never bootstrap."""
        output = {"output_type": "stream", "name": "stdout", "text": "hello"}
        assert _is_dotnet_bootstrap(output) is False

    def test_error_output(self):
        """error output is never bootstrap."""
        output = {
            "output_type": "error",
            "ename": "RuntimeError",
            "evalue": "test",
            "traceback": [],
        }
        assert _is_dotnet_bootstrap(output) is False

    def test_html_as_list_with_marker(self):
        """text/html as list of strings with dotnet marker."""
        output = {
            "output_type": "display_data",
            "data": {"text/html": ["<div>", "dotnet-interactive-this-cell", "</div>"]},
        }
        assert _is_dotnet_bootstrap(output) is True

    def test_html_as_list_without_marker(self):
        """text/html as list without dotnet marker."""
        output = {
            "output_type": "display_data",
            "data": {"text/html": ["<p>", "normal output", "</p>"]},
        }
        assert _is_dotnet_bootstrap(output) is False

    def test_no_data_key(self):
        """Missing data key = not bootstrap."""
        output = {"output_type": "display_data"}
        assert _is_dotnet_bootstrap(output) is False

    def test_empty_html(self):
        """Empty HTML = not bootstrap."""
        output = {
            "output_type": "display_data",
            "data": {"text/html": ""},
        }
        assert _is_dotnet_bootstrap(output) is False

    def test_no_html_key_in_data(self):
        """No text/html in data = not bootstrap."""
        output = {
            "output_type": "display_data",
            "data": {"text/plain": "hello"},
        }
        assert _is_dotnet_bootstrap(output) is False


# ---------------------------------------------------------------------------
# collect_outputs (mocked kernel client)
# ---------------------------------------------------------------------------

def _make_msg(msg_type, content, msg_id="test-msg-001"):
    """Build a fake iopub message."""
    return {
        "parent_header": {"msg_id": msg_id},
        "msg_type": msg_type,
        "content": content,
    }


class TestCollectOutputs:
    def _mock_kc(self, messages, msg_id="test-msg-001"):
        """Build a mock kernel client that yields the given messages."""
        kc = MagicMock()

        def side_effect(timeout=None):
            if not messages:
                raise queue.Empty()
            return messages.pop(0)

        kc.get_iopub_msg = MagicMock(side_effect=side_effect)
        return kc

    def test_stream_output(self):
        """Stream messages become stream outputs."""
        msgs = [
            _make_msg("execute_input", {"execution_count": 1, "code": "print('hi')"}),
            _make_msg("stream", {"name": "stdout", "text": "hi\n"}),
            _make_msg("status", {"execution_state": "idle"}),
        ]
        kc = self._mock_kc(msgs)
        outputs, ec = collect_outputs(kc, "test-msg-001", timeout=5)
        assert ec == 1
        assert len(outputs) == 1
        assert outputs[0]["output_type"] == "stream"
        assert outputs[0]["name"] == "stdout"
        assert outputs[0]["text"] == "hi\n"

    def test_execute_result(self):
        """execute_result message produces output with execution_count."""
        msgs = [
            _make_msg("execute_input", {"execution_count": 2, "code": "1+1"}),
            _make_msg("execute_result", {
                "execution_count": 2,
                "data": {"text/plain": "2"},
                "metadata": {},
            }),
            _make_msg("status", {"execution_state": "idle"}),
        ]
        kc = self._mock_kc(msgs)
        outputs, ec = collect_outputs(kc, "test-msg-001", timeout=5)
        assert ec == 2
        assert len(outputs) == 1
        assert outputs[0]["output_type"] == "execute_result"
        assert outputs[0]["data"]["text/plain"] == "2"

    def test_error_output(self):
        """Error messages become error outputs."""
        msgs = [
            _make_msg("execute_input", {"execution_count": 1, "code": "1/0"}),
            _make_msg("error", {
                "ename": "ZeroDivisionError",
                "evalue": "division by zero",
                "traceback": ["ZeroDivisionError: division by zero"],
            }),
            _make_msg("status", {"execution_state": "idle"}),
        ]
        kc = self._mock_kc(msgs)
        outputs, ec = collect_outputs(kc, "test-msg-001", timeout=5)
        assert len(outputs) == 1
        assert outputs[0]["output_type"] == "error"
        assert outputs[0]["ename"] == "ZeroDivisionError"

    def test_display_data(self):
        """display_data messages are captured."""
        msgs = [
            _make_msg("display_data", {
                "data": {"text/html": "<b>bold</b>"},
                "metadata": {},
            }),
            _make_msg("status", {"execution_state": "idle"}),
        ]
        kc = self._mock_kc(msgs)
        outputs, ec = collect_outputs(kc, "test-msg-001", timeout=5)
        assert len(outputs) == 1
        assert outputs[0]["output_type"] == "display_data"

    def test_filters_dotnet_bootstrap(self):
        """dotnet-interactive bootstrap outputs are filtered out."""
        msgs = [
            _make_msg("display_data", {
                "data": {"text/html": '<div class="dotnet-interactive-this-cell">...</div>'},
                "metadata": {},
            }),
            _make_msg("stream", {"name": "stdout", "text": "real output"}),
            _make_msg("status", {"execution_state": "idle"}),
        ]
        kc = self._mock_kc(msgs)
        outputs, ec = collect_outputs(kc, "test-msg-001", timeout=5)
        assert len(outputs) == 1
        assert outputs[0]["output_type"] == "stream"

    def test_ignores_other_parent_msgs(self):
        """Messages from other parents are skipped."""
        msgs = [
            {"parent_header": {"msg_id": "other-msg"}, "msg_type": "stream",
             "content": {"name": "stdout", "text": "ignored"}},
            _make_msg("stream", {"name": "stdout", "text": "real"}),
            _make_msg("status", {"execution_state": "idle"}),
        ]
        kc = self._mock_kc(msgs)
        outputs, ec = collect_outputs(kc, "test-msg-001", timeout=5)
        assert len(outputs) == 1
        assert outputs[0]["text"] == "real"

    def test_empty_timeout(self):
        """Empty queue (timeout) returns empty outputs."""
        kc = MagicMock()
        kc.get_iopub_msg = MagicMock(side_effect=queue.Empty())
        outputs, ec = collect_outputs(kc, "test-msg-001", timeout=1)
        assert outputs == []
        assert ec is None

    def test_mixed_outputs(self):
        """Multiple output types in sequence."""
        msgs = [
            _make_msg("execute_input", {"execution_count": 3, "code": "code"}),
            _make_msg("stream", {"name": "stdout", "text": "hello"}),
            _make_msg("display_data", {"data": {"text/plain": "chart"}, "metadata": {}}),
            _make_msg("execute_result", {
                "execution_count": 3,
                "data": {"text/plain": "42"},
                "metadata": {},
            }),
            _make_msg("status", {"execution_state": "idle"}),
        ]
        kc = self._mock_kc(msgs)
        outputs, ec = collect_outputs(kc, "test-msg-001", timeout=5)
        assert ec == 3
        assert len(outputs) == 3
        assert outputs[0]["output_type"] == "stream"
        assert outputs[1]["output_type"] == "display_data"
        assert outputs[2]["output_type"] == "execute_result"

    def test_status_busy_ignored(self):
        """status:busy messages don't produce outputs."""
        msgs = [
            _make_msg("status", {"execution_state": "busy"}),
            _make_msg("stream", {"name": "stdout", "text": "ok"}),
            _make_msg("status", {"execution_state": "idle"}),
        ]
        kc = self._mock_kc(msgs)
        outputs, ec = collect_outputs(kc, "test-msg-001", timeout=5)
        assert len(outputs) == 1
        assert outputs[0]["text"] == "ok"

    def test_multiple_streams(self):
        """Multiple stream outputs (stdout + stderr)."""
        msgs = [
            _make_msg("stream", {"name": "stdout", "text": "out"}),
            _make_msg("stream", {"name": "stderr", "text": "err"}),
            _make_msg("status", {"execution_state": "idle"}),
        ]
        kc = self._mock_kc(msgs)
        outputs, ec = collect_outputs(kc, "test-msg-001", timeout=5)
        assert len(outputs) == 2
        assert outputs[0]["name"] == "stdout"
        assert outputs[1]["name"] == "stderr"

    def test_execute_result_metadata_preserved(self):
        """execute_result output preserves metadata from the message."""
        msgs = [
            _make_msg("execute_result", {
                "execution_count": 1,
                "data": {"text/plain": "result"},
                "metadata": {"custom_key": "custom_value"},
            }),
            _make_msg("status", {"execution_state": "idle"}),
        ]
        kc = self._mock_kc(msgs)
        outputs, ec = collect_outputs(kc, "test-msg-001", timeout=5)
        assert outputs[0]["metadata"]["custom_key"] == "custom_value"

    def test_error_traceback_preserved(self):
        """Error output preserves the full traceback list."""
        msgs = [
            _make_msg("error", {
                "ename": "ValueError",
                "evalue": "bad value",
                "traceback": ["line1", "ValueError: bad value"],
            }),
            _make_msg("status", {"execution_state": "idle"}),
        ]
        kc = self._mock_kc(msgs)
        outputs, ec = collect_outputs(kc, "test-msg-001", timeout=5)
        assert outputs[0]["traceback"] == ["line1", "ValueError: bad value"]
