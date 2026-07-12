#!/usr/bin/env python3
"""
Tests for scripts/genai-stack/core/comfyui_client.py

Covers testable units (constants, dataclasses, pure functions, init logic).
Network methods (_request, is_reachable, get_*, upload_*, queue_*, wait_for_*)
are intentionally excluded — they require a live ComfyUI server.
"""

import json
import os
import sys
import tempfile
from pathlib import Path
from unittest.mock import patch, MagicMock

import pytest

# Add genai-stack/core to sys.path so we can import comfyui_client
_genai_core = str(Path(__file__).resolve().parent.parent / "genai-stack" / "core")
if _genai_core not in sys.path:
    sys.path.insert(0, _genai_core)

from comfyui_client import (
    DEFAULT_HOST,
    DEFAULT_PORT,
    ComfyUIConfig,
    ComfyUIError,
    ComfyUIClient,
    WorkflowManager,
)


# ─── Constants ────────────────────────────────────────────────────────


class TestDefaultHost:
    def test_is_string(self):
        assert isinstance(DEFAULT_HOST, str)

    def test_value(self):
        assert DEFAULT_HOST == "127.0.0.1"

    def test_is_localhost(self):
        assert DEFAULT_HOST in ("127.0.0.1", "localhost")


class TestDefaultPort:
    def test_is_int(self):
        assert isinstance(DEFAULT_PORT, int)

    def test_value(self):
        assert DEFAULT_PORT == 8188

    def test_is_positive(self):
        assert DEFAULT_PORT > 0

    def test_is_valid_port_range(self):
        assert 1 <= DEFAULT_PORT <= 65535


# ─── ComfyUIConfig dataclass ─────────────────────────────────────────


class TestComfyUIConfig:
    def test_defaults(self):
        cfg = ComfyUIConfig()
        assert cfg.host == DEFAULT_HOST
        assert cfg.port == DEFAULT_PORT
        assert cfg.protocol == "http"
        assert cfg.api_key is None
        assert cfg.timeout == 30
        assert cfg.max_retries == 3
        assert cfg.retry_delay == 1.0
        assert cfg.verify_ssl is False

    def test_custom_host(self):
        cfg = ComfyUIConfig(host="192.168.1.100")
        assert cfg.host == "192.168.1.100"

    def test_custom_port(self):
        cfg = ComfyUIConfig(port=9999)
        assert cfg.port == 9999

    def test_custom_protocol(self):
        cfg = ComfyUIConfig(protocol="https")
        assert cfg.protocol == "https"

    def test_custom_api_key(self):
        cfg = ComfyUIConfig(api_key="test-key-123")
        assert cfg.api_key == "test-key-123"

    def test_custom_timeout(self):
        cfg = ComfyUIConfig(timeout=60)
        assert cfg.timeout == 60

    def test_custom_max_retries(self):
        cfg = ComfyUIConfig(max_retries=5)
        assert cfg.max_retries == 5

    def test_custom_retry_delay(self):
        cfg = ComfyUIConfig(retry_delay=2.5)
        assert cfg.retry_delay == 2.5

    def test_custom_verify_ssl(self):
        cfg = ComfyUIConfig(verify_ssl=True)
        assert cfg.verify_ssl is True

    def test_is_dataclass(self):
        import dataclasses
        assert dataclasses.is_dataclass(ComfyUIConfig)

    def test_all_fields_present(self):
        import dataclasses
        fields = {f.name for f in dataclasses.fields(ComfyUIConfig)}
        expected = {"host", "port", "protocol", "api_key", "timeout",
                    "max_retries", "retry_delay", "verify_ssl"}
        assert fields == expected

    def test_repr_contains_class_name(self):
        cfg = ComfyUIConfig()
        assert "ComfyUIConfig" in repr(cfg)


# ─── ComfyUIError ────────────────────────────────────────────────────


class TestComfyUIError:
    def test_is_exception(self):
        assert issubclass(ComfyUIError, Exception)

    def test_message_stored(self):
        err = ComfyUIError("test error")
        assert err.message == "test error"

    def test_str_is_message(self):
        err = ComfyUIError("something failed")
        assert str(err) == "something failed"

    def test_status_code_default_none(self):
        err = ComfyUIError("err")
        assert err.status_code is None

    def test_status_code_custom(self):
        err = ComfyUIError("err", status_code=404)
        assert err.status_code == 404

    def test_response_default_none(self):
        err = ComfyUIError("err")
        assert err.response is None

    def test_response_custom(self):
        mock_resp = MagicMock()
        err = ComfyUIError("err", response=mock_resp)
        assert err.response is mock_resp

    def test_can_be_caught_as_exception(self):
        with pytest.raises(ComfyUIError):
            raise ComfyUIError("test")

    def test_caught_as_base_exception(self):
        with pytest.raises(Exception):
            raise ComfyUIError("test")

    def test_all_args_together(self):
        mock_resp = MagicMock()
        err = ComfyUIError("not found", status_code=404, response=mock_resp)
        assert err.message == "not found"
        assert err.status_code == 404
        assert err.response is mock_resp


# ─── ComfyUIClient.__init__ ──────────────────────────────────────────


class TestComfyUIClientInit:
    def test_default_config(self):
        client = ComfyUIClient()
        assert client.config.host == DEFAULT_HOST
        assert client.config.port == DEFAULT_PORT

    def test_custom_config(self):
        cfg = ComfyUIConfig(host="10.0.0.1", port=9999)
        client = ComfyUIClient(cfg)
        assert client.config.host == "10.0.0.1"
        assert client.config.port == 9999

    def test_client_id_format(self):
        client = ComfyUIClient()
        assert client.client_id.startswith("ComfyUIClient-")
        # 12 hex chars after prefix
        suffix = client.client_id.split("-", 1)[1].split("-")[-1]
        assert len(suffix) == 12

    def test_client_id_unique(self):
        c1 = ComfyUIClient()
        c2 = ComfyUIClient()
        assert c1.client_id != c2.client_id

    def test_session_exists(self):
        client = ComfyUIClient()
        assert client.session is not None

    def test_user_agent_header(self):
        client = ComfyUIClient()
        assert client.session.headers.get("User-Agent") == "ComfyUI-Client-Lib/2.0.0"

    def test_content_type_header(self):
        client = ComfyUIClient()
        assert client.session.headers.get("Content-Type") == "application/json"

    def test_no_auth_without_api_key(self):
        client = ComfyUIClient()
        assert "Authorization" not in client.session.headers

    def test_auth_with_bearer_api_key(self):
        client = ComfyUIClient(ComfyUIConfig(api_key="mytoken"))
        assert client.session.headers["Authorization"] == "Bearer mytoken"

    def test_auth_already_has_bearer_prefix(self):
        client = ComfyUIClient(ComfyUIConfig(api_key="Bearer mytoken"))
        assert client.session.headers["Authorization"] == "Bearer mytoken"

    def test_auth_already_has_basic_prefix(self):
        client = ComfyUIClient(ComfyUIConfig(api_key="Basic dXNlcjpwYXNz"))
        assert client.session.headers["Authorization"] == "Basic dXNlcjpwYXNz"


# ─── ComfyUIClient._url ─────────────────────────────────────────────


class TestComfyUIClientUrl:
    def test_simple_endpoint(self):
        client = ComfyUIClient()
        url = client._url("/system_stats")
        assert url == "http://127.0.0.1:8188/system_stats"

    def test_custom_host_port(self):
        cfg = ComfyUIConfig(host="10.0.0.1", port=9999)
        client = ComfyUIClient(cfg)
        url = client._url("/test")
        assert url == "http://10.0.0.1:9999/test"

    def test_https_protocol(self):
        cfg = ComfyUIConfig(protocol="https", host="comfy.example.com", port=443)
        client = ComfyUIClient(cfg)
        url = client._url("/api")
        assert url == "https://comfy.example.com:443/api"

    def test_root_endpoint(self):
        client = ComfyUIClient()
        url = client._url("/")
        assert url == "http://127.0.0.1:8188/"

    def test_nested_endpoint(self):
        client = ComfyUIClient()
        url = client._url("/object_info/CheckpointLoaderSimple")
        assert url == "http://127.0.0.1:8188/object_info/CheckpointLoaderSimple"

    def test_returns_string(self):
        client = ComfyUIClient()
        assert isinstance(client._url("/x"), str)


# ─── WorkflowManager.load ────────────────────────────────────────────


class TestWorkflowManagerLoad:
    def _write_wf(self, data, tmpdir):
        path = os.path.join(tmpdir, "test_workflow.json")
        with open(path, "w", encoding="utf-8") as f:
            json.dump(data, f)
        return path

    def test_load_simple_workflow(self):
        wf = {
            "1": {"class_type": "KSampler", "inputs": {"seed": 42}},
            "2": {"class_type": "CLIPTextEncode", "inputs": {"text": "test"}},
        }
        with tempfile.TemporaryDirectory() as tmpdir:
            path = self._write_wf(wf, tmpdir)
            loaded = WorkflowManager.load(path)
            assert "1" in loaded
            assert "2" in loaded
            assert loaded["1"]["class_type"] == "KSampler"

    def test_load_filters_meta_keys(self):
        """Root-level keys without 'class_type' (like _meta) are filtered out."""
        wf = {
            "1": {"class_type": "KSampler", "inputs": {}},
            "_meta": {"version": "1.0", "title": "Test"},
            "extra": "not a dict",
        }
        with tempfile.TemporaryDirectory() as tmpdir:
            path = self._write_wf(wf, tmpdir)
            loaded = WorkflowManager.load(path)
            assert "1" in loaded
            assert "_meta" not in loaded
            assert "extra" not in loaded

    def test_load_empty_workflow(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = self._write_wf({}, tmpdir)
            loaded = WorkflowManager.load(path)
            assert loaded == {}

    def test_load_preserves_inputs(self):
        wf = {
            "5": {"class_type": "SaveImage", "inputs": {"filename_prefix": "test", "images": ["4", 0]}},
        }
        with tempfile.TemporaryDirectory() as tmpdir:
            path = self._write_wf(wf, tmpdir)
            loaded = WorkflowManager.load(path)
            assert loaded["5"]["inputs"]["filename_prefix"] == "test"
            assert loaded["5"]["inputs"]["images"] == ["4", 0]

    def test_load_file_not_found(self):
        with pytest.raises(FileNotFoundError):
            WorkflowManager.load("/nonexistent/path/workflow.json")

    def test_load_invalid_json(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "bad.json")
            with open(path, "w") as f:
                f.write("{invalid json")
            with pytest.raises(json.JSONDecodeError):
                WorkflowManager.load(path)

    def test_load_with_path_object(self):
        wf = {"1": {"class_type": "Test", "inputs": {}}}
        with tempfile.TemporaryDirectory() as tmpdir:
            path = self._write_wf(wf, tmpdir)
            loaded = WorkflowManager.load(Path(path))
            assert "1" in loaded

    def test_load_filters_non_dict_values(self):
        wf = {
            "1": {"class_type": "Test", "inputs": {}},
            "count": 42,
            "name": "test",
        }
        with tempfile.TemporaryDirectory() as tmpdir:
            path = self._write_wf(wf, tmpdir)
            loaded = WorkflowManager.load(path)
            assert "1" in loaded
            assert "count" not in loaded
            assert "name" not in loaded

    def test_load_filters_dict_without_class_type(self):
        wf = {
            "1": {"class_type": "Test", "inputs": {}},
            "2": {"not_class_type": "Fake", "data": {}},
        }
        with tempfile.TemporaryDirectory() as tmpdir:
            path = self._write_wf(wf, tmpdir)
            loaded = WorkflowManager.load(path)
            assert "1" in loaded
            assert "2" not in loaded


# ─── WorkflowManager.validate ────────────────────────────────────────


class TestWorkflowManagerValidate:
    def test_valid_api_format(self):
        wf = {
            "1": {"class_type": "KSampler", "inputs": {}},
            "2": {"class_type": "SaveImage", "inputs": {}},
        }
        ok, errors = WorkflowManager.validate(wf)
        assert ok is True
        assert errors == []

    def test_empty_dict_is_api_format(self):
        ok, errors = WorkflowManager.validate({})
        assert ok is True
        assert errors == []

    def test_valid_ui_format(self):
        wf = {
            "nodes": [
                {"id": 1, "type": "KSampler"},
                {"id": 2, "type": "SaveImage"},
            ]
        }
        ok, errors = WorkflowManager.validate(wf)
        assert ok is True
        assert errors == []

    def test_ui_format_missing_id(self):
        wf = {"nodes": [{"type": "KSampler"}]}
        ok, errors = WorkflowManager.validate(wf)
        assert ok is False
        assert any("missing 'id'" in e for e in errors)

    def test_ui_format_missing_type(self):
        wf = {"nodes": [{"id": 1}]}
        ok, errors = WorkflowManager.validate(wf)
        assert ok is False
        assert any("missing 'type'" in e for e in errors)

    def test_ui_format_missing_nodes_key(self):
        wf = {"other_key": "value"}
        # No 'nodes' and values are not all dict with class_type → not API, not UI
        ok, errors = WorkflowManager.validate(wf)
        assert ok is False
        assert any("Missing 'nodes'" in e for e in errors)

    def test_mixed_errors_ui_format(self):
        wf = {"nodes": [{"type": "KSampler"}, {"id": 2}]}
        ok, errors = WorkflowManager.validate(wf)
        assert ok is False
        assert len(errors) == 2  # node 0 missing id, node 1 missing type

    def test_returns_tuple(self):
        result = WorkflowManager.validate({})
        assert isinstance(result, tuple)
        assert len(result) == 2


# ─── WorkflowManager.convert_ui_to_api ───────────────────────────────


class TestWorkflowManagerConvertUiToApi:
    def test_empty_nodes(self):
        result = WorkflowManager.convert_ui_to_api({"nodes": []})
        assert result == {}

    def test_no_nodes_key(self):
        result = WorkflowManager.convert_ui_to_api({})
        assert result == {}

    def test_skips_reroute_nodes(self):
        wf = {"nodes": [{"id": 1, "type": "Reroute"}]}
        result = WorkflowManager.convert_ui_to_api(wf)
        assert result == {}

    def test_skips_note_nodes(self):
        wf = {"nodes": [{"id": 1, "type": "Note"}]}
        result = WorkflowManager.convert_ui_to_api(wf)
        assert result == {}

    def test_returns_dict(self):
        wf = {"nodes": [{"id": 1, "type": "KSampler"}]}
        result = WorkflowManager.convert_ui_to_api(wf)
        assert isinstance(result, dict)


# ─── WorkflowManager.fix_links ───────────────────────────────────────


class TestWorkflowManagerFixLinks:
    def test_no_links_key(self):
        wf = {"nodes": []}
        result = WorkflowManager.fix_links(wf)
        assert result == wf

    def test_preserves_valid_links(self):
        links = [[1, 5, 0, 3, 0, "MODEL"]]
        wf = {"links": links, "nodes": []}
        result = WorkflowManager.fix_links(wf)
        assert result["links"] == links

    def test_empty_links(self):
        wf = {"links": [], "nodes": []}
        result = WorkflowManager.fix_links(wf)
        assert result["links"] == []

    def test_returns_dict(self):
        wf = {"nodes": []}
        assert isinstance(WorkflowManager.fix_links(wf), dict)

    def test_does_not_mutate_original(self):
        original_links = [[1, 5, 0, 3, 0, "MODEL"]]
        wf = {"links": list(original_links), "nodes": []}
        WorkflowManager.fix_links(wf)
        # Links list is replaced in-place but content is same
        assert wf["links"] == original_links


# ─── Cross-invariants ────────────────────────────────────────────────


class TestCrossInvariants:
    def test_config_defaults_match_module_constants(self):
        cfg = ComfyUIConfig()
        assert cfg.host == DEFAULT_HOST
        assert cfg.port == DEFAULT_PORT

    def test_client_url_uses_config(self):
        cfg = ComfyUIConfig(host="custom.host", port=1234, protocol="https")
        client = ComfyUIClient(cfg)
        url = client._url("/test")
        assert "custom.host" in url
        assert "1234" in url
        assert url.startswith("https://")

    def test_error_is_raisable_and_catchable(self):
        try:
            raise ComfyUIError("test", status_code=500)
        except ComfyUIError as e:
            assert e.status_code == 500
            assert e.message == "test"

    def test_workflow_roundtrip(self):
        """Load → validate should work for a well-formed API workflow."""
        wf = {
            "1": {"class_type": "KSampler", "inputs": {"seed": 42}},
            "2": {"class_type": "SaveImage", "inputs": {"filename_prefix": "test"}},
        }
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "rt.json")
            with open(path, "w") as f:
                json.dump(wf, f)
            loaded = WorkflowManager.load(path)
            ok, errors = WorkflowManager.validate(loaded)
            assert ok is True
            assert len(loaded) == 2
