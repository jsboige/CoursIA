"""Tests for genai-stack comfyui_client.py — WorkflowManager static methods + _url."""

import importlib.util
import sys
from pathlib import Path

import pytest

# Load module by file path to avoid sys.path issues
_MOD_PATH = Path(__file__).resolve().parent.parent.parent / "genai-stack" / "core" / "comfyui_client.py"
_spec = importlib.util.spec_from_file_location("comfyui_client", _MOD_PATH)
_mod = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_mod)

ComfyUIConfig = _mod.ComfyUIConfig
ComfyUIClient = _mod.ComfyUIClient
ComfyUIError = _mod.ComfyUIError
WorkflowManager = _mod.WorkflowManager


# --- ComfyUIConfig defaults ---


class TestComfyUIConfig:
    def test_default_host(self):
        cfg = ComfyUIConfig()
        assert cfg.host == "127.0.0.1"

    def test_default_port(self):
        cfg = ComfyUIConfig()
        assert cfg.port == 8188

    def test_default_protocol(self):
        cfg = ComfyUIConfig()
        assert cfg.protocol == "http"

    def test_custom_config(self):
        cfg = ComfyUIConfig(host="192.168.1.100", port=9999, protocol="https")
        assert cfg.host == "192.168.1.100"
        assert cfg.port == 9999
        assert cfg.protocol == "https"


# --- ComfyUIClient._url ---


class TestClientUrl:
    def test_default_url(self):
        client = ComfyUIClient()
        assert client._url("/system_stats") == "http://127.0.0.1:8188/system_stats"

    def test_custom_host_port(self):
        cfg = ComfyUIConfig(host="10.0.0.1", port=9090)
        client = ComfyUIClient(config=cfg)
        assert client._url("/prompt") == "http://10.0.0.1:9090/prompt"

    def test_https_protocol(self):
        cfg = ComfyUIConfig(protocol="https", host="comfy.example.com", port=443)
        client = ComfyUIClient(config=cfg)
        assert client._url("/api/test") == "https://comfy.example.com:443/api/test"

    def test_root_endpoint(self):
        client = ComfyUIClient()
        assert client._url("/") == "http://127.0.0.1:8188/"


# --- WorkflowManager.validate ---


class TestWorkflowValidate:
    def test_api_format_valid(self):
        """API format: dict of nodes with class_type keys → valid."""
        workflow = {
            "3": {"class_type": "KSampler", "inputs": {"steps": 20}},
            "5": {"class_type": "CLIPTextEncode", "inputs": {"text": "cat"}},
        }
        valid, errors = WorkflowManager.validate(workflow)
        assert valid is True
        assert errors == []

    def test_ui_format_valid(self):
        """UI format: has 'nodes' list with id and type → valid."""
        workflow = {
            "nodes": [
                {"id": 1, "type": "KSampler"},
                {"id": 2, "type": "CLIPTextEncode"},
            ]
        }
        valid, errors = WorkflowManager.validate(workflow)
        assert valid is True
        assert errors == []

    def test_ui_format_missing_nodes(self):
        """No 'nodes' list and not API format → invalid."""
        workflow = {"something": "else"}
        valid, errors = WorkflowManager.validate(workflow)
        assert valid is False
        assert any("Missing 'nodes'" in e for e in errors)

    def test_ui_format_node_missing_id(self):
        workflow = {"nodes": [{"type": "KSampler"}]}
        valid, errors = WorkflowManager.validate(workflow)
        assert valid is False
        assert any("missing 'id'" in e for e in errors)

    def test_ui_format_node_missing_type(self):
        workflow = {"nodes": [{"id": 1}]}
        valid, errors = WorkflowManager.validate(workflow)
        assert valid is False
        assert any("missing 'type'" in e for e in errors)

    def test_empty_dict_treated_as_api(self):
        """Empty dict: no 'nodes' key, all values pass isinstance check (vacuously true) → API format."""
        workflow = {}
        valid, errors = WorkflowManager.validate(workflow)
        assert valid is True

    def test_ui_format_multiple_errors(self):
        workflow = {"nodes": [{}, {}]}
        valid, errors = WorkflowManager.validate(workflow)
        assert valid is False
        # 2 nodes × 2 missing fields = 4 errors
        assert len(errors) == 4


# --- WorkflowManager.convert_ui_to_api ---


class TestConvertUiToApi:
    def test_skips_reroute_nodes(self):
        """Reroute nodes are filtered out. KSampler node is processed but
        convert_ui_to_api is a placeholder that never populates api_workflow
        (pass statement at L245). Result is always {} for non-Reroute/Note nodes."""
        workflow = {
            "nodes": [
                {"type": "Reroute", "id": 1},
                {"type": "KSampler", "id": 2},
            ]
        }
        result = WorkflowManager.convert_ui_to_api(workflow)
        # Placeholder implementation: api_node created but never added to dict
        assert len(result) == 0

    def test_skips_note_nodes(self):
        workflow = {
            "nodes": [
                {"type": "Note", "id": 1},
            ]
        }
        result = WorkflowManager.convert_ui_to_api(workflow)
        assert len(result) == 0

    def test_empty_workflow(self):
        workflow = {"nodes": []}
        result = WorkflowManager.convert_ui_to_api(workflow)
        assert result == {}

    def test_no_nodes_key(self):
        workflow = {}
        result = WorkflowManager.convert_ui_to_api(workflow)
        assert result == {}


# --- WorkflowManager.fix_links ---


class TestFixLinks:
    def test_no_links_key(self):
        """Workflow without 'links' key → returned unchanged."""
        workflow = {"nodes": [{"id": 1}]}
        result = WorkflowManager.fix_links(workflow)
        assert result == workflow

    def test_valid_links_preserved(self):
        """Valid links are kept as-is."""
        link = [1, 5, 0, 3, 1, "NORMAL"]
        workflow = {"links": [link], "nodes": []}
        result = WorkflowManager.fix_links(workflow)
        assert link in result["links"]

    def test_short_link_kept(self):
        """Short 2-element links are kept (function doesn't transform them)."""
        link = [10, 20]
        workflow = {"links": [link], "nodes": []}
        result = WorkflowManager.fix_links(workflow)
        assert link in result["links"]

    def test_empty_links_list(self):
        workflow = {"links": [], "nodes": []}
        result = WorkflowManager.fix_links(workflow)
        assert result["links"] == []

    def test_multiple_links(self):
        links = [
            [1, 5, 0, 3, 1, "NORMAL"],
            [2, 6, 0, 4, 0, "NORMAL"],
        ]
        workflow = {"links": links, "nodes": []}
        result = WorkflowManager.fix_links(workflow)
        assert len(result["links"]) == 2

    def test_non_list_links_handled(self):
        """Non-list entries in links are still appended."""
        workflow = {"links": ["bad_link", [1, 2, 3, 4, 5, 6]], "nodes": []}
        result = WorkflowManager.fix_links(workflow)
        assert len(result["links"]) == 2


# --- ComfyUIError ---


class TestComfyUIError:
    def test_error_message(self):
        err = ComfyUIError("test error")
        assert str(err) == "test error"
        assert err.message == "test error"

    def test_error_with_status(self):
        err = ComfyUIError("not found", status_code=404)
        assert err.status_code == 404

    def test_is_exception(self):
        with pytest.raises(ComfyUIError):
            raise ComfyUIError("boom")


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
