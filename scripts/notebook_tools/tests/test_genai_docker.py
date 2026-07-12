"""Tests for genai-stack commands/docker.py — DockerManager offline with mocked subprocess/requests."""

import importlib.util
import json
import subprocess
import sys
import types
from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest

# --- Load docker.py ---
_DK_PATH = Path(__file__).resolve().parent.parent.parent / "genai-stack" / "commands" / "docker.py"
_dk_spec = importlib.util.spec_from_file_location("docker_cmd", _DK_PATH)
_dk_mod = importlib.util.module_from_spec(_dk_spec)

# Stub config dependencies before loading
_mock_services = {
    "whisper-api": {
        "container_name": "test-whisper",
        "port": 8190,
        "health_endpoint": "/health",
        "remote_url": "http://whisper.example.com",
        "compose_dir": Path("/tmp/compose/whisper"),
        "gpu_id": 1,
        "vram_required": "2GB",
        "auth_type": "none",
    },
    "comfyui-qwen": {
        "container_name": "test-comfyui",
        "port": 8188,
        "health_endpoint": "/system_stats",
        "remote_url": "http://comfyui.example.com",
        "compose_dir": Path("/tmp/compose/comfyui"),
        "gpu_id": 0,
        "vram_required": "8GB",
        "auth_type": "bearer",
        "auth_env_var": "COMFYUI_BEARER_TOKEN",
    },
    "tts-api": {
        "container_name": "test-tts",
        "port": 8197,
        "health_endpoint": "/v1/health",
        "remote_url": "http://tts.example.com",
        "compose_dir": Path("/tmp/compose/tts"),
        "gpu_id": 1,
        "vram_required": "4GB",
        "auth_type": "basic",
        "auth_env_vars": ["BASIC_USER", "BASIC_PASS"],
    },
}
_mock_config = types.SimpleNamespace(
    SERVICES=_mock_services,
    GPU_PROFILES={},
    GROUP_GPU_PROFILE={},
    load_env=lambda: {
        "COMFYUI_BEARER_TOKEN": "test-token-123",
        "BASIC_USER": "admin",
        "BASIC_PASS": "changeme",
    },
)

# Inject mock config into sys.modules so docker.py `from config import ...` resolves.
# Save the previous binding so we can RESTORE it afterwards (not just delete).
# Blindly popping the key nukes a real `config` module that a sibling test
# already imported (e.g. test_genai_config.py when both run together), leaving
# `from config import ...` broken for the rest of the session — collection-order
# flakiness observed under Ubuntu CI (#2871 part 2).
_prev_config = sys.modules.get("config")
sys.modules["config"] = _mock_config
_dk_spec.loader.exec_module(_dk_mod)

# Restore the prior binding (or remove the key if there was none).
if _prev_config is not None:
    sys.modules["config"] = _prev_config
else:
    sys.modules.pop("config", None)

DockerManager = _dk_mod.DockerManager
_run_cmd = _dk_mod._run_cmd


# ============================================================================
# Tests for _run_cmd helper
# ============================================================================


class TestRunCmd:
    """Tests for _run_cmd() — subprocess wrapper."""

    def test_success(self):
        result = _run_cmd(["echo", "hello"])
        assert result.returncode == 0
        assert "hello" in result.stdout

    def test_failure(self):
        result = _run_cmd(["false"])
        assert result.returncode != 0

    def test_timeout_returns_failure(self):
        """_run_cmd catches TimeoutExpired and returns failure."""
        with patch("subprocess.run", side_effect=subprocess.TimeoutExpired(cmd=["sleep", "10"], timeout=0.01)):
            result = _run_cmd(["sleep", "10"], timeout=0.01)
        assert result.returncode == 1
        assert "Timeout" in result.stderr

    def test_exception_returns_failure(self):
        """_run_cmd catches generic exceptions."""
        with patch("subprocess.run", side_effect=OSError("mock error")):
            result = _run_cmd(["nonexistent-cmd"])
        assert result.returncode == 1
        assert "mock error" in result.stderr

    def test_cwd_forwarded(self):
        """cwd parameter is passed to subprocess.run."""
        with patch("subprocess.run") as mock_run:
            mock_run.return_value = subprocess.CompletedProcess(["test"], 0, "ok", "")
            _run_cmd(["test"], cwd=Path("/tmp"))
            _, kwargs = mock_run.call_args
            # On Windows, Path("/tmp") stringifies to backslash form
            assert str(kwargs["cwd"]).replace("\\", "/") == "/tmp"

    def test_capture_false(self):
        """capture=False passes capture_output=False."""
        with patch("subprocess.run") as mock_run:
            mock_run.return_value = subprocess.CompletedProcess(["test"], 0, "", "")
            _run_cmd(["test"], capture=False)
            _, kwargs = mock_run.call_args
            assert kwargs["capture_output"] is False


# ============================================================================
# Tests for DockerManager.get_container_status
# ============================================================================


class TestGetContainerStatus:
    """Tests for DockerManager.get_container_status()."""

    def test_unknown_service(self):
        mgr = DockerManager()
        result = mgr.get_container_status("nonexistent-service")
        assert result["status"] == "unknown"
        assert result["running"] is False

    def test_not_found_container(self):
        mgr = DockerManager()
        with patch.object(_dk_mod, "_run_cmd", return_value=subprocess.CompletedProcess(["docker"], 1, "", "not found")):
            result = mgr.get_container_status("whisper-api")
        assert result["status"] == "not_found"
        assert result["running"] is False

    def test_running_container(self):
        mgr = DockerManager()
        inspect_output = json.dumps([{
            "State": {
                "Status": "running",
                "Running": True,
                "StartedAt": "2026-01-01T00:00:00Z",
                "Health": {"Status": "healthy"},
            }
        }])
        with patch.object(_dk_mod, "_run_cmd", return_value=subprocess.CompletedProcess(["docker"], 0, inspect_output, "")):
            result = mgr.get_container_status("whisper-api")
        assert result["status"] == "running"
        assert result["running"] is True
        assert result["health"] == "healthy"

    def test_stopped_container(self):
        mgr = DockerManager()
        inspect_output = json.dumps([{
            "State": {
                "Status": "exited",
                "Running": False,
                "StartedAt": None,
                "Health": {"Status": "unknown"},
            }
        }])
        with patch.object(_dk_mod, "_run_cmd", return_value=subprocess.CompletedProcess(["docker"], 0, inspect_output, "")):
            result = mgr.get_container_status("whisper-api")
        assert result["status"] == "exited"
        assert result["running"] is False

    def test_malformed_json(self):
        mgr = DockerManager()
        with patch.object(_dk_mod, "_run_cmd", return_value=subprocess.CompletedProcess(["docker"], 0, "not json", "")):
            result = mgr.get_container_status("whisper-api")
        assert result["status"] == "error"
        assert result["running"] is False

    def test_missing_health_key(self):
        """Container without Health field returns 'unknown' health."""
        mgr = DockerManager()
        inspect_output = json.dumps([{
            "State": {"Status": "running", "Running": True, "StartedAt": "2026-01-01T00:00:00Z"},
        }])
        with patch.object(_dk_mod, "_run_cmd", return_value=subprocess.CompletedProcess(["docker"], 0, inspect_output, "")):
            result = mgr.get_container_status("whisper-api")
        assert result["status"] == "running"
        assert result["health"] == "unknown"


# ============================================================================
# Tests for DockerManager.check_service_health
# ============================================================================


class TestCheckServiceHealth:
    """Tests for DockerManager.check_service_health() — HTTP health checks."""

    def test_unknown_service(self):
        mgr = DockerManager()
        ok, msg = mgr.check_service_health("nonexistent-service")
        assert ok is False
        assert "inconnu" in msg.lower()

    def test_healthy_no_auth(self):
        mgr = DockerManager()
        mock_resp = MagicMock()
        mock_resp.status_code = 200

        with patch.object(_dk_mod.requests, "get", return_value=mock_resp):
            ok, msg = mgr.check_service_health("whisper-api")
        assert ok is True
        assert "OK" in msg

    def test_auth_required(self):
        mgr = DockerManager()
        mock_resp = MagicMock()
        mock_resp.status_code = 401

        with patch.object(_dk_mod.requests, "get", return_value=mock_resp):
            ok, msg = mgr.check_service_health("whisper-api")
        assert ok is False
        assert "401" in msg

    def test_connection_refused(self):
        mgr = DockerManager()
        with patch.object(_dk_mod.requests, "get", side_effect=_dk_mod.requests.exceptions.ConnectionError("refused")):
            ok, msg = mgr.check_service_health("whisper-api")
        assert ok is False
        assert "Connection refused" in msg

    def test_timeout(self):
        mgr = DockerManager()
        with patch.object(_dk_mod.requests, "get", side_effect=_dk_mod.requests.exceptions.Timeout("timed out")):
            ok, msg = mgr.check_service_health("whisper-api")
        assert ok is False
        assert "Timeout" in msg

    def test_bearer_auth_header(self):
        """Bearer token service sends Authorization header."""
        mgr = DockerManager()
        mock_resp = MagicMock()
        mock_resp.status_code = 200

        with patch.object(_dk_mod.requests, "get", return_value=mock_resp) as mock_get:
            ok, msg = mgr.check_service_health("comfyui-qwen")
            # Verify Authorization header was sent
            call_kwargs = mock_get.call_args
            headers = call_kwargs[1].get("headers", {}) if len(call_kwargs) > 1 else call_kwargs.kwargs.get("headers", {})
            assert "Authorization" in headers
            assert headers["Authorization"].startswith("Bearer ")
        assert ok is True

    def test_basic_auth(self):
        """Basic auth service sends auth tuple."""
        mgr = DockerManager()
        mock_resp = MagicMock()
        mock_resp.status_code = 200

        with patch.object(_dk_mod.requests, "get", return_value=mock_resp) as mock_get:
            ok, msg = mgr.check_service_health("tts-api")
            call_kwargs = mock_get.call_args
            auth = call_kwargs[1].get("auth", None) if len(call_kwargs) > 1 else call_kwargs.kwargs.get("auth", None)
            assert auth is not None
            assert auth == ("admin", "changeme")
        assert ok is True

    def test_remote_url(self):
        """use_remote=True uses remote_url instead of localhost."""
        mgr = DockerManager()
        mock_resp = MagicMock()
        mock_resp.status_code = 200

        with patch.object(_dk_mod.requests, "get", return_value=mock_resp) as mock_get:
            mgr.check_service_health("whisper-api", use_remote=True)
            url = mock_get.call_args[0][0]
            assert "whisper.example.com" in url

    def test_other_http_error(self):
        mgr = DockerManager()
        mock_resp = MagicMock()
        mock_resp.status_code = 500

        with patch.object(_dk_mod.requests, "get", return_value=mock_resp):
            ok, msg = mgr.check_service_health("whisper-api")
        assert ok is False
        assert "500" in msg


# ============================================================================
# Tests for DockerManager.start_service / stop_service / restart_service
# ============================================================================


class TestStartStopService:
    """Tests for start/stop/restart — subprocess mock."""

    def test_start_unknown_service(self):
        mgr = DockerManager()
        assert mgr.start_service("nonexistent-service") is False

    def test_start_known_service_success(self):
        mgr = DockerManager()
        with patch.object(Path, "exists", return_value=True):
            with patch.object(_dk_mod, "_run_cmd", return_value=subprocess.CompletedProcess(["docker"], 0, "", "")):
                with patch.object(_dk_mod, "COMPOSE_CMD", ["docker", "compose"]):
                    result = mgr.start_service("whisper-api")
        assert result is True

    def test_start_known_service_failure(self):
        mgr = DockerManager()
        with patch.object(Path, "exists", return_value=True):
            with patch.object(_dk_mod, "_run_cmd", return_value=subprocess.CompletedProcess(["docker"], 1, "", "error")):
                with patch.object(_dk_mod, "COMPOSE_CMD", ["docker", "compose"]):
                    result = mgr.start_service("whisper-api")
        assert result is False

    def test_start_compose_dir_missing(self):
        """start_service returns False when compose_dir doesn't exist."""
        mgr = DockerManager()
        with patch.object(Path, "exists", return_value=False):
            result = mgr.start_service("whisper-api")
        assert result is False

    def test_start_with_build_flag(self):
        """Build flag adds --build to compose command."""
        mgr = DockerManager()
        with patch.object(Path, "exists", return_value=True):
            with patch.object(_dk_mod, "_run_cmd", return_value=subprocess.CompletedProcess(["docker"], 0, "", "")) as mock_cmd:
                with patch.object(_dk_mod, "COMPOSE_CMD", ["docker", "compose"]):
                    mgr.start_service("whisper-api", build=True)
                    cmd = mock_cmd.call_args[0][0]
                    assert "--build" in cmd

    def test_stop_unknown_service(self):
        mgr = DockerManager()
        assert mgr.stop_service("nonexistent-service") is False

    def test_stop_known_service_success(self):
        mgr = DockerManager()
        with patch.object(_dk_mod, "_run_cmd", return_value=subprocess.CompletedProcess(["docker"], 0, "", "")):
            with patch.object(_dk_mod, "COMPOSE_CMD", ["docker", "compose"]):
                result = mgr.stop_service("whisper-api")
        assert result is True

    def test_restart_calls_stop_then_start(self):
        mgr = DockerManager()
        call_order = []
        with patch.object(_dk_mod, "_run_cmd", return_value=subprocess.CompletedProcess(["docker"], 0, "", "")):
            with patch.object(_dk_mod, "COMPOSE_CMD", ["docker", "compose"]):
                with patch.object(mgr, "stop_service", side_effect=lambda s: call_order.append("stop") or True):
                    with patch.object(mgr, "start_service", side_effect=lambda s, **kw: call_order.append("start") or True):
                        with patch("time.sleep"):  # skip the 3s sleep
                            mgr.restart_service("whisper-api")
        assert call_order == ["stop", "start"]


# ============================================================================
# Tests for DockerManager.get_logs
# ============================================================================


class TestGetLogs:
    """Tests for DockerManager.get_logs()."""

    def test_unknown_service(self):
        mgr = DockerManager()
        result = mgr.get_logs("nonexistent-service")
        assert "inconnu" in result.lower()

    def test_known_service_logs(self):
        mgr = DockerManager()
        with patch.object(_dk_mod, "_run_cmd", return_value=subprocess.CompletedProcess(["docker"], 0, "stdout-log", "stderr-log")):
            result = mgr.get_logs("whisper-api")
        assert "stdout-log" in result
        assert "stderr-log" in result

    def test_tail_parameter(self):
        """Tail parameter is forwarded to docker logs command."""
        mgr = DockerManager()
        with patch.object(_dk_mod, "_run_cmd", return_value=subprocess.CompletedProcess(["docker"], 0, "", "")) as mock_cmd:
            mgr.get_logs("whisper-api", tail=100)
            cmd = mock_cmd.call_args[0][0]
            assert "100" in cmd


# ============================================================================
# Tests for DockerManager.check_gpu
# ============================================================================


class TestCheckGpu:
    """Tests for DockerManager.check_gpu() — nvidia-smi mock."""

    def test_nvidia_smi_not_found(self):
        mgr = DockerManager()
        with patch.object(_dk_mod, "_run_cmd", return_value=subprocess.CompletedProcess(["nvidia-smi"], 1, "", "not found")):
            result = mgr.check_gpu()
        assert result["available"] is False

    def test_single_gpu(self):
        mgr = DockerManager()
        nvidia_output = "0, NVIDIA GeForce RTX 3090, 24576, 12000, 12576, 45"
        with patch.object(_dk_mod, "_run_cmd", return_value=subprocess.CompletedProcess(["nvidia-smi"], 0, nvidia_output, "")):
            result = mgr.check_gpu()
        assert result["available"] is True
        assert result["count"] == 1
        gpu = result["gpus"][0]
        assert gpu["index"] == 0
        assert gpu["memory_total_mb"] == 24576
        assert gpu["memory_free_mb"] == 12000
        assert gpu["memory_used_mb"] == 12576
        assert gpu["utilization_pct"] == 45

    def test_dual_gpu(self):
        mgr = DockerManager()
        nvidia_output = (
            "0, NVIDIA GeForce RTX 3080 Ti, 16384, 15000, 1384, 12\n"
            "1, NVIDIA GeForce RTX 3090, 24576, 10000, 14576, 75"
        )
        with patch.object(_dk_mod, "_run_cmd", return_value=subprocess.CompletedProcess(["nvidia-smi"], 0, nvidia_output, "")):
            result = mgr.check_gpu()
        assert result["count"] == 2
        assert result["gpus"][0]["memory_total_mb"] == 16384
        assert result["gpus"][1]["memory_total_mb"] == 24576

    def test_empty_output(self):
        mgr = DockerManager()
        with patch.object(_dk_mod, "_run_cmd", return_value=subprocess.CompletedProcess(["nvidia-smi"], 0, "", "")):
            result = mgr.check_gpu()
        assert result["available"] is True
        assert result["count"] == 0


# ============================================================================
# Tests for register() and execute()
# ============================================================================


class TestRegisterAndExecute:
    """Tests for CLI registration and execute dispatch."""

    def test_register_creates_subparser(self):
        """register() adds docker subcommands without error."""
        import argparse
        parser = argparse.ArgumentParser()
        subparsers = parser.add_subparsers(dest="command")
        _dk_mod.register(subparsers)
        # Verify parsing works for docker status
        args = parser.parse_args(["docker", "status"])
        assert args.docker_action == "status"

    def test_execute_status(self, capsys):
        """execute with status action prints output."""
        mgr_instance = MagicMock()
        mgr_instance.print_status = MagicMock()
        with patch.object(_dk_mod, "DockerManager", return_value=mgr_instance):
            args = MagicMock(docker_action="status", remote=False)
            result = _dk_mod.execute(args)
        assert result == 0
        mgr_instance.print_status.assert_called_once()

    def test_execute_start_single(self):
        """execute with start action for single service."""
        mgr_instance = MagicMock()
        mgr_instance.start_service = MagicMock(return_value=True)
        with patch.object(_dk_mod, "DockerManager", return_value=mgr_instance):
            args = MagicMock(docker_action="start", service="whisper-api", build=False)
            result = _dk_mod.execute(args)
        assert result == 0
        mgr_instance.start_service.assert_called_once_with("whisper-api", build=False)

    def test_execute_start_all(self):
        """execute with start all calls start for every service."""
        mgr_instance = MagicMock()
        mgr_instance.start_service = MagicMock(return_value=True)
        with patch.object(_dk_mod, "DockerManager", return_value=mgr_instance):
            args = MagicMock(docker_action="start", service="all", build=False)
            result = _dk_mod.execute(args)
        assert result == 0
        assert mgr_instance.start_service.call_count == len(_mock_services)

    def test_execute_stop_single(self):
        mgr_instance = MagicMock()
        mgr_instance.stop_service = MagicMock(return_value=True)
        with patch.object(_dk_mod, "DockerManager", return_value=mgr_instance):
            args = MagicMock(docker_action="stop", service="whisper-api")
            result = _dk_mod.execute(args)
        assert result == 0

    def test_execute_logs(self, capsys):
        mgr_instance = MagicMock()
        mgr_instance.get_logs = MagicMock(return_value="log output here")
        with patch.object(_dk_mod, "DockerManager", return_value=mgr_instance):
            args = MagicMock(docker_action="logs", service="whisper-api", tail=100)
            result = _dk_mod.execute(args)
        assert result == 0
        mgr_instance.get_logs.assert_called_once_with("whisper-api", 100)

    def test_execute_test(self):
        mgr_instance = MagicMock()
        mgr_instance.test_all_services = MagicMock(return_value=True)
        with patch.object(_dk_mod, "DockerManager", return_value=mgr_instance):
            args = MagicMock(docker_action="test", remote=False)
            result = _dk_mod.execute(args)
        assert result == 0

    def test_execute_default_status(self):
        """No docker_action defaults to printing status."""
        mgr_instance = MagicMock()
        mgr_instance.print_status = MagicMock()
        with patch.object(_dk_mod, "DockerManager", return_value=mgr_instance):
            args = MagicMock(docker_action=None)
            result = _dk_mod.execute(args)
        assert result == 0
        mgr_instance.print_status.assert_called_once()


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
