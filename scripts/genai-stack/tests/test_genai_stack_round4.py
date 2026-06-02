"""
Round 4: Pure-logic tests for genai-stack command modules.

Targets:
  - commands/gpu.py: profile scoring, schedule, check_fit, table formatting
  - commands/models.py: data integrity, _get_hf_token, download_nunchaku
  - commands/docker.py: DockerManager error paths, container status parsing
  - commands/quant.py: execute dispatch

Dispatch #2149, item 6.
"""

import json
import os
import sys
import unittest
from io import StringIO
from pathlib import Path
from unittest.mock import MagicMock, patch, PropertyMock

# Ensure genai-stack root is importable
_genai_root = str(Path(__file__).resolve().parent.parent)
if _genai_root not in sys.path:
    sys.path.insert(0, _genai_root)


# ============================================================================
# commands/models.py — Data integrity
# ============================================================================

class TestQwenModelsData(unittest.TestCase):
    """QWEN_MODELS list integrity checks."""

    def test_qwen_models_count(self):
        from commands.models import QWEN_MODELS
        self.assertEqual(len(QWEN_MODELS), 3)

    def test_qwen_models_required_keys(self):
        from commands.models import QWEN_MODELS
        required = {"name", "repo_id", "filename", "local_name", "subdir", "size_gb"}
        for i, model in enumerate(QWEN_MODELS):
            self.assertTrue(required.issubset(model.keys()),
                            f"QWEN_MODELS[{i}] missing keys: {required - model.keys()}")

    def test_qwen_models_positive_size(self):
        from commands.models import QWEN_MODELS
        for model in QWEN_MODELS:
            self.assertGreater(model["size_gb"], 0,
                               f"{model['name']} has non-positive size_gb")

    def test_qwen_models_unique_local_names(self):
        from commands.models import QWEN_MODELS
        names = [m["local_name"] for m in QWEN_MODELS]
        self.assertEqual(len(names), len(set(names)), "Duplicate local_name in QWEN_MODELS")

    def test_qwen_models_filenames_safetensors(self):
        from commands.models import QWEN_MODELS
        for model in QWEN_MODELS:
            self.assertTrue(model["local_name"].endswith(".safetensors"),
                            f"{model['local_name']} is not .safetensors")


class TestNunchakuModelsData(unittest.TestCase):
    """NUNCHAKU_MODELS dict integrity checks."""

    def test_nunchaku_models_count(self):
        from commands.models import NUNCHAKU_MODELS
        self.assertGreaterEqual(len(NUNCHAKU_MODELS), 6)

    def test_nunchaku_values_safetensors(self):
        from commands.models import NUNCHAKU_MODELS
        for key, filename in NUNCHAKU_MODELS.items():
            self.assertTrue(filename.endswith(".safetensors"),
                            f"NUNCHAKU_MODELS[{key}] = {filename} not .safetensors")

    def test_nunchaku_unique_values(self):
        from commands.models import NUNCHAKU_MODELS
        values = list(NUNCHAKU_MODELS.values())
        self.assertEqual(len(values), len(set(values)), "Duplicate filenames in NUNCHAKU_MODELS")

    def test_nunchaku_repo_id_is_string(self):
        from commands.models import NUNCHAKU_REPO_ID
        self.assertIsInstance(NUNCHAKU_REPO_ID, str)
        self.assertIn("/", NUNCHAKU_REPO_ID)  # org/repo format


class TestZimageVaeConfig(unittest.TestCase):
    """ZIMAGE_VAE_CONFIG integrity checks."""

    def test_zimage_vae_config_keys(self):
        from commands.models import ZIMAGE_VAE_CONFIG
        required = {"url", "filename", "subfolder"}
        self.assertTrue(required.issubset(ZIMAGE_VAE_CONFIG.keys()))

    def test_zimage_vae_config_url_is_http(self):
        from commands.models import ZIMAGE_VAE_CONFIG
        self.assertTrue(ZIMAGE_VAE_CONFIG["url"].startswith("https://"))

    def test_zimage_vae_config_filename_safetensors(self):
        from commands.models import ZIMAGE_VAE_CONFIG
        self.assertTrue(ZIMAGE_VAE_CONFIG["filename"].endswith(".safetensors"))


# ============================================================================
# commands/models.py — _get_hf_token
# ============================================================================

class TestGetHfToken(unittest.TestCase):
    """Token resolution logic for HuggingFace."""

    @patch.dict(os.environ, {"HF_TOKEN": "hf_test123"}, clear=False)
    def test_hf_token_from_env_hf_token(self):
        from commands.models import _get_hf_token
        self.assertEqual(_get_hf_token(), "hf_test123")

    @patch.dict(os.environ, {"HUGGINGFACE_TOKEN": "hf_from_alt"}, clear=False)
    def test_hf_token_from_env_huggingface(self):
        from commands.models import _get_hf_token
        # HF_TOKEN not set, HUGGINGFACE_TOKEN is set
        os.environ.pop("HF_TOKEN", None)
        result = _get_hf_token()
        self.assertEqual(result, "hf_from_alt")

    @patch.dict(os.environ, {}, clear=True)
    @patch.object(Path, "exists", return_value=False)
    @patch.object(Path, "home", return_value=Path("C:/Users/test"))
    def test_hf_token_none_when_no_env_no_files(self, mock_home, mock_exists):
        from commands.models import _get_hf_token
        self.assertIsNone(_get_hf_token())


# ============================================================================
# commands/models.py — download_nunchaku pure paths
# ============================================================================

class TestDownloadNunchakuLogic(unittest.TestCase):
    """download_nunchaku list and error paths."""

    def test_list_models_returns_true(self):
        from commands.models import download_nunchaku
        with patch("sys.stdout", new_callable=StringIO):
            result = download_nunchaku(list_models=True)
        self.assertTrue(result)

    def test_list_models_prints_all_keys(self):
        from commands.models import download_nunchaku, NUNCHAKU_MODELS
        buf = StringIO()
        with patch("sys.stdout", buf):
            download_nunchaku(list_models=True)
        output = buf.getvalue()
        for key in NUNCHAKU_MODELS:
            self.assertIn(key, output)

    def test_unknown_model_key_returns_false(self):
        from commands.models import download_nunchaku
        with patch("sys.stdout", new_callable=StringIO):
            result = download_nunchaku(model_key="nonexistent-model")
        self.assertFalse(result)


# ============================================================================
# commands/gpu.py — profile_current scoring
# ============================================================================

class TestProfileCurrentScoring(unittest.TestCase):
    """profile_current scoring algorithm with mocked services."""

    @patch("commands.gpu._get_running_services")
    @patch("commands.gpu.check_vram", return_value=[])
    def test_no_running_services_selects_best_match(self, mock_vram, mock_running):
        from commands.gpu import profile_current
        # No services running — profile with most services_down matched wins
        mock_running.return_value = []
        with patch("sys.stdout", new_callable=StringIO):
            result = profile_current()
        # Should return some profile (the one that best matches "nothing running")
        self.assertIsInstance(result, (str, type(None)))

    @patch("commands.gpu._get_running_services")
    @patch("commands.gpu.check_vram", return_value=[])
    def test_running_services_affects_match(self, mock_vram, mock_running):
        from commands.gpu import profile_current
        from config import GPU_PROFILES
        # Pick a profile and pretend its services_up are running
        first_profile = next(iter(GPU_PROFILES.items()))
        profile_name, profile_data = first_profile
        mock_running.return_value = list(profile_data.get("services_up", []))
        with patch("sys.stdout", new_callable=StringIO):
            result = profile_current()
        self.assertEqual(result, profile_name)


# ============================================================================
# commands/gpu.py — schedule_group
# ============================================================================

class TestScheduleGroup(unittest.TestCase):
    """schedule_group group-to-profile resolution."""

    @patch("commands.gpu.profile_apply", return_value=True)
    def test_known_group_calls_profile_apply(self, mock_apply):
        from commands.gpu import schedule_group
        from config import GROUP_GPU_PROFILE
        first_group = next(iter(GROUP_GPU_PROFILE))
        result = schedule_group(first_group)
        self.assertTrue(result)
        expected_profile = GROUP_GPU_PROFILE[first_group]
        mock_apply.assert_called_once_with(expected_profile)

    def test_unknown_group_returns_false(self):
        from commands.gpu import schedule_group
        with patch("sys.stdout", new_callable=StringIO):
            result = schedule_group("nonexistent_group_xyz")
        self.assertFalse(result)


# ============================================================================
# commands/gpu.py — profile_apply
# ============================================================================

class TestProfileApply(unittest.TestCase):
    """profile_apply error path for unknown profile."""

    def test_unknown_profile_returns_false(self):
        from commands.gpu import profile_apply
        with patch("sys.stdout", new_callable=StringIO):
            result = profile_apply("nonexistent_profile_xyz")
        self.assertFalse(result)


# ============================================================================
# commands/gpu.py — check_fit
# ============================================================================

class TestCheckFit(unittest.TestCase):
    """check_fit VRAM compatibility check with mock data."""

    @patch("commands.gpu.check_vram")
    def test_no_gpu_returns_false(self, mock_vram):
        from commands.gpu import check_fit
        mock_vram.return_value = []
        with patch("sys.stdout", new_callable=StringIO):
            result = check_fit(4096)
        self.assertFalse(result)

    @patch("commands.gpu.check_vram")
    def test_fits_when_free_sufficient(self, mock_vram):
        from commands.gpu import check_fit
        mock_vram.return_value = [
            {"index": "0", "name": "RTX 3090", "total": 24576, "used": 4096, "free": 20480}
        ]
        with patch("sys.stdout", new_callable=StringIO):
            result = check_fit(8192)
        self.assertTrue(result)

    @patch("commands.gpu.check_vram")
    def test_does_not_fit_when_free_insufficient(self, mock_vram):
        from commands.gpu import check_fit
        mock_vram.return_value = [
            {"index": "0", "name": "RTX 3090", "total": 24576, "used": 20480, "free": 4096}
        ]
        with patch("sys.stdout", new_callable=StringIO):
            result = check_fit(8192)
        self.assertFalse(result)

    @patch("commands.gpu.check_vram")
    def test_specific_gpu_index_filter(self, mock_vram):
        from commands.gpu import check_fit
        mock_vram.return_value = [
            {"index": "0", "name": "RTX 3090", "total": 24576, "used": 20480, "free": 4096},
            {"index": "1", "name": "RTX 3080", "total": 16384, "used": 0, "free": 16384},
        ]
        with patch("sys.stdout", new_callable=StringIO):
            # GPU 0 has only 4096 free, GPU 1 has 16384 free
            result = check_fit(8192, gpu_index=1)
        self.assertTrue(result)


# ============================================================================
# commands/gpu.py — print_gpu_table
# ============================================================================

class TestPrintGpuTable(unittest.TestCase):
    """print_gpu_table output formatting."""

    def test_empty_gpus_prints_none(self):
        from commands.gpu import print_gpu_table
        buf = StringIO()
        with patch("sys.stdout", buf):
            print_gpu_table([])
        self.assertIn("Aucun GPU", buf.getvalue())

    def test_with_gpus_prints_table(self):
        from commands.gpu import print_gpu_table
        gpus = [
            {"index": "0", "name": "RTX 3090", "total": 24576, "used": 4096, "free": 20480}
        ]
        buf = StringIO()
        with patch("sys.stdout", buf):
            print_gpu_table(gpus)
        output = buf.getvalue()
        self.assertIn("RTX 3090", output)
        self.assertIn("20480", output)


# ============================================================================
# commands/docker.py — DockerManager error paths
# ============================================================================

class TestDockerManagerErrorPaths(unittest.TestCase):
    """DockerManager returns correct errors for unknown services."""

    @patch("commands.docker.load_env", return_value={})
    def setUp(self, mock_env):
        from commands.docker import DockerManager
        self.manager = DockerManager()

    def test_container_status_unknown_service(self):
        result = self.manager.get_container_status("nonexistent_xyz")
        self.assertFalse(result["running"])
        # Returns {"status": "unknown", "running": False, "error": "Service inconnu"}
        self.assertIn("inconnu", result.get("error", "").lower())

    def test_check_service_health_unknown(self):
        ok, msg = self.manager.check_service_health("nonexistent_xyz")
        self.assertFalse(ok)
        self.assertIn("inconnu", msg.lower())

    def test_start_service_unknown(self):
        result = self.manager.start_service("nonexistent_xyz")
        self.assertFalse(result)

    def test_stop_service_unknown(self):
        result = self.manager.stop_service("nonexistent_xyz")
        self.assertFalse(result)

    def test_get_logs_unknown(self):
        result = self.manager.get_logs("nonexistent_xyz")
        self.assertIn("inconnu", result.lower())


# ============================================================================
# commands/docker.py — get_container_status JSON parsing
# ============================================================================

class TestDockerContainerStatusParsing(unittest.TestCase):
    """get_container_status parses docker inspect JSON correctly."""

    @patch("commands.docker.load_env", return_value={})
    def setUp(self, mock_env):
        from commands.docker import DockerManager
        from config import SERVICES
        self.manager = DockerManager()
        self.svc_name = next(iter(SERVICES))

    @patch("commands.docker._run_cmd")
    def test_running_container_parsed(self, mock_run):
        import subprocess
        mock_run.return_value = subprocess.CompletedProcess(
            args=["docker", "inspect"],
            returncode=0,
            stdout=json.dumps([{
                "State": {
                    "Status": "running",
                    "Running": True,
                    "StartedAt": "2026-01-01T00:00:00Z",
                    "Health": {"Status": "healthy"}
                }
            }]),
            stderr=""
        )
        result = self.manager.get_container_status(self.svc_name)
        self.assertTrue(result["running"])
        self.assertEqual(result["status"], "running")
        self.assertEqual(result["health"], "healthy")

    @patch("commands.docker._run_cmd")
    def test_stopped_container_parsed(self, mock_run):
        import subprocess
        mock_run.return_value = subprocess.CompletedProcess(
            args=["docker", "inspect"],
            returncode=0,
            stdout=json.dumps([{
                "State": {
                    "Status": "exited",
                    "Running": False,
                    "StartedAt": None,
                    "Health": {}
                }
            }]),
            stderr=""
        )
        result = self.manager.get_container_status(self.svc_name)
        self.assertFalse(result["running"])
        self.assertEqual(result["status"], "exited")

    @patch("commands.docker._run_cmd")
    def test_not_found_container(self, mock_run):
        import subprocess
        mock_run.return_value = subprocess.CompletedProcess(
            args=["docker", "inspect"],
            returncode=1,
            stdout="",
            stderr="not found"
        )
        result = self.manager.get_container_status(self.svc_name)
        self.assertFalse(result["running"])
        self.assertEqual(result["status"], "not_found")


# ============================================================================
# commands/docker.py — check_service_health with mock requests
# ============================================================================

class TestDockerServiceHealthCheck(unittest.TestCase):
    """check_service_health HTTP response handling."""

    @patch("commands.docker.load_env", return_value={})
    def setUp(self, mock_env):
        from commands.docker import DockerManager
        self.manager = DockerManager()

    @patch("commands.docker.requests.get")
    def test_200_response_is_healthy(self, mock_get):
        mock_get.return_value = MagicMock(status_code=200)
        # Pick a known service name from SERVICES
        from config import SERVICES
        svc_name = next(iter(SERVICES))
        ok, msg = self.manager.check_service_health(svc_name)
        self.assertTrue(ok)
        self.assertIn("200", msg)

    @patch("commands.docker.requests.get")
    def test_401_response_is_auth_required(self, mock_get):
        mock_get.return_value = MagicMock(status_code=401)
        from config import SERVICES
        svc_name = next(iter(SERVICES))
        ok, msg = self.manager.check_service_health(svc_name)
        self.assertFalse(ok)
        self.assertIn("401", msg)

    @patch("commands.docker.requests.get")
    def test_connection_error(self, mock_get):
        import requests as _requests
        mock_get.side_effect = _requests.exceptions.ConnectionError("refused")
        from config import SERVICES
        svc_name = next(iter(SERVICES))
        ok, msg = self.manager.check_service_health(svc_name)
        self.assertFalse(ok)
        self.assertIn("Connection refused", msg)

    @patch("commands.docker.requests.get")
    def test_timeout_error(self, mock_get):
        import requests as _requests
        mock_get.side_effect = _requests.exceptions.Timeout("timed out")
        from config import SERVICES
        svc_name = next(iter(SERVICES))
        ok, msg = self.manager.check_service_health(svc_name)
        self.assertFalse(ok)
        self.assertIn("Timeout", msg)


# ============================================================================
# commands/quant.py — execute dispatch
# ============================================================================

class TestQuantExecuteDispatch(unittest.TestCase):
    """quant.execute dispatches to correct configure functions."""

    @patch("commands.quant.show_summary")
    def test_summary_action(self, mock_summary):
        from commands.quant import execute
        args = MagicMock(quant_action="summary")
        result = execute(args)
        mock_summary.assert_called_once()
        self.assertEqual(result, 0)

    @patch("commands.quant.show_summary")
    def test_no_quant_action_shows_summary(self, mock_summary):
        from commands.quant import execute
        args = MagicMock(spec=[])
        # No quant_action attribute → show_summary
        del args.quant_action
        result = execute(args)
        mock_summary.assert_called_once()
        self.assertEqual(result, 0)

    @patch("commands.quant.configure_qwen", return_value=True)
    @patch("commands.quant.configure_zimage", return_value=True)
    def test_apply_all(self, mock_zimage, mock_qwen):
        from commands.quant import execute
        args = MagicMock(quant_action="apply", service="all", dry_run=False)
        with patch("sys.stdout", new_callable=StringIO):
            result = execute(args)
        mock_zimage.assert_called_once()
        mock_qwen.assert_called_once()
        self.assertEqual(result, 0)

    @patch("commands.quant.configure_zimage", return_value=True)
    def test_apply_zimage_only(self, mock_zimage):
        from commands.quant import execute
        args = MagicMock(quant_action="apply", service="zimage", dry_run=False)
        with patch("sys.stdout", new_callable=StringIO):
            result = execute(args)
        mock_zimage.assert_called_once()
        self.assertEqual(result, 0)

    @patch("commands.quant.configure_qwen", return_value=True)
    def test_apply_qwen_only(self, mock_qwen):
        from commands.quant import execute
        args = MagicMock(quant_action="apply", service="qwen", dry_run=False)
        with patch("sys.stdout", new_callable=StringIO):
            result = execute(args)
        mock_qwen.assert_called_once()
        self.assertEqual(result, 0)


# ============================================================================
# commands/gpu.py — _run_cmd
# ============================================================================

class TestGpuRunCmd(unittest.TestCase):
    """_run_cmd subprocess wrapper."""

    @patch("commands.gpu.subprocess.run")
    def test_success_returns_tuple(self, mock_run):
        from commands.gpu import _run_cmd
        mock_run.return_value = MagicMock(returncode=0, stdout="ok", stderr="")
        ok, stdout, stderr = _run_cmd("echo ok")
        self.assertTrue(ok)
        self.assertEqual(stdout, "ok")

    @patch("commands.gpu.subprocess.run")
    def test_failure_returns_false(self, mock_run):
        from commands.gpu import _run_cmd
        mock_run.return_value = MagicMock(returncode=1, stdout="", stderr="err")
        ok, stdout, stderr = _run_cmd("false")
        self.assertFalse(ok)

    @patch("commands.gpu.subprocess.run", side_effect=Exception("boom"))
    def test_exception_returns_false(self, mock_run):
        from commands.gpu import _run_cmd
        ok, stdout, stderr = _run_cmd("bad")
        self.assertFalse(ok)
        self.assertIn("boom", stderr)


if __name__ == "__main__":
    unittest.main()
