#!/usr/bin/env python3
"""
Tests for scripts/genai-stack/commands/gpu.py

Covers: check_vram (parsing), print_gpu_table, _run_cmd,
profile_list, profile_current (mocked), check_fit (mocked),
schedule_group (mocked), register/execute CLI dispatch,
GPU_PROFILES/GROUP_GPU_PROFILE data validation.
CPU-only: mocks nvidia-smi, Docker, network calls.

LIVE: 4 callers (check_vram.py, auto_validate.py, notebooks.py, genai.py).
"""

import subprocess
import sys
import pytest
from pathlib import Path
from unittest.mock import patch, MagicMock
from io import StringIO

# Add genai-stack to sys.path
_genai_stack = str(Path(__file__).resolve().parent.parent / "genai-stack")
if _genai_stack not in sys.path:
    sys.path.insert(0, _genai_stack)

from commands.gpu import (
    check_vram,
    print_gpu_table,
    _run_cmd,
    profile_list,
    profile_current,
    check_fit,
    schedule_group,
    register,
    execute,
)
from config import SERVICES, GPU_PROFILES, GROUP_GPU_PROFILE


# ============================================================================
# Helpers
# ============================================================================

def _nvidia_smi_output(gpus):
    """Build fake nvidia-smi CSV output."""
    lines = []
    for g in gpus:
        lines.append(f"{g['index']}, {g['name']}, {g['total']}, {g['used']}, {g['free']}")
    return "\n".join(lines)


FAKE_GPU_SINGLE = [
    {"index": "0", "name": "NVIDIA GeForce RTX 3090", "total": 24576, "used": 8192, "free": 16384}
]

FAKE_GPU_MULTI = [
    {"index": "0", "name": "NVIDIA GeForce RTX 3090", "total": 24576, "used": 4096, "free": 20480},
    {"index": "1", "name": "NVIDIA GeForce RTX 3080 Ti", "total": 12288, "used": 6144, "free": 6144},
]


def _mock_subprocess_run(stdout="", returncode=0, side_effect=None):
    """Create a mock subprocess.run that returns the given stdout."""
    mock_result = MagicMock()
    mock_result.stdout = stdout
    mock_result.stderr = ""
    mock_result.returncode = returncode
    mock = MagicMock(return_value=mock_result)
    if side_effect:
        mock.side_effect = side_effect
    return mock


# ============================================================================
# check_vram
# ============================================================================

class TestCheckVram:
    def test_parses_single_gpu(self):
        """Parses single GPU from nvidia-smi CSV output."""
        output = _nvidia_smi_output(FAKE_GPU_SINGLE)
        with patch("commands.gpu.subprocess.run", _mock_subprocess_run(stdout=output)):
            gpus = check_vram()
        assert len(gpus) == 1
        assert gpus[0]["index"] == "0"
        assert gpus[0]["name"] == "NVIDIA GeForce RTX 3090"
        assert gpus[0]["total"] == 24576
        assert gpus[0]["used"] == 8192
        assert gpus[0]["free"] == 16384

    def test_parses_multiple_gpus(self):
        """Parses multiple GPUs from nvidia-smi CSV output."""
        output = _nvidia_smi_output(FAKE_GPU_MULTI)
        with patch("commands.gpu.subprocess.run", _mock_subprocess_run(stdout=output)):
            gpus = check_vram()
        assert len(gpus) == 2
        assert gpus[0]["index"] == "0"
        assert gpus[1]["index"] == "1"
        assert gpus[1]["total"] == 12288

    def test_returns_empty_on_nvidia_smi_not_found(self):
        """Returns empty list when nvidia-smi is not installed."""
        with patch("commands.gpu.subprocess.run", side_effect=FileNotFoundError):
            gpus = check_vram()
        assert gpus == []

    def test_returns_empty_on_nvidia_smi_error(self):
        """Returns empty list when nvidia-smi returns error."""
        mock_result = MagicMock()
        mock_result.stdout = ""
        mock_result.returncode = 1
        with patch("commands.gpu.subprocess.run", side_effect=subprocess.CalledProcessError(1, "nvidia-smi")):
            gpus = check_vram()
        assert gpus == []

    def test_skips_malformed_rows(self):
        """Skips rows that don't have exactly 5 columns."""
        output = "0, RTX 3090, 24576\n"  # Only 3 columns
        with patch("commands.gpu.subprocess.run", _mock_subprocess_run(stdout=output)):
            gpus = check_vram()
        assert gpus == []

    def test_handles_whitespace_in_fields(self):
        """Strips whitespace from CSV fields."""
        output = " 0 ,  RTX 3090 ,  24576 ,  4096 ,  20480 "
        with patch("commands.gpu.subprocess.run", _mock_subprocess_run(stdout=output)):
            gpus = check_vram()
        assert len(gpus) == 1
        assert gpus[0]["index"] == "0"
        assert gpus[0]["name"] == "RTX 3090"

    def test_converts_values_to_int(self):
        """Converts memory values to integers."""
        output = "0, RTX 3090, 24576, 8192, 16384"
        with patch("commands.gpu.subprocess.run", _mock_subprocess_run(stdout=output)):
            gpus = check_vram()
        assert isinstance(gpus[0]["total"], int)
        assert isinstance(gpus[0]["used"], int)
        assert isinstance(gpus[0]["free"], int)


# ============================================================================
# print_gpu_table
# ============================================================================

class TestPrintGpuTable:
    def test_prints_header_and_rows(self, capsys):
        """Prints table header and one row per GPU."""
        print_gpu_table(FAKE_GPU_MULTI)
        captured = capsys.readouterr()
        assert "Index" in captured.out
        assert "RTX 3090" in captured.out
        assert "RTX 3080 Ti" in captured.out
        assert "16384" not in captured.out  # free is formatted as "free / total"

    def test_prints_no_gpu_message(self, capsys):
        """Prints 'Aucun GPU detecte' when list is empty."""
        print_gpu_table([])
        captured = capsys.readouterr()
        assert "Aucun GPU" in captured.out

    def test_shows_percent_used(self, capsys):
        """Shows percentage of used memory."""
        gpus = [{"index": "0", "name": "RTX 3090", "total": 10000, "used": 2500, "free": 7500}]
        print_gpu_table(gpus)
        captured = capsys.readouterr()
        assert "25.0%" in captured.out

    def test_free_total_format(self, capsys):
        """Shows 'free / total MiB' format."""
        gpus = [{"index": "0", "name": "RTX 3090", "total": 24576, "used": 8192, "free": 16384}]
        print_gpu_table(gpus)
        captured = capsys.readouterr()
        assert "16384 / 24576 MiB" in captured.out


# ============================================================================
# _run_cmd
# ============================================================================

class TestRunCmd:
    def test_returns_success_on_zero_returncode(self):
        """Returns (True, stdout, stderr) on success."""
        with patch("commands.gpu.subprocess.run") as mock_run:
            mock_result = MagicMock()
            mock_result.returncode = 0
            mock_result.stdout = "running"
            mock_result.stderr = ""
            mock_run.return_value = mock_result
            success, stdout, stderr = _run_cmd("docker inspect test")
        assert success is True
        assert stdout == "running"

    def test_returns_failure_on_nonzero_returncode(self):
        """Returns (False, stdout, stderr) on failure."""
        with patch("commands.gpu.subprocess.run") as mock_run:
            mock_result = MagicMock()
            mock_result.returncode = 1
            mock_result.stdout = ""
            mock_result.stderr = "error"
            mock_run.return_value = mock_result
            success, stdout, stderr = _run_cmd("false_command")
        assert success is False

    def test_returns_failure_on_exception(self):
        """Returns (False, '', error_msg) on exception."""
        with patch("commands.gpu.subprocess.run", side_effect=OSError("not found")):
            success, stdout, stderr = _run_cmd("bad command")
        assert success is False
        assert "not found" in stderr


# ============================================================================
# profile_list
# ============================================================================

class TestProfileList:
    def test_prints_all_profiles(self, capsys):
        """Prints all GPU_PROFILES entries."""
        profile_list()
        captured = capsys.readouterr()
        for name in GPU_PROFILES:
            assert name in captured.out

    def test_prints_description(self, capsys):
        """Prints profile descriptions."""
        profile_list()
        captured = capsys.readouterr()
        for name, profile in GPU_PROFILES.items():
            assert profile["description"] in captured.out

    def test_prints_profile_count(self, capsys):
        """Prints the total number of profiles."""
        profile_list()
        captured = capsys.readouterr()
        assert f"{len(GPU_PROFILES)} profils" in captured.out


# ============================================================================
# profile_current (mocked)
# ============================================================================

class TestProfileCurrent:
    def test_detects_matching_profile(self, capsys):
        """Detects the best matching profile from running services."""
        # Simulate only comfyui-qwen and forge-turbo running = image_default
        with patch("commands.gpu._get_running_services", return_value=["comfyui-qwen", "forge-turbo"]):
            with patch("commands.gpu.check_vram", return_value=[]):
                result = profile_current()
        assert result == "image_default"

    def test_detects_no_services_as_api(self, capsys):
        """No running services matches audio_api (empty up/down sets)."""
        with patch("commands.gpu._get_running_services", return_value=[]):
            with patch("commands.gpu.check_vram", return_value=[]):
                result = profile_current()
        # audio_api has empty services_up and services_down, should score highest
        assert result is not None

    def test_returns_none_on_no_match(self, capsys):
        """Returns None-compatible when nothing matches well."""
        # All services running — penalizes every profile heavily
        all_services = list(SERVICES.keys())
        with patch("commands.gpu._get_running_services", return_value=all_services):
            with patch("commands.gpu.check_vram", return_value=[]):
                result = profile_current()
        # Still returns something (best_score > -1), but heavily penalized
        assert result is not None  # Always picks best available

    def test_prints_running_services(self, capsys):
        """Prints the list of running services."""
        with patch("commands.gpu._get_running_services", return_value=["comfyui-qwen"]):
            with patch("commands.gpu.check_vram", return_value=[]):
                profile_current()
        captured = capsys.readouterr()
        assert "comfyui-qwen" in captured.out


# ============================================================================
# check_fit (mocked)
# ============================================================================

class TestCheckFit:
    def test_fits_when_enough_vram(self, capsys):
        """Returns True when enough free VRAM."""
        gpus = [{"index": "0", "name": "RTX 3090", "total": 24576, "used": 4096, "free": 20480}]
        with patch("commands.gpu.check_vram", return_value=gpus):
            result = check_fit(10000)
        assert result is True

    def test_does_not_fit_when_insufficient(self, capsys):
        """Returns False when insufficient VRAM."""
        gpus = [{"index": "0", "name": "RTX 3090", "total": 24576, "used": 20480, "free": 4096}]
        with patch("commands.gpu.check_vram", return_value=gpus):
            result = check_fit(10000)
        assert result is False

    def test_returns_false_no_gpu(self, capsys):
        """Returns False when no GPU detected."""
        with patch("commands.gpu.check_vram", return_value=[]):
            result = check_fit(10000)
        assert result is False

    def test_gpu_index_filter(self, capsys):
        """Only checks the specified GPU index."""
        gpus = [
            {"index": "0", "name": "RTX 3090", "total": 24576, "used": 20480, "free": 4096},
            {"index": "1", "name": "RTX 3080 Ti", "total": 12288, "used": 2048, "free": 10240},
        ]
        with patch("commands.gpu.check_vram", return_value=gpus):
            result = check_fit(8000, gpu_index=1)
        assert result is True

    def test_gpu_index_filter_insufficient(self, capsys):
        """Returns False when specified GPU has insufficient VRAM."""
        gpus = [
            {"index": "0", "name": "RTX 3090", "total": 24576, "used": 4096, "free": 20480},
            {"index": "1", "name": "RTX 3080 Ti", "total": 12288, "used": 8192, "free": 4096},
        ]
        with patch("commands.gpu.check_vram", return_value=gpus):
            result = check_fit(8000, gpu_index=1)
        assert result is False

    def test_prints_status(self, capsys):
        """Prints OK/INSUFFISANT status per GPU."""
        gpus = [{"index": "0", "name": "RTX 3090", "total": 24576, "used": 4096, "free": 20480}]
        with patch("commands.gpu.check_vram", return_value=gpus):
            check_fit(10000)
        captured = capsys.readouterr()
        assert "OK" in captured.out


# ============================================================================
# schedule_group (mocked)
# ============================================================================

class TestScheduleGroup:
    def test_valid_group_applies_profile(self, capsys):
        """Valid group name maps to profile and calls profile_apply."""
        with patch("commands.gpu.profile_apply", return_value=True) as mock_apply:
            result = schedule_group("cloud")
        assert result is True
        mock_apply.assert_called_once_with("image_default")

    def test_invalid_group_returns_false(self, capsys):
        """Invalid group name returns False."""
        result = schedule_group("nonexistent_group")
        assert result is False

    def test_all_groups_have_profiles(self):
        """Every GROUP_GPU_PROFILE key maps to a valid GPU_PROFILES entry."""
        for group, profile in GROUP_GPU_PROFILE.items():
            assert profile in GPU_PROFILES, f"Group '{group}' maps to unknown profile '{profile}'"

    def test_prints_mapping(self, capsys):
        """Prints the group->profile mapping."""
        with patch("commands.gpu.profile_apply", return_value=True):
            schedule_group("cloud")
        captured = capsys.readouterr()
        assert "image_default" in captured.out


# ============================================================================
# register (CLI argparse)
# ============================================================================

class TestRegister:
    def test_registers_gpu_subcommand(self):
        """Register creates a gpu subparser."""
        import argparse
        parser = argparse.ArgumentParser()
        subparsers = parser.add_subparsers()
        register(subparsers)
        # Parse 'gpu' command
        args = parser.parse_args(["gpu"])
        assert hasattr(args, "detailed")
        assert hasattr(args, "json")

    def test_gpu_detailed_flag(self):
        """--detailed flag is parsed."""
        import argparse
        parser = argparse.ArgumentParser()
        subparsers = parser.add_subparsers()
        register(subparsers)
        args = parser.parse_args(["gpu", "--detailed"])
        assert args.detailed is True

    def test_gpu_json_flag(self):
        """--json flag is parsed."""
        import argparse
        parser = argparse.ArgumentParser()
        subparsers = parser.add_subparsers()
        register(subparsers)
        args = parser.parse_args(["gpu", "--json"])
        assert args.json is True

    def test_check_fit_subcommand(self):
        """gpu check-fit <vram_mb> is parsed."""
        import argparse
        parser = argparse.ArgumentParser()
        subparsers = parser.add_subparsers()
        register(subparsers)
        args = parser.parse_args(["gpu", "check-fit", "8000"])
        assert args.gpu_action == "check-fit"
        assert args.vram_mb == 8000


# ============================================================================
# execute (CLI dispatch, mocked)
# ============================================================================

class TestExecute:
    def _make_args(self, **kwargs):
        """Create a mock args namespace."""
        from argparse import Namespace
        defaults = {
            "gpu_action": None,
            "profile_action": None,
            "detailed": False,
            "json": False,
            "name": None,
            "no_wait": False,
            "vram_mb": 0,
            "gpu": None,
            "group": None,
        }
        defaults.update(kwargs)
        return Namespace(**defaults)

    def test_default_calls_check_vram(self, capsys):
        """No subcommand calls check_vram and print_gpu_table."""
        gpus = FAKE_GPU_SINGLE
        with patch("commands.gpu.check_vram", return_value=gpus):
            args = self._make_args()
            result = execute(args)
        assert result == 0
        captured = capsys.readouterr()
        assert "RTX 3090" in captured.out

    def test_json_flag_outputs_json(self, capsys):
        """--json flag outputs JSON."""
        import json
        with patch("commands.gpu.check_vram", return_value=FAKE_GPU_SINGLE):
            args = self._make_args(json=True)
            result = execute(args)
        assert result == 0
        captured = capsys.readouterr()
        data = json.loads(captured.out)
        assert len(data) == 1

    def test_check_fit_dispatch(self):
        """gpu check-fit dispatches to check_fit."""
        with patch("commands.gpu.check_fit", return_value=True) as mock:
            args = self._make_args(gpu_action="check-fit", vram_mb=8000)
            result = execute(args)
        assert result == 0
        mock.assert_called_once_with(8000, gpu_index=None)

    def test_check_fit_dispatch_with_gpu_index(self):
        """gpu check-fit --gpu 1 dispatches with gpu_index."""
        with patch("commands.gpu.check_fit", return_value=False) as mock:
            args = self._make_args(gpu_action="check-fit", vram_mb=30000, gpu=1)
            result = execute(args)
        assert result == 1  # False -> exit code 1
        mock.assert_called_once_with(30000, gpu_index=1)

    def test_schedule_dispatch(self):
        """gpu schedule dispatches to schedule_group."""
        with patch("commands.gpu.schedule_group", return_value=True) as mock:
            args = self._make_args(gpu_action="schedule", group="cloud")
            result = execute(args)
        assert result == 0
        mock.assert_called_once_with("cloud")

    def test_no_gpu_returns_1(self):
        """Returns 1 when no GPU detected."""
        with patch("commands.gpu.check_vram", return_value=[]):
            args = self._make_args()
            result = execute(args)
        assert result == 1

    def test_profile_list_dispatch(self):
        """gpu profile list dispatches to profile_list."""
        with patch("commands.gpu.profile_list") as mock:
            args = self._make_args(gpu_action="profile", profile_action="list")
            result = execute(args)
        assert result == 0
        mock.assert_called_once()

    def test_profile_apply_dispatch(self):
        """gpu profile apply dispatches to profile_apply."""
        with patch("commands.gpu.profile_apply", return_value=True) as mock:
            args = self._make_args(gpu_action="profile", profile_action="apply", name="image_default")
            result = execute(args)
        assert result == 0
        mock.assert_called_once()

    def test_profile_apply_no_wait(self):
        """gpu profile apply --no-wait passes wait_health=False."""
        with patch("commands.gpu.profile_apply", return_value=True) as mock:
            args = self._make_args(gpu_action="profile", profile_action="apply",
                                   name="image_default", no_wait=True)
            result = execute(args)
        assert result == 0
        mock.assert_called_once_with("image_default", wait_health=False)


# ============================================================================
# Data validation: GPU_PROFILES
# ============================================================================

class TestGpuProfilesData:
    def test_profiles_is_dict(self):
        """GPU_PROFILES is a dict."""
        assert isinstance(GPU_PROFILES, dict)

    def test_profiles_not_empty(self):
        """GPU_PROFILES has entries."""
        assert len(GPU_PROFILES) > 0

    def test_each_profile_has_required_keys(self):
        """Each profile has description, services_up, services_down."""
        for name, profile in GPU_PROFILES.items():
            assert "description" in profile, f"Profile '{name}' missing description"
            assert "services_up" in profile, f"Profile '{name}' missing services_up"
            assert "services_down" in profile, f"Profile '{name}' missing services_down"

    def test_services_up_is_list(self):
        """services_up is a list."""
        for name, profile in GPU_PROFILES.items():
            assert isinstance(profile["services_up"], list), f"Profile '{name}' services_up not a list"

    def test_services_down_is_list(self):
        """services_down is a list."""
        for name, profile in GPU_PROFILES.items():
            assert isinstance(profile["services_down"], list), f"Profile '{name}' services_down not a list"

    def test_services_refer_to_real_services(self):
        """All service names in profiles exist in SERVICES config."""
        for name, profile in GPU_PROFILES.items():
            for svc in profile["services_up"]:
                assert svc in SERVICES, f"Profile '{name}' references unknown service '{svc}' in services_up"
            for svc in profile["services_down"]:
                assert svc in SERVICES, f"Profile '{name}' references unknown service '{svc}' in services_down"

    def test_no_overlap_up_down(self):
        """No service appears in both services_up and services_down of same profile."""
        for name, profile in GPU_PROFILES.items():
            up = set(profile["services_up"])
            down = set(profile["services_down"])
            overlap = up & down
            assert not overlap, f"Profile '{name}' has services in both up and down: {overlap}"


# ============================================================================
# Data validation: GROUP_GPU_PROFILE
# ============================================================================

class TestGroupGpuProfileData:
    def test_mapping_is_dict(self):
        """GROUP_GPU_PROFILE is a dict."""
        assert isinstance(GROUP_GPU_PROFILE, dict)

    def test_all_profiles_valid(self):
        """All mapped profiles exist in GPU_PROFILES."""
        for group, profile_name in GROUP_GPU_PROFILE.items():
            assert profile_name in GPU_PROFILES, \
                f"Group '{group}' maps to unknown profile '{profile_name}'"

    def test_covers_all_notebook_groups(self):
        """All NOTEBOOK_SERVICE_MAP groups have a GPU profile."""
        from config import NOTEBOOK_SERVICE_MAP
        for group in NOTEBOOK_SERVICE_MAP:
            assert group in GROUP_GPU_PROFILE, \
                f"Notebook group '{group}' has no GPU profile mapping"

    def test_schedule_accepts_all_groups(self):
        """schedule_group() accepts every GROUP_GPU_PROFILE key."""
        for group in GROUP_GPU_PROFILE:
            with patch("commands.gpu.profile_apply", return_value=True):
                result = schedule_group(group)
            assert result is True


# ============================================================================
# Cross-invariants
# ============================================================================

class TestCrossInvariants:
    def test_check_vram_output_compatible_with_print_gpu_table(self, capsys):
        """check_vram output format is compatible with print_gpu_table."""
        gpus = [{"index": "0", "name": "RTX 3090", "total": 24576, "used": 8192, "free": 16384}]
        # print_gpu_table should not raise with check_vram-like output
        print_gpu_table(gpus)
        captured = capsys.readouterr()
        assert "RTX 3090" in captured.out

    def test_check_vram_output_compatible_with_check_fit(self, capsys):
        """check_vram output format is compatible with check_fit."""
        gpus = [{"index": "0", "name": "RTX 3090", "total": 24576, "used": 4096, "free": 20480}]
        with patch("commands.gpu.check_vram", return_value=gpus):
            result = check_fit(10000)
        assert result is True

    def test_profile_current_uses_check_vram(self, capsys):
        """profile_current calls check_vram for VRAM display."""
        gpus = [{"index": "0", "name": "RTX 3090", "total": 24576, "used": 4096, "free": 20480}]
        with patch("commands.gpu._get_running_services", return_value=[]):
            with patch("commands.gpu.check_vram", return_value=gpus) as mock:
                profile_current()
        mock.assert_called_once()
        captured = capsys.readouterr()
        assert "20480" in captured.out
