#!/usr/bin/env python3
"""
Tests for scripts/genai-stack/configure_max_quantization.py

Covers: QUANTIZATION_CONFIGS data validation, configure_zimage env file
manipulation. Uses tmp_path fixtures (no real Docker/env files touched).

LIVE: imported by commands/quant.py (genai.py quant subcommand).
"""

import pytest
import sys
from pathlib import Path

# Add genai-stack to sys.path
_genai_dir = str(Path(__file__).resolve().parent.parent / "genai-stack")
if _genai_dir not in sys.path:
    sys.path.insert(0, _genai_dir)

from configure_max_quantization import QUANTIZATION_CONFIGS, configure_zimage


# ─── QUANTIZATION_CONFIGS data structure ──────────────────────────────


class TestQuantizationConfigs:
    def test_is_dict(self):
        assert isinstance(QUANTIZATION_CONFIGS, dict)

    def test_required_services_present(self):
        expected = {"zimage", "qwen", "whisper", "musicgen", "hunyuan", "forge"}
        assert set(QUANTIZATION_CONFIGS.keys()) == expected

    def test_each_config_has_name(self):
        for key, cfg in QUANTIZATION_CONFIGS.items():
            assert "name" in cfg, f"Missing 'name' in {key}"
            assert isinstance(cfg["name"], str)
            assert len(cfg["name"]) > 0

    def test_each_config_has_description(self):
        for key, cfg in QUANTIZATION_CONFIGS.items():
            assert "description" in cfg, f"Missing 'description' in {key}"
            assert isinstance(cfg["description"], str)

    def test_each_config_has_notes(self):
        for key, cfg in QUANTIZATION_CONFIGS.items():
            assert "notes" in cfg, f"Missing 'notes' in {key}"
            assert isinstance(cfg["notes"], str)

    def test_vram_format_valid(self):
        """VRAM strings should be like '10GB' or '5GB'."""
        for key, cfg in QUANTIZATION_CONFIGS.items():
            if "vram_before" in cfg:
                assert cfg["vram_before"].endswith("GB"), \
                    f"{key}: vram_before should end with 'GB', got '{cfg['vram_before']}'"
                float(cfg["vram_before"].replace("GB", ""))
            if "vram_after" in cfg:
                assert cfg["vram_after"].endswith("GB"), \
                    f"{key}: vram_after should end with 'GB', got '{cfg['vram_after']}'"
                float(cfg["vram_after"].replace("GB", ""))
            if "vram" in cfg:
                assert cfg["vram"].endswith("GB"), \
                    f"{key}: vram should end with 'GB', got '{cfg['vram']}'"
                float(cfg["vram"].replace("GB", ""))

    def test_savings_format(self):
        """Savings should be a percentage string like '-50%'."""
        for key, cfg in QUANTIZATION_CONFIGS.items():
            if "savings" in cfg:
                assert cfg["savings"].startswith("-"), \
                    f"{key}: savings should start with '-', got '{cfg['savings']}'"
                assert cfg["savings"].endswith("%"), \
                    f"{key}: savings should end with '%', got '{cfg['savings']}'"

    def test_zimage_has_env_config(self):
        """Z-Image service should have docker_compose and env_file."""
        zimage = QUANTIZATION_CONFIGS["zimage"]
        assert "docker_compose" in zimage
        assert "env_file" in zimage
        assert "env_vars" in zimage
        assert "VLLM_QUANTIZATION" in zimage["env_vars"]

    def test_zimage_restart_required(self):
        assert QUANTIZATION_CONFIGS["zimage"]["restart_required"] is True

    def test_qwen_has_model_info(self):
        """Qwen config should have models list and workflow."""
        qwen = QUANTIZATION_CONFIGS["qwen"]
        assert "models" in qwen
        assert isinstance(qwen["models"], list)
        assert len(qwen["models"]) > 0
        assert "workflow" in qwen

    def test_already_configured_services(self):
        """Whisper, musicgen should be marked as already configured."""
        for key in ["whisper", "musicgen"]:
            assert QUANTIZATION_CONFIGS[key].get("status") == "already_configured"

    def test_forge_no_quantization(self):
        assert QUANTIZATION_CONFIGS["forge"].get("status") == "no_quantization"

    def test_savings_reflect_vram_reduction(self):
        """Savings percentage should match vram_before -> vram_after reduction."""
        for key, cfg in QUANTIZATION_CONFIGS.items():
            if "vram_before" in cfg and "vram_after" in cfg and "savings" in cfg:
                before = float(cfg["vram_before"].replace("GB", ""))
                after = float(cfg["vram_after"].replace("GB", ""))
                expected_pct = -(1 - after / before) * 100
                # Parse savings as signed value: "-50%" -> -50.0
                actual_pct = float(cfg["savings"].replace("%", ""))
                assert abs(expected_pct - actual_pct) < 2, \
                    f"{key}: savings {cfg['savings']} doesn't match " \
                    f"{cfg['vram_before']}->{cfg['vram_after']} ({expected_pct:.0f}%)"


# ─── configure_zimage ─────────────────────────────────────────────────


class TestConfigureZimage:
    def test_returns_false_if_env_missing(self, tmp_path):
        """Non-existent env file should return False."""
        env_file = tmp_path / "nonexistent.env"
        assert configure_zimage(env_file) is False

    def test_already_configured(self, tmp_path):
        """Already-configured file should return True without changes."""
        env_file = tmp_path / ".env"
        env_file.write_text(
            "VLLM_MODEL=zimage\n"
            "# VLLM_QUANTIZATION=bfloat16\n"
            "VLLM_QUANTIZATION=fp8\n"
        )
        original = env_file.read_text()
        result = configure_zimage(env_file)
        assert result is True
        # File should NOT change
        assert env_file.read_text() == original

    def test_applies_fp8_config(self, tmp_path):
        """File with active bfloat16 and commented fp8 should swap to active fp8."""
        env_file = tmp_path / ".env"
        env_file.write_text(
            "VLLM_MODEL=zimage\n"
            "# VLLM_QUANTIZATION=fp8\n"
            "VLLM_QUANTIZATION=bfloat16\n"
        )
        result = configure_zimage(env_file)
        assert result is True
        content = env_file.read_text()
        assert "VLLM_QUANTIZATION=fp8\n" in content
        assert "# VLLM_QUANTIZATION=bfloat16" in content
        # No uncommented bfloat16 line (check lines, not substrings)
        lines = content.splitlines()
        assert not any(
            line == "VLLM_QUANTIZATION=bfloat16" for line in lines
        )

    def test_dry_run_does_not_modify(self, tmp_path):
        """Dry run should not modify the file."""
        env_file = tmp_path / ".env"
        env_file.write_text(
            "VLLM_MODEL=zimage\n"
            "# VLLM_QUANTIZATION=fp8\n"
            "VLLM_QUANTIZATION=bfloat16\n"
        )
        original = env_file.read_text()
        result = configure_zimage(env_file, dry_run=True)
        assert result is True
        # File should NOT change in dry run
        assert env_file.read_text() == original

    def test_unconfigures_and_reconfigures(self, tmp_path):
        """Applying twice: first activates fp8, second confirms already configured."""
        env_file = tmp_path / ".env"
        env_file.write_text(
            "# VLLM_QUANTIZATION=fp8\n"
            "VLLM_QUANTIZATION=bfloat16\n"
        )
        # First apply: swaps to fp8
        assert configure_zimage(env_file) is True
        content_after_first = env_file.read_text()
        assert "VLLM_QUANTIZATION=fp8\n" in content_after_first
        # Second apply (already configured)
        assert configure_zimage(env_file) is True
        assert env_file.read_text() == content_after_first

    def test_preserves_other_content(self, tmp_path):
        """Other env vars should be preserved during configuration."""
        env_file = tmp_path / ".env"
        original = (
            "VLLM_MODEL=Qwen/Qwen2.5-VL-3B\n"
            "# VLLM_QUANTIZATION=fp8\n"
            "VLLM_QUANTIZATION=bfloat16\n"
            "VLLM_PORT=8000\n"
            "OTHER_VAR=hello\n"
        )
        env_file.write_text(original)
        configure_zimage(env_file)
        content = env_file.read_text()
        assert "VLLM_MODEL=Qwen/Qwen2.5-VL-3B" in content
        assert "VLLM_PORT=8000" in content
        assert "OTHER_VAR=hello" in content

    def test_empty_file_returns_true(self, tmp_path):
        """Empty file (no bfloat16 or fp8) — not already configured, replace is no-op."""
        env_file = tmp_path / ".env"
        env_file.write_text("")
        result = configure_zimage(env_file)
        assert result is True

    def test_bfloat16_only_no_fp8_comment(self, tmp_path):
        """File with bfloat16 but no commented fp8 — only comments out bfloat16."""
        env_file = tmp_path / ".env"
        env_file.write_text(
            "VLLM_MODEL=zimage\n"
            "VLLM_QUANTIZATION=bfloat16\n"
        )
        result = configure_zimage(env_file)
        assert result is True
        content = env_file.read_text()
        # bfloat16 gets commented out
        assert "# VLLM_QUANTIZATION=bfloat16" in content
        # fp8 NOT added (no commented line to uncomment)
        assert "VLLM_QUANTIZATION=fp8" not in content


# ─── Cross-invariants ─────────────────────────────────────────────────


class TestCrossInvariants:
    def test_zimage_env_var_matches_config(self):
        """The env_var value in config should be 'fp8'."""
        assert QUANTIZATION_CONFIGS["zimage"]["env_vars"]["VLLM_QUANTIZATION"] == "fp8"

    def test_configure_zimage_uses_correct_value(self, tmp_path):
        """configure_zimage should set VLLM_QUANTIZATION to the config value."""
        expected_val = QUANTIZATION_CONFIGS["zimage"]["env_vars"]["VLLM_QUANTIZATION"]
        env_file = tmp_path / ".env"
        env_file.write_text(
            f"# VLLM_QUANTIZATION={expected_val}\n"
            "VLLM_QUANTIZATION=bfloat16\n"
        )
        configure_zimage(env_file)
        assert f"VLLM_QUANTIZATION={expected_val}\n" in env_file.read_text()

    def test_total_vram_savings_reasonable(self):
        """Total VRAM savings across quantifiable services should be significant."""
        total_before = 0
        total_after = 0
        for key, cfg in QUANTIZATION_CONFIGS.items():
            if "vram_before" in cfg and "vram_after" in cfg:
                total_before += float(cfg["vram_before"].replace("GB", ""))
                total_after += float(cfg["vram_after"].replace("GB", ""))
        # Should save at least 50% total
        assert total_after < total_before * 0.5
