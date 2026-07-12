"""Tests for genai-stack commands/quant.py — offline with mocked deps."""

import importlib.util
import sys
import types
from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest

# --- Build mock dependencies ---
_mock_quant_configs = {
    "whisper": {"name": "Whisper", "notes": "Already FP16 optimized"},
    "musicgen": {"name": "MusicGen", "notes": "Already FP16 optimized"},
    "hunyuan": {"name": "Hunyuan", "notes": "Already FP16 optimized"},
    "forge": {"name": "Forge", "notes": "Already FP16 optimized"},
}

_mock_configure_zimage = MagicMock(return_value=True)
_mock_configure_qwen = MagicMock(return_value=True)
_mock_show_summary = MagicMock()

_mock_cmq_mod = types.SimpleNamespace(
    QUANTIZATION_CONFIGS=_mock_quant_configs,
    configure_zimage=_mock_configure_zimage,
    configure_qwen=_mock_configure_qwen,
    show_summary=_mock_show_summary,
)

_MODULES_PATCH = {
    "configure_max_quantization": _mock_cmq_mod,
}

_QUANT_PATH = Path(__file__).resolve().parent.parent.parent / "genai-stack" / "commands" / "quant.py"


@pytest.fixture(scope="module", autouse=True)
def _setup_module():
    """Inject mock modules with clean teardown."""
    saved = {}
    for key, val in _MODULES_PATCH.items():
        saved[key] = sys.modules.get(key)
        sys.modules[key] = val

    global _quant_mod
    _spec = importlib.util.spec_from_file_location("quant_cmd", _QUANT_PATH)
    _quant_mod = importlib.util.module_from_spec(_spec)
    _spec.loader.exec_module(_quant_mod)

    yield

    for key, orig in saved.items():
        if orig is None:
            sys.modules.pop(key, None)
        else:
            sys.modules[key] = orig


# ============================================================================
# Tests for register()
# ============================================================================


class TestRegister:
    """Tests for register() — CLI parser setup."""

    def test_register_creates_subparser(self):
        import argparse
        parser = argparse.ArgumentParser()
        subparsers = parser.add_subparsers(dest="command")
        _quant_mod.register(subparsers)
        args = parser.parse_args(["quant", "summary"])
        assert args.quant_action == "summary"

    def test_register_apply_with_service(self):
        import argparse
        parser = argparse.ArgumentParser()
        subparsers = parser.add_subparsers(dest="command")
        _quant_mod.register(subparsers)
        args = parser.parse_args(["quant", "apply", "zimage"])
        assert args.service == "zimage"

    def test_register_apply_with_dry_run(self):
        import argparse
        parser = argparse.ArgumentParser()
        subparsers = parser.add_subparsers(dest="command")
        _quant_mod.register(subparsers)
        args = parser.parse_args(["quant", "apply", "--dry-run"])
        assert args.dry_run is True

    def test_register_apply_all_default(self):
        import argparse
        parser = argparse.ArgumentParser()
        subparsers = parser.add_subparsers(dest="command")
        _quant_mod.register(subparsers)
        args = parser.parse_args(["quant", "apply"])
        assert args.service is None  # nargs='?', const='all'

    def test_register_apply_invalid_service(self):
        import argparse
        parser = argparse.ArgumentParser()
        subparsers = parser.add_subparsers(dest="command")
        _quant_mod.register(subparsers)
        with pytest.raises(SystemExit):
            parser.parse_args(["quant", "apply", "invalid_service"])


# ============================================================================
# Tests for execute()
# ============================================================================


class TestExecuteSummary:
    """Tests for execute() — summary action."""

    def test_summary_calls_show_summary(self):
        import argparse
        _mock_show_summary.reset_mock()
        args = argparse.Namespace(quant_action="summary")
        result = _quant_mod.execute(args)
        _mock_show_summary.assert_called_once()
        assert result == 0

    def test_no_quant_action_calls_show_summary(self):
        import argparse
        _mock_show_summary.reset_mock()
        args = argparse.Namespace()
        result = _quant_mod.execute(args)
        _mock_show_summary.assert_called_once()
        assert result == 0


class TestExecuteApply:
    """Tests for execute() — apply action."""

    def test_apply_all_services(self, capsys):
        import argparse
        _mock_configure_zimage.reset_mock()
        _mock_configure_qwen.reset_mock()
        args = argparse.Namespace(quant_action="apply", service=None, dry_run=False)
        result = _quant_mod.execute(args)
        assert result == 0
        _mock_configure_zimage.assert_called_once()
        _mock_configure_qwen.assert_called_once()
        captured = capsys.readouterr()
        assert "APPLICATION" in captured.out

    def test_apply_dry_run(self, capsys):
        import argparse
        _mock_configure_zimage.reset_mock()
        args = argparse.Namespace(quant_action="apply", service=None, dry_run=True)
        result = _quant_mod.execute(args)
        assert result == 0
        captured = capsys.readouterr()
        assert "DRY RUN" in captured.out

    def test_apply_zimage_only(self):
        import argparse
        _mock_configure_zimage.reset_mock()
        _mock_configure_qwen.reset_mock()
        args = argparse.Namespace(quant_action="apply", service="zimage", dry_run=False)
        result = _quant_mod.execute(args)
        assert result == 0
        _mock_configure_zimage.assert_called_once()
        _mock_configure_qwen.assert_not_called()

    def test_apply_qwen_only(self):
        import argparse
        _mock_configure_zimage.reset_mock()
        _mock_configure_qwen.reset_mock()
        args = argparse.Namespace(quant_action="apply", service="qwen", dry_run=False)
        result = _quant_mod.execute(args)
        assert result == 0
        _mock_configure_zimage.assert_not_called()
        _mock_configure_qwen.assert_called_once()

    def test_apply_all_shows_already_configured(self, capsys):
        import argparse
        args = argparse.Namespace(quant_action="apply", service=None, dry_run=False)
        _quant_mod.execute(args)
        captured = capsys.readouterr()
        assert "Whisper" in captured.out
        assert "MusicGen" in captured.out

    def test_apply_zimage_does_not_show_already_configured(self, capsys):
        import argparse
        args = argparse.Namespace(quant_action="apply", service="zimage", dry_run=False)
        _quant_mod.execute(args)
        captured = capsys.readouterr()
        assert "Whisper" not in captured.out

    def test_configure_zimage_receives_env_path(self):
        import argparse
        _mock_configure_zimage.reset_mock()
        args = argparse.Namespace(quant_action="apply", service="zimage", dry_run=False)
        _quant_mod.execute(args)
        call_args = _mock_configure_zimage.call_args
        # First positional arg should be a Path ending in .env
        env_path = call_args[0][0]
        assert isinstance(env_path, Path)
        assert str(env_path).endswith(".env")


class TestExecuteReturnCode:
    """Tests for execute() — return codes."""

    def test_returns_zero_on_unknown_action(self):
        import argparse
        args = argparse.Namespace(quant_action="unknown")
        result = _quant_mod.execute(args)
        assert result == 0


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
