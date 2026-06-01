"""Tests for genai-stack commands/auth.py — CLI facade for GenAIAuthManager."""

import importlib.util
import sys
import types
from pathlib import Path
from unittest.mock import MagicMock, patch

import pytest

# --- Load auth.py ---
_AUTH_PATH = Path(__file__).resolve().parent.parent.parent / "genai-stack" / "commands" / "auth.py"
_auth_spec = importlib.util.spec_from_file_location("genai_auth", _AUTH_PATH)
_auth_mod = importlib.util.module_from_spec(_auth_spec)

# Stub core.auth_manager so auth.py `from core.auth_manager import GenAIAuthManager` resolves
_saved_modules = dict(sys.modules)
_mock_manager_cls = MagicMock(name="GenAIAuthManager")
sys.modules["core"] = types.ModuleType("core")
sys.modules["core.auth_manager"] = types.ModuleType("core.auth_manager")
sys.modules["core"].auth_manager = sys.modules["core.auth_manager"]
sys.modules["core.auth_manager"].GenAIAuthManager = _mock_manager_cls

_auth_spec.loader.exec_module(_auth_mod)

# Restore sys.modules
sys.modules.clear()
sys.modules.update(_saved_modules)

register = _auth_mod.register
execute = _auth_mod.execute


def _args(action="init", force=False, json_output=False, raw=False):
    """Build a mock args namespace."""
    return MagicMock(
        action=action,
        force=force,
        json=json_output,
        raw=raw,
    )


# ============================================================================
# Tests for register()
# ============================================================================


class TestRegister:
    """Tests for register() — CLI subparser creation."""

    def test_register_creates_subparser(self):
        """register() adds 'auth' subparser without error."""
        import argparse

        parser = argparse.ArgumentParser()
        subparsers = parser.add_subparsers(dest="command")
        register(subparsers)
        args = parser.parse_args(["auth", "init"])
        assert args.action == "init"

    def test_register_all_actions(self):
        """All 5 auth actions are accepted."""
        import argparse

        parser = argparse.ArgumentParser()
        subparsers = parser.add_subparsers(dest="command")
        register(subparsers)
        for action in ["init", "sync", "audit", "get-token", "reconstruct-env"]:
            args = parser.parse_args(["auth", action])
            assert args.action == action

    def test_register_invalid_action(self):
        """Invalid action is rejected."""
        import argparse

        parser = argparse.ArgumentParser()
        subparsers = parser.add_subparsers(dest="command")
        register(subparsers)
        with pytest.raises(SystemExit):
            parser.parse_args(["auth", "nonexistent"])

    def test_register_force_flag(self):
        """--force flag is parsed."""
        import argparse

        parser = argparse.ArgumentParser()
        subparsers = parser.add_subparsers(dest="command")
        register(subparsers)
        args = parser.parse_args(["auth", "init", "--force"])
        assert args.force is True

    def test_register_json_flag(self):
        """--json flag is parsed."""
        import argparse

        parser = argparse.ArgumentParser()
        subparsers = parser.add_subparsers(dest="command")
        register(subparsers)
        args = parser.parse_args(["auth", "audit", "--json"])
        assert args.json is True

    def test_register_raw_flag(self):
        """--raw flag is parsed."""
        import argparse

        parser = argparse.ArgumentParser()
        subparsers = parser.add_subparsers(dest="command")
        register(subparsers)
        args = parser.parse_args(["auth", "get-token", "--raw"])
        assert args.raw is True


# ============================================================================
# Tests for execute()
# ============================================================================


class TestExecuteInit:
    """Tests for execute() with action='init'."""

    def test_init_config_exists_no_force(self):
        """init returns 1 when config exists and --force not set."""
        mock_mgr = MagicMock()
        mock_mgr.config_file = MagicMock()
        mock_mgr.config_file.exists.return_value = True
        with patch.object(_auth_mod, "GenAIAuthManager", return_value=mock_mgr):
            result = execute(_args("init", force=False))
        assert result == 1

    def test_init_config_exists_with_force(self):
        """init proceeds when config exists and --force is set."""
        mock_mgr = MagicMock()
        mock_mgr.config_file = MagicMock()
        mock_mgr.config_file.exists.return_value = True
        with patch.object(_auth_mod, "GenAIAuthManager", return_value=mock_mgr):
            result = execute(_args("init", force=True))
        assert result == 0
        mock_mgr.create_unified_config.assert_called_once()
        mock_mgr.synchronize_credentials.assert_called_once()

    def test_init_config_missing(self):
        """init proceeds when config doesn't exist."""
        mock_mgr = MagicMock()
        mock_mgr.config_file = MagicMock()
        mock_mgr.config_file.exists.return_value = False
        with patch.object(_auth_mod, "GenAIAuthManager", return_value=mock_mgr):
            result = execute(_args("init", force=False))
        assert result == 0
        mock_mgr.create_unified_config.assert_called_once()

    def test_init_outputs_message_on_existing(self, capsys):
        """init prints message when config exists without force."""
        mock_mgr = MagicMock()
        mock_mgr.config_file = MagicMock()
        mock_mgr.config_file.exists.return_value = True
        with patch.object(_auth_mod, "GenAIAuthManager", return_value=mock_mgr):
            execute(_args("init", force=False))
        captured = capsys.readouterr()
        assert "force" in captured.out.lower()


class TestExecuteSync:
    """Tests for execute() with action='sync'."""

    def test_sync_success(self):
        """sync returns 0 on success."""
        mock_mgr = MagicMock()
        mock_mgr.synchronize_credentials.return_value = True
        with patch.object(_auth_mod, "GenAIAuthManager", return_value=mock_mgr):
            result = execute(_args("sync"))
        assert result == 0

    def test_sync_failure(self):
        """sync returns 1 on failure."""
        mock_mgr = MagicMock()
        mock_mgr.synchronize_credentials.return_value = False
        with patch.object(_auth_mod, "GenAIAuthManager", return_value=mock_mgr):
            result = execute(_args("sync"))
        assert result == 1


class TestExecuteAudit:
    """Tests for execute() with action='audit'."""

    def test_audit_text_output(self, capsys):
        """audit prints text report."""
        mock_report = MagicMock()
        mock_report.timestamp = "2026-06-01"
        mock_report.locations = []
        mock_report.inconsistencies = []
        mock_mgr = MagicMock()
        mock_mgr.audit_security.return_value = mock_report
        with patch.object(_auth_mod, "GenAIAuthManager", return_value=mock_mgr):
            result = execute(_args("audit"))
        assert result == 0
        captured = capsys.readouterr()
        assert "RAPPORT" in captured.out

    def test_audit_json_output(self, capsys):
        """audit --json prints JSON report."""
        mock_report = MagicMock()
        mock_report.to_dict.return_value = {"timestamp": "2026-06-01", "locations": []}
        mock_mgr = MagicMock()
        mock_mgr.audit_security.return_value = mock_report
        with patch.object(_auth_mod, "GenAIAuthManager", return_value=mock_mgr):
            result = execute(_args("audit", json_output=True))
        assert result == 0
        captured = capsys.readouterr()
        assert "timestamp" in captured.out

    def test_audit_with_inconsistencies(self, capsys):
        """audit prints inconsistencies when found."""
        mock_report = MagicMock()
        mock_report.timestamp = "2026-06-01"
        mock_report.locations = []
        mock_report.inconsistencies = [{"path": "/tmp/test", "issue": "mismatch"}]
        mock_mgr = MagicMock()
        mock_mgr.audit_security.return_value = mock_report
        with patch.object(_auth_mod, "GenAIAuthManager", return_value=mock_mgr):
            result = execute(_args("audit"))
        assert result == 0
        captured = capsys.readouterr()
        assert "INCOHERENCES" in captured.out

    def test_audit_with_locations(self, capsys):
        """audit prints location statuses."""
        mock_loc = MagicMock()
        mock_loc.is_valid = True
        mock_loc.exists = True
        mock_loc.description = "Test config"
        mock_loc.path = "/tmp/test.env"
        mock_report = MagicMock()
        mock_report.timestamp = "2026-06-01"
        mock_report.locations = [mock_loc]
        mock_report.inconsistencies = []
        mock_mgr = MagicMock()
        mock_mgr.audit_security.return_value = mock_report
        with patch.object(_auth_mod, "GenAIAuthManager", return_value=mock_mgr):
            execute(_args("audit"))
        captured = capsys.readouterr()
        assert "OK" in captured.out
        assert "Test config" in captured.out

    def test_audit_missing_location(self, capsys):
        """audit shows MISSING for non-existent location."""
        mock_loc = MagicMock()
        mock_loc.is_valid = False
        mock_loc.exists = False
        mock_loc.description = "Missing file"
        mock_loc.path = "/tmp/missing.env"
        mock_report = MagicMock()
        mock_report.timestamp = "2026-06-01"
        mock_report.locations = [mock_loc]
        mock_report.inconsistencies = []
        mock_mgr = MagicMock()
        mock_mgr.audit_security.return_value = mock_report
        with patch.object(_auth_mod, "GenAIAuthManager", return_value=mock_mgr):
            execute(_args("audit"))
        captured = capsys.readouterr()
        assert "MISSING" in captured.out


class TestExecuteGetToken:
    """Tests for execute() with action='get-token'."""

    def test_get_token_no_config(self, capsys):
        """get-token returns 1 when no config found."""
        mock_mgr = MagicMock()
        mock_mgr.load_config.return_value = None
        with patch.object(_auth_mod, "GenAIAuthManager", return_value=mock_mgr):
            result = execute(_args("get-token"))
        assert result == 1
        captured = capsys.readouterr()
        assert "init" in captured.out.lower()

    def test_get_token_hash(self, capsys):
        """get-token prints bcrypt hash by default."""
        mock_mgr = MagicMock()
        mock_mgr.load_config.return_value = {"bcrypt_hash": "hash123", "raw_token": "raw456"}
        with patch.object(_auth_mod, "GenAIAuthManager", return_value=mock_mgr):
            result = execute(_args("get-token"))
        assert result == 0
        captured = capsys.readouterr()
        assert "hash123" in captured.out

    def test_get_token_raw(self, capsys):
        """get-token --raw prints raw token."""
        mock_mgr = MagicMock()
        mock_mgr.load_config.return_value = {"bcrypt_hash": "hash123", "raw_token": "raw456"}
        with patch.object(_auth_mod, "GenAIAuthManager", return_value=mock_mgr):
            result = execute(_args("get-token", raw=True))
        assert result == 0
        captured = capsys.readouterr()
        assert "raw456" in captured.out

    def test_get_token_empty(self, capsys):
        """get-token returns 1 when token not available."""
        mock_mgr = MagicMock()
        mock_mgr.load_config.return_value = {"bcrypt_hash": "", "raw_token": ""}
        with patch.object(_auth_mod, "GenAIAuthManager", return_value=mock_mgr):
            result = execute(_args("get-token"))
        assert result == 1
        captured = capsys.readouterr()
        assert "non disponible" in captured.out.lower()


class TestExecuteReconstructEnv:
    """Tests for execute() with action='reconstruct-env'."""

    def test_reconstruct_env_success(self):
        """reconstruct-env returns 0 on success."""
        mock_mgr = MagicMock()
        mock_mgr.reconstruct_env_file.return_value = True
        with patch.object(_auth_mod, "GenAIAuthManager", return_value=mock_mgr):
            result = execute(_args("reconstruct-env"))
        assert result == 0

    def test_reconstruct_env_failure(self):
        """reconstruct-env returns 1 on failure."""
        mock_mgr = MagicMock()
        mock_mgr.reconstruct_env_file.return_value = False
        with patch.object(_auth_mod, "GenAIAuthManager", return_value=mock_mgr):
            result = execute(_args("reconstruct-env"))
        assert result == 1


class TestExecuteUnknown:
    """Tests for execute() with unknown action."""

    def test_unknown_action_returns_1(self):
        """Unknown action returns 1."""
        mock_mgr = MagicMock()
        with patch.object(_auth_mod, "GenAIAuthManager", return_value=mock_mgr):
            result = execute(_args("unknown_action"))
        assert result == 1


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
