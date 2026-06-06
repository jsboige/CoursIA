#!/usr/bin/env python3
"""
Tests for scripts/genai-stack/commands/auth.py

Covers: register() argparse setup, execute() dispatch logic with mocked
GenAIAuthManager, main() standalone entry point.
All tests mock GenAIAuthManager to avoid filesystem/network side effects.

LIVE: 5 callers (docker-configs/services auth_middleware.py,
genai-stack/archive/core/*, genai-stack commands).
"""

import argparse
import sys
from pathlib import Path
from unittest.mock import MagicMock, patch, PropertyMock

import pytest

# Add genai-stack to sys.path
_genai_root = str(Path(__file__).resolve().parent.parent / "genai-stack")
if _genai_root not in sys.path:
    sys.path.insert(0, _genai_root)

# Must import AFTER sys.path is set
from commands.auth import register, execute


# ─── register ──────────────────────────────────────────────────────────


class TestRegister:
    def test_adds_auth_subparser(self):
        parser = argparse.ArgumentParser()
        subparsers = parser.add_subparsers(dest="command")
        register(subparsers)
        # Verify 'auth' subcommand is parseable
        args = parser.parse_args(["auth", "init"])
        assert args.action == "init"

    def test_registers_all_actions(self):
        parser = argparse.ArgumentParser()
        subparsers = parser.add_subparsers(dest="command")
        register(subparsers)
        for action in ["init", "sync", "audit", "get-token", "reconstruct-env"]:
            args = parser.parse_args(["auth", action])
            assert args.action == action

    def test_force_flag(self):
        parser = argparse.ArgumentParser()
        subparsers = parser.add_subparsers(dest="command")
        register(subparsers)
        args = parser.parse_args(["auth", "init", "--force"])
        assert args.force is True

    def test_force_default_false(self):
        parser = argparse.ArgumentParser()
        subparsers = parser.add_subparsers(dest="command")
        register(subparsers)
        args = parser.parse_args(["auth", "init"])
        assert args.force is False

    def test_json_flag(self):
        parser = argparse.ArgumentParser()
        subparsers = parser.add_subparsers(dest="command")
        register(subparsers)
        args = parser.parse_args(["auth", "audit", "--json"])
        assert args.json is True

    def test_json_default_false(self):
        parser = argparse.ArgumentParser()
        subparsers = parser.add_subparsers(dest="command")
        register(subparsers)
        args = parser.parse_args(["auth", "audit"])
        assert args.json is False

    def test_raw_flag(self):
        parser = argparse.ArgumentParser()
        subparsers = parser.add_subparsers(dest="command")
        register(subparsers)
        args = parser.parse_args(["auth", "get-token", "--raw"])
        assert args.raw is True

    def test_raw_default_false(self):
        parser = argparse.ArgumentParser()
        subparsers = parser.add_subparsers(dest="command")
        register(subparsers)
        args = parser.parse_args(["auth", "get-token"])
        assert args.raw is False

    def test_invalid_action_raises(self):
        parser = argparse.ArgumentParser()
        subparsers = parser.add_subparsers(dest="command")
        register(subparsers)
        with pytest.raises(SystemExit):
            parser.parse_args(["auth", "invalid-action"])


# ─── execute — init ────────────────────────────────────────────────────


class TestExecuteInit:
    def _make_args(self, force=False):
        args = argparse.Namespace(action="init", force=force)
        return args

    @patch("commands.auth.GenAIAuthManager")
    def test_init_config_exists_no_force(self, MockManager):
        mock_mgr = MagicMock()
        mock_mgr.config_file.exists.return_value = True
        MockManager.return_value = mock_mgr
        args = self._make_args(force=False)
        result = execute(args)
        assert result == 1
        mock_mgr.create_unified_config.assert_not_called()

    @patch("commands.auth.GenAIAuthManager")
    def test_init_config_exists_with_force(self, MockManager):
        mock_mgr = MagicMock()
        mock_mgr.config_file.exists.return_value = True
        MockManager.return_value = mock_mgr
        args = self._make_args(force=True)
        result = execute(args)
        assert result == 0
        mock_mgr.create_unified_config.assert_called_once()
        mock_mgr.synchronize_credentials.assert_called_once()

    @patch("commands.auth.GenAIAuthManager")
    def test_init_config_not_exists(self, MockManager):
        mock_mgr = MagicMock()
        mock_mgr.config_file.exists.return_value = False
        MockManager.return_value = mock_mgr
        args = self._make_args(force=False)
        result = execute(args)
        assert result == 0
        mock_mgr.create_unified_config.assert_called_once()


# ─── execute — sync ────────────────────────────────────────────────────


class TestExecuteSync:
    def _make_args(self):
        return argparse.Namespace(action="sync")

    @patch("commands.auth.GenAIAuthManager")
    def test_sync_success(self, MockManager):
        mock_mgr = MagicMock()
        mock_mgr.synchronize_credentials.return_value = True
        MockManager.return_value = mock_mgr
        result = execute(self._make_args())
        assert result == 0

    @patch("commands.auth.GenAIAuthManager")
    def test_sync_failure(self, MockManager):
        mock_mgr = MagicMock()
        mock_mgr.synchronize_credentials.return_value = False
        MockManager.return_value = mock_mgr
        result = execute(self._make_args())
        assert result == 1


# ─── execute — audit ───────────────────────────────────────────────────


class TestExecuteAudit:
    def _make_args(self, json_output=False):
        return argparse.Namespace(action="audit", json=json_output)

    @patch("commands.auth.GenAIAuthManager")
    def test_audit_text_output(self, MockManager, capsys):
        from core.auth_manager import AuditReport, TokenLocation
        loc = TokenLocation(
            path="/tmp/test",
            type="bcrypt",
            description="Test token",
            exists=True,
            is_valid=True,
        )
        report = AuditReport(
            timestamp="2026-01-01T00:00:00",
            locations=[loc],
            inconsistencies=[],
            recommendations=[],
        )
        mock_mgr = MagicMock()
        mock_mgr.audit_security.return_value = report
        MockManager.return_value = mock_mgr

        result = execute(self._make_args(json_output=False))
        assert result == 0
        captured = capsys.readouterr()
        assert "RAPPORT D'AUDIT" in captured.out
        assert "OK" in captured.out

    @patch("commands.auth.GenAIAuthManager")
    def test_audit_json_output(self, MockManager, capsys):
        from core.auth_manager import AuditReport, TokenLocation
        loc = TokenLocation(
            path="/tmp/test",
            type="bcrypt",
            description="Test token",
            exists=True,
            is_valid=True,
        )
        report = AuditReport(
            timestamp="2026-01-01T00:00:00",
            locations=[loc],
            inconsistencies=[],
            recommendations=[],
        )
        mock_mgr = MagicMock()
        mock_mgr.audit_security.return_value = report
        MockManager.return_value = mock_mgr

        result = execute(self._make_args(json_output=True))
        assert result == 0
        captured = capsys.readouterr()
        assert '"locations"' in captured.out

    @patch("commands.auth.GenAIAuthManager")
    def test_audit_with_inconsistencies(self, MockManager, capsys):
        from core.auth_manager import AuditReport, TokenLocation
        loc = TokenLocation(
            path="/tmp/test",
            type="raw",
            description="Test",
            exists=False,
            is_valid=False,
        )
        report = AuditReport(
            timestamp="2026-01-01",
            locations=[loc],
            inconsistencies=[{"path": "/tmp/test", "issue": "missing"}],
            recommendations=[],
        )
        mock_mgr = MagicMock()
        mock_mgr.audit_security.return_value = report
        MockManager.return_value = mock_mgr

        result = execute(self._make_args(json_output=False))
        assert result == 0
        captured = capsys.readouterr()
        assert "INCOHERENCES" in captured.out

    @patch("commands.auth.GenAIAuthManager")
    def test_audit_fail_location(self, MockManager, capsys):
        from core.auth_manager import AuditReport, TokenLocation
        loc = TokenLocation(
            path="/tmp/bad",
            type="env",
            description="Bad token",
            exists=True,
            is_valid=False,
        )
        report = AuditReport(
            timestamp="2026-01-01",
            locations=[loc],
            inconsistencies=[],
            recommendations=[],
        )
        mock_mgr = MagicMock()
        mock_mgr.audit_security.return_value = report
        MockManager.return_value = mock_mgr

        result = execute(self._make_args(json_output=False))
        assert result == 0
        captured = capsys.readouterr()
        assert "FAIL" in captured.out


# ─── execute — get-token ───────────────────────────────────────────────


class TestExecuteGetToken:
    def _make_args(self, raw=False):
        return argparse.Namespace(action="get-token", raw=raw)

    @patch("commands.auth.GenAIAuthManager")
    def test_get_bcrypt_token(self, MockManager, capsys):
        mock_mgr = MagicMock()
        mock_mgr.load_config.return_value = {"bcrypt_hash": "hash123", "raw_token": "raw456"}
        MockManager.return_value = mock_mgr

        result = execute(self._make_args(raw=False))
        assert result == 0
        captured = capsys.readouterr()
        assert "hash123" in captured.out

    @patch("commands.auth.GenAIAuthManager")
    def test_get_raw_token(self, MockManager, capsys):
        mock_mgr = MagicMock()
        mock_mgr.load_config.return_value = {"bcrypt_hash": "hash123", "raw_token": "raw456"}
        MockManager.return_value = mock_mgr

        result = execute(self._make_args(raw=True))
        assert result == 0
        captured = capsys.readouterr()
        assert "raw456" in captured.out

    @patch("commands.auth.GenAIAuthManager")
    def test_no_config(self, MockManager, capsys):
        mock_mgr = MagicMock()
        mock_mgr.load_config.return_value = None
        MockManager.return_value = mock_mgr

        result = execute(self._make_args())
        assert result == 1
        captured = capsys.readouterr()
        assert "Aucune configuration" in captured.out

    @patch("commands.auth.GenAIAuthManager")
    def test_token_not_available(self, MockManager, capsys):
        mock_mgr = MagicMock()
        mock_mgr.load_config.return_value = {"other_key": "value"}
        MockManager.return_value = mock_mgr

        result = execute(self._make_args())
        assert result == 1
        captured = capsys.readouterr()
        assert "Token non disponible" in captured.out

    @patch("commands.auth.GenAIAuthManager")
    def test_empty_token(self, MockManager, capsys):
        mock_mgr = MagicMock()
        mock_mgr.load_config.return_value = {"bcrypt_hash": "", "raw_token": ""}
        MockManager.return_value = mock_mgr

        result = execute(self._make_args())
        assert result == 1
        captured = capsys.readouterr()
        assert "Token non disponible" in captured.out


# ─── execute — reconstruct-env ─────────────────────────────────────────


class TestExecuteReconstructEnv:
    def _make_args(self):
        return argparse.Namespace(action="reconstruct-env")

    @patch("commands.auth.GenAIAuthManager")
    def test_reconstruct_success(self, MockManager):
        mock_mgr = MagicMock()
        mock_mgr.reconstruct_env_file.return_value = True
        MockManager.return_value = mock_mgr
        result = execute(self._make_args())
        assert result == 0

    @patch("commands.auth.GenAIAuthManager")
    def test_reconstruct_failure(self, MockManager):
        mock_mgr = MagicMock()
        mock_mgr.reconstruct_env_file.return_value = False
        MockManager.return_value = mock_mgr
        result = execute(self._make_args())
        assert result == 1


# ─── execute — unknown action ──────────────────────────────────────────


class TestExecuteUnknown:
    def test_unknown_action_returns_1(self):
        args = argparse.Namespace(action="nonexistent")
        result = execute(args)
        assert result == 1


# ─── Cross-invariants ──────────────────────────────────────────────────


class TestCrossInvariants:
    @patch("commands.auth.GenAIAuthManager")
    def test_all_actions_covered_by_register(self, MockManager):
        """Every action in register() is handled by execute()."""
        parser = argparse.ArgumentParser()
        subparsers = parser.add_subparsers(dest="command")
        register(subparsers)

        mock_mgr = MagicMock()
        mock_mgr.config_file.exists.return_value = False
        mock_mgr.synchronize_credentials.return_value = True
        mock_mgr.audit_security.return_value = MagicMock(
            locations=[], inconsistencies=[], recommendations=[], timestamp="t"
        )
        mock_mgr.load_config.return_value = {"bcrypt_hash": "x"}
        mock_mgr.reconstruct_env_file.return_value = True
        MockManager.return_value = mock_mgr

        actions = ["init", "sync", "audit", "get-token", "reconstruct-env"]
        for action in actions:
            args = parser.parse_args(["auth", action])
            # Should not crash for any registered action
            result = execute(args)
            assert isinstance(result, int)

    @patch("commands.auth.GenAIAuthManager")
    def test_execute_delegates_to_auth_manager(self, MockManager):
        """execute() creates GenAIAuthManager and calls the right method."""
        mock_mgr = MagicMock()
        mock_mgr.synchronize_credentials.return_value = True
        MockManager.return_value = mock_mgr

        args = argparse.Namespace(action="sync")
        execute(args)
        MockManager.assert_called_once()
        mock_mgr.synchronize_credentials.assert_called_once()
