#!/usr/bin/env python3
"""Tests migrate_env_to_keyring — phase 4 de #17558."""
from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "secrets"))

from migrate_env_to_keyring import migrate  # noqa: E402


def test_dry_run_preserves_file(tmp_path):
    f = tmp_path / "test.env"
    f.write_text("OPENAI_API_KEY=sk-test\nCOMFYUI_PASSWORD=secret\nPORT=8080\n",
                 encoding="utf-8")
    result = migrate(f, apply=False)
    assert result["written"] is False
    assert result["shared_count"] == 1
    assert result["lines_kept"] == 2
    assert result["lines_removed"] == 1


def test_apply_removes_shared_keeps_instance(tmp_path):
    f = tmp_path / "test.env"
    f.write_text(
        "OPENAI_API_KEY=sk-test\n"
        "COMFYUI_PASSWORD=secret\n"
        "COMFYUI_USERNAME=admin\n"
        "PORT=8080\n"
        "HF_TOKEN=hf-test\n",
        encoding="utf-8")
    result = migrate(f, apply=True)
    assert result["written"] is True
    assert result["shared_count"] == 2
    content = f.read_text(encoding="utf-8")
    assert "OPENAI_API_KEY" not in content
    assert "HF_TOKEN" not in content
    assert "COMFYUI_PASSWORD=secret" in content
    assert "COMFYUI_USERNAME=admin" in content
    assert "PORT=8080" in content


def test_comments_and_blanks_preserved(tmp_path):
    f = tmp_path / "test.env"
    f.write_text("# config\n\nSECRET_KEY=x\nDEBUG=true\n", encoding="utf-8")
    result = migrate(f, apply=True)
    content = f.read_text(encoding="utf-8")
    assert "# config" in content
    assert "DEBUG=true" in content
    assert "SECRET_KEY" not in content


def test_no_shared_keys_noop(tmp_path):
    f = tmp_path / "test.env"
    f.write_text("COMFYUI_PASSWORD=x\nPORT=8080\n", encoding="utf-8")
    result = migrate(f, apply=True)
    assert result["shared_count"] == 0
    assert result["lines_removed"] == 0


def test_idempotent(tmp_path):
    f = tmp_path / "test.env"
    f.write_text("OPENAI_API_KEY=sk\nCOMFYUI_PASSWORD=x\n", encoding="utf-8")
    migrate(f, apply=True)
    result2 = migrate(f, apply=True)
    assert result2["shared_count"] == 0
    assert result2["lines_removed"] == 0
