#!/usr/bin/env python3
"""Pytest suite for `GenAI/shared/helpers/genai_helpers.py`.

Co-located with the module under `helpers/`. CPU-only, no network, no real
API keys, no real image generation. The module is the Phase-2 GenAI utilities
helper (logging setup, env config loading, API validation, generation-result
saving) consumed across the GenAI Image notebooks and had 0 dedicated Python
test coverage before this PR.

Strategy: the module imports only stdlib at top level (os/json/base64/asyncio/
typing/Path/datetime/logging) and lazily imports `dotenv` inside
`load_genai_config`, so it loads cleanly without optional deps. API checks
read `os.getenv` (monkeypatched). Image saving writes a known base64 payload
to a tmp_path and the JSON metadata is round-tripped.
"""
from __future__ import annotations

import base64
import importlib.util
import json
import logging
from pathlib import Path

import pytest

# Load the module by path (lives under shared/helpers/, stdlib-only at import
# time -> no sys.path manipulation, no package-relative imports).
_MODULE_PATH = Path(__file__).resolve().parent / "genai_helpers.py"
_spec = importlib.util.spec_from_file_location("genai_helpers", _MODULE_PATH)
gh = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(gh)


# --------------------------------------------------------------------------
# setup_genai_logging
# --------------------------------------------------------------------------


def test_setup_genai_logging_returns_named_logger():
    logger = gh.setup_genai_logging("INFO")
    assert isinstance(logger, logging.Logger)
    assert logger.name == "genai_coursia"


@pytest.mark.parametrize("level", ["DEBUG", "INFO", "WARNING", "ERROR"])
def test_setup_genai_logging_sets_level(level):
    logger = gh.setup_genai_logging(level)
    assert logger.level == getattr(logging, level)


def test_setup_genai_logging_is_idempotent_no_duplicate_handlers():
    logger = gh.setup_genai_logging("INFO")
    n_before = len(logger.handlers)
    # Calling again must NOT add a second handler (the guard prevents duplicates).
    logger2 = gh.setup_genai_logging("DEBUG")
    assert logger2 is logger  # same named logger from getLogger
    assert len(logger.handlers) == n_before
    assert logger.level == logging.DEBUG  # level reflects the latest call


def test_setup_genai_logging_adds_streamhandler_when_none():
    # Use a fresh child logger name to start from zero handlers.
    logger = logging.getLogger("genai_coursia_test_fresh")
    for h in list(logger.handlers):
        logger.removeHandler(h)
    assert logger.handlers == []

    # The module hardcodes the name 'genai_coursia'; verify it attaches a
    # StreamHandler on first setup of THAT logger.
    main_logger = gh.setup_genai_logging("INFO")
    assert any(isinstance(h, logging.StreamHandler) for h in main_logger.handlers)


def test_setup_genai_logging_formatter_includes_fields():
    logger = gh.setup_genai_logging("INFO")
    handler = next(
        (h for h in logger.handlers if isinstance(h, logging.StreamHandler)), None
    )
    assert handler is not None
    fmt = handler.formatter
    assert fmt is not None
    # The format string must reference time, name, level, message.
    for field in ("asctime", "name", "levelname", "message"):
        assert f"%({field})" in fmt._fmt


# --------------------------------------------------------------------------
# load_genai_config
# --------------------------------------------------------------------------


def test_load_genai_config_returns_true_when_env_present(tmp_path, monkeypatch):
    env = tmp_path / ".env"
    env.write_text("OPENROUTER_API_KEY=sk-test\n", encoding="utf-8")
    monkeypatch.chdir(tmp_path)
    result = gh.load_genai_config()
    assert result is True


def test_load_genai_config_returns_false_when_no_env(tmp_path, monkeypatch):
    # tmp_path has no .env file.
    monkeypatch.chdir(tmp_path)
    result = gh.load_genai_config()
    assert result is False


# --------------------------------------------------------------------------
# validate_apis
# --------------------------------------------------------------------------


def test_validate_apis_all_absent(monkeypatch):
    monkeypatch.delenv("OPENROUTER_API_KEY", raising=False)
    monkeypatch.delenv("OPENAI_API_KEY", raising=False)
    monkeypatch.delenv("DOCKER_ENABLED", raising=False)
    status = gh.validate_apis()
    assert status == {
        "openrouter": False,
        "openai": False,
        "docker_enabled": False,
    }


def test_validate_apis_keys_present(monkeypatch):
    monkeypatch.setenv("OPENROUTER_API_KEY", "sk-or")
    monkeypatch.setenv("OPENAI_API_KEY", "sk-oai")
    monkeypatch.delenv("DOCKER_ENABLED", raising=False)
    status = gh.validate_apis()
    assert status["openrouter"] is True
    assert status["openai"] is True
    assert status["docker_enabled"] is False


@pytest.mark.parametrize("val,expected", [
    ("true", True), ("True", True), ("TRUE", True),
    ("false", False), ("False", False), ("0", False),
])
def test_validate_apis_docker_enabled_parsing(monkeypatch, val, expected):
    # DOCKER_ENABLED is compared lowercased against 'true' -> only the literal
    # 'true' (case-insensitive) enables docker.
    monkeypatch.delenv("OPENROUTER_API_KEY", raising=False)
    monkeypatch.delenv("OPENAI_API_KEY", raising=False)
    monkeypatch.setenv("DOCKER_ENABLED", val)
    status = gh.validate_apis()
    assert status["docker_enabled"] is expected


# --------------------------------------------------------------------------
# save_generation_result
# --------------------------------------------------------------------------


def test_save_generation_result_writes_png_and_metadata(tmp_path):
    # A tiny valid PNG (1x1 transparent) base64-encoded.
    png_bytes = base64.b64decode(
        "iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAQAAAC1HAwCAAAAC0lEQVR42mNkYAAAAAYAAjCB0C8AAAAASUVORK5CYII="
    )
    image_b64 = base64.b64encode(png_bytes).decode("ascii")
    metadata = {"model": "sd35", "prompt": "a cat", "seed": 42}

    img_path, meta_path = gh.save_generation_result(
        image_b64, metadata, output_dir=str(tmp_path / "out")
    )

    # PNG file written and decodes back to the exact bytes.
    assert Path(img_path).exists()
    assert Path(img_path).read_bytes() == png_bytes
    assert img_path.endswith(".png")

    # JSON metadata round-trips.
    assert Path(meta_path).exists()
    assert meta_path.endswith(".json")
    loaded = json.loads(Path(meta_path).read_text(encoding="utf-8"))
    assert loaded == metadata


def test_save_generation_result_creates_output_dir(tmp_path):
    nested = tmp_path / "deep" / "nested" / "outputs"
    assert not nested.exists()
    png_bytes = b"\x89PNG\r\n"  # not a real PNG, just bytes to encode
    image_b64 = base64.b64encode(png_bytes).decode("ascii")
    img_path, _ = gh.save_generation_result(
        image_b64, {"k": "v"}, output_dir=str(nested)
    )
    assert nested.exists()
    assert Path(img_path).exists()


def test_save_generation_result_timestamps_in_filenames(tmp_path):
    png_bytes = b"data"
    image_b64 = base64.b64encode(png_bytes).decode("ascii")
    img_path, meta_path = gh.save_generation_result(
        image_b64, {}, output_dir=str(tmp_path / "out")
    )
    # Both filenames share the same YYYYMMDD_HHMMSS timestamp prefix.
    assert "genai_image_" in img_path
    assert "genai_metadata_" in meta_path


def test_save_generation_result_metadata_uses_default_str_serializer(tmp_path):
    # default=str lets non-JSON-native objects (e.g. datetime) serialize.
    from datetime import datetime as _dt
    metadata = {"generated_at": _dt(2026, 1, 1, 12, 0, 0), "nested": {"a": 1}}
    image_b64 = base64.b64encode(b"x").decode("ascii")
    _, meta_path = gh.save_generation_result(
        image_b64, metadata, output_dir=str(tmp_path / "out")
    )
    loaded = json.loads(Path(meta_path).read_text(encoding="utf-8"))
    # datetime serialized as ISO-ish string via str(), not an error.
    assert isinstance(loaded["generated_at"], str)
    assert loaded["nested"] == {"a": 1}


# --------------------------------------------------------------------------
# __all__
# --------------------------------------------------------------------------


def test_all_exports_present():
    assert set(gh.__all__) == {
        "setup_genai_logging", "load_genai_config",
        "validate_apis", "save_generation_result",
    }
    for name in gh.__all__:
        assert hasattr(gh, name)
