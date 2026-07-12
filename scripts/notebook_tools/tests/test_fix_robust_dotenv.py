"""Tests for fix_robust_dotenv.py — .env loading pattern detection."""

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent.parent))
from fix_robust_dotenv import has_env_loading, needs_fix


# --- has_env_loading ---


class TestHasEnvLoading:
    def test_load_dotenv(self):
        assert has_env_loading("from dotenv import load_dotenv") is True

    def test_dotenv_file_reference(self):
        assert has_env_loading("env_path = Path('.env')") is True

    def test_genai_root(self):
        assert has_env_loading("GENAI_ROOT = Path.cwd()") is True

    def test_no_keywords(self):
        assert has_env_loading("import pandas as pd") is False

    def test_empty_string(self):
        assert has_env_loading("") is False

    def test_case_sensitive_dotenv(self):
        """'.env' check is case-sensitive — '.ENV' does NOT match."""
        assert has_env_loading("path = '.ENV'") is False

    def test_partial_match(self):
        """'load_dotenv' as substring."""
        assert has_env_loading("# we use load_dotenv here") is True


# --- needs_fix ---


class TestNeedsFix:
    def test_old_pattern_needs_fix(self):
        source = "from dotenv import load_dotenv\nGENAI_ROOT = Path.cwd()"
        assert needs_fix(source) is True

    def test_robust_pattern_no_fix(self):
        source = (
            "from dotenv import load_dotenv\n"
            "env_loaded = False\n"
            "load_dotenv(env_path)\n"
        )
        assert needs_fix(source) is False

    def test_no_env_code_no_fix(self):
        assert needs_fix("import pandas as pd") is False

    def test_only_genai_root_needs_fix(self):
        source = "GENAI_ROOT = Path.cwd()"
        assert needs_fix(source) is True

    def test_empty_string(self):
        assert needs_fix("") is False

    def test_env_loaded_keyword_present(self):
        """env_loaded presence prevents fix."""
        source = "load_dotenv()\nenv_loaded = True"
        assert needs_fix(source) is False

    def test_dotenv_without_env_loaded(self):
        source = "load_dotenv('.env')"
        assert needs_fix(source) is True


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
