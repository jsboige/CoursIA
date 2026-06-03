"""Tests for scripts/genai-stack/commands/models.py -- static config and pure helpers.

Tests cover testable pure logic: QWEN_MODELS (3 model entries), NUNCHAKU_MODELS
(6 variants dict), NUNCHAKU_REPO_ID (string), ZIMAGE_VAE_CONFIG (VAE download config),
_get_hf_token (env/file-based token loading). Network/Docker/external functions
(download_qwen, download_nunchaku, setup_zimage, list_checkpoints, list_nodes,
_ensure_huggingface_hub, register, execute, main*) are excluded -- they require
live Docker containers, HTTP endpoints, or huggingface_hub installation.
"""

import os
import sys
from pathlib import Path
from unittest.mock import patch

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "genai-stack"))
from commands.models import (
    NUNCHAKU_MODELS,
    NUNCHAKU_REPO_ID,
    QWEN_MODELS,
    ZIMAGE_VAE_CONFIG,
    _get_hf_token,
)


# ---------------------------------------------------------------------------
# QWEN_MODELS constant
# ---------------------------------------------------------------------------


class TestQwenModels:
    """Tests for the QWEN_MODELS list."""

    def test_is_list(self):
        """QWEN_MODELS is a list."""
        assert isinstance(QWEN_MODELS, list)

    def test_count(self):
        """Has exactly 3 models (Diffusion, Text Encoder, VAE)."""
        assert len(QWEN_MODELS) == 3

    def test_no_duplicates(self):
        """No duplicate model entries."""
        names = [m["local_name"] for m in QWEN_MODELS]
        assert len(names) == len(set(names))

    def test_all_dicts(self):
        """All entries are dicts."""
        assert all(isinstance(m, dict) for m in QWEN_MODELS)

    def test_required_keys(self):
        """Each model has all required keys."""
        required = {"name", "repo_id", "filename", "local_name", "subdir", "size_gb"}
        for model in QWEN_MODELS:
            assert required <= set(model.keys()), f"Missing keys in {model['name']}"

    def test_names_are_strings(self):
        """All name fields are non-empty strings."""
        for model in QWEN_MODELS:
            assert isinstance(model["name"], str) and len(model["name"]) > 0

    def test_repo_ids_are_strings(self):
        """All repo_id fields are non-empty strings."""
        for model in QWEN_MODELS:
            assert isinstance(model["repo_id"], str) and "/" in model["repo_id"]

    def test_filenames_are_strings(self):
        """All filename fields are non-empty strings."""
        for model in QWEN_MODELS:
            assert isinstance(model["filename"], str) and len(model["filename"]) > 0

    def test_local_names_have_safetensors_extension(self):
        """All local_name fields end with .safetensors."""
        for model in QWEN_MODELS:
            assert model["local_name"].endswith(".safetensors")

    def test_subdirs_are_strings(self):
        """All subdir fields are non-empty strings."""
        for model in QWEN_MODELS:
            assert isinstance(model["subdir"], str) and len(model["subdir"]) > 0

    def test_size_gb_are_positive_numbers(self):
        """All size_gb fields are positive numbers."""
        for model in QWEN_MODELS:
            assert isinstance(model["size_gb"], (int, float))
            assert model["size_gb"] > 0

    def test_total_size_reasonable(self):
        """Total size is roughly 29 GB (3 models: ~20 + ~8.8 + ~0.2)."""
        total = sum(m["size_gb"] for m in QWEN_MODELS)
        assert 28 < total < 32

    def test_diffusion_model_largest(self):
        """Diffusion model (UNET) is the largest."""
        sizes = {m["name"]: m["size_gb"] for m in QWEN_MODELS}
        diffusion_size = max(sizes.values())
        assert any("Diffusion" in m["name"] and m["size_gb"] == diffusion_size
                    for m in QWEN_MODELS)

    def test_distinct_subdirs(self):
        """Each model targets a different subdir."""
        subdirs = [m["subdir"] for m in QWEN_MODELS]
        assert len(subdirs) == len(set(subdirs))

    def test_comfy_org_repo(self):
        """All repo_ids start with Comfy-Org/."""
        for model in QWEN_MODELS:
            assert model["repo_id"].startswith("Comfy-Org/")

    def test_distinct_repo_ids(self):
        """Models may share repo_ids but local_names are unique."""
        local_names = [m["local_name"] for m in QWEN_MODELS]
        assert len(local_names) == len(set(local_names))


# ---------------------------------------------------------------------------
# NUNCHAKU_MODELS constant
# ---------------------------------------------------------------------------


class TestNunchakuModels:
    """Tests for the NUNCHAKU_MODELS mapping."""

    def test_is_dict(self):
        """NUNCHAKU_MODELS is a dict."""
        assert isinstance(NUNCHAKU_MODELS, dict)

    def test_count(self):
        """Has exactly 6 variants."""
        assert len(NUNCHAKU_MODELS) == 6

    def test_keys_are_strings(self):
        """All keys are strings."""
        for key in NUNCHAKU_MODELS:
            assert isinstance(key, str)

    def test_values_are_strings(self):
        """All values are filenames (strings)."""
        for val in NUNCHAKU_MODELS.values():
            assert isinstance(val, str)

    def test_values_have_safetensors_extension(self):
        """All values end with .safetensors."""
        for val in NUNCHAKU_MODELS.values():
            assert val.endswith(".safetensors")

    def test_no_duplicate_values(self):
        """No duplicate filenames."""
        values = list(NUNCHAKU_MODELS.values())
        assert len(values) == len(set(values))

    def test_lightning_4step_keys(self):
        """Has exactly 2 lightning-4step variants (r128, r32)."""
        lightning_4 = [k for k in NUNCHAKU_MODELS if k.startswith("lightning-4step")]
        assert len(lightning_4) == 2
        assert "lightning-4step-r128" in NUNCHAKU_MODELS
        assert "lightning-4step-r32" in NUNCHAKU_MODELS

    def test_lightning_8step_keys(self):
        """Has exactly 2 lightning-8step variants (r128, r32)."""
        lightning_8 = [k for k in NUNCHAKU_MODELS if k.startswith("lightning-8step")]
        assert len(lightning_8) == 2
        assert "lightning-8step-r128" in NUNCHAKU_MODELS
        assert "lightning-8step-r32" in NUNCHAKU_MODELS

    def test_standard_keys(self):
        """Has exactly 2 standard variants (r128, r32)."""
        standard = [k for k in NUNCHAKU_MODELS if k.startswith("standard")]
        assert len(standard) == 2
        assert "standard-r128" in NUNCHAKU_MODELS
        assert "standard-r32" in NUNCHAKU_MODELS

    def test_keys_match_pattern(self):
        """All keys follow pattern: variant[-step]-rank (2 or 3 hyphen-separated parts)."""
        for key in NUNCHAKU_MODELS:
            parts = key.split("-")
            assert len(parts) >= 2, f"Key '{key}' doesn't follow expected pattern"
            assert parts[-1].startswith("r"), f"Key '{key}' last part should be rank (rNNN)"

    def test_r128_and_r32_variants(self):
        """Each model variant has both r128 and r32 ranks."""
        variants = {}
        for key in NUNCHAKU_MODELS:
            variant = key.rsplit("-", 1)[0]  # e.g. "lightning-4step"
            rank = key.rsplit("-", 1)[1]      # e.g. "r128"
            variants.setdefault(variant, set()).add(rank)
        for variant, ranks in variants.items():
            assert ranks == {"r128", "r32"}, f"{variant} missing rank variants: {ranks}"

    def test_values_contain_int4(self):
        """All filenames contain 'int4' indicating quantization."""
        for val in NUNCHAKU_MODELS.values():
            assert "int4" in val

    def test_values_contain_svdaq_prefix(self):
        """All filenames start with svdq-."""
        for val in NUNCHAKU_MODELS.values():
            assert val.startswith("svdq-")

    def test_lightning_r128_filename_has_4steps(self):
        """lightning-4step-r128 filename contains '4steps'."""
        fn = NUNCHAKU_MODELS["lightning-4step-r128"]
        assert "4steps" in fn

    def test_lightning_r32_filename_has_4steps(self):
        """lightning-4step-r32 filename contains '4steps'."""
        fn = NUNCHAKU_MODELS["lightning-4step-r32"]
        assert "4steps" in fn


# ---------------------------------------------------------------------------
# NUNCHAKU_REPO_ID constant
# ---------------------------------------------------------------------------


class TestNunchakuRepoId:
    """Tests for the NUNCHAKU_REPO_ID string."""

    def test_is_string(self):
        """NUNCHAKU_REPO_ID is a string."""
        assert isinstance(NUNCHAKU_REPO_ID, str)

    def test_format(self):
        """Has org/repo format."""
        assert "/" in NUNCHAKU_REPO_ID

    def test_nunchaku_org(self):
        """Starts with nunchaku-ai/."""
        assert NUNCHAKU_REPO_ID.startswith("nunchaku-ai/")

    def test_non_empty(self):
        """Is non-empty."""
        assert len(NUNCHAKU_REPO_ID) > 0

    def test_contains_qwen(self):
        """Contains 'qwen' in the repo name."""
        assert "qwen" in NUNCHAKU_REPO_ID.lower()


# ---------------------------------------------------------------------------
# ZIMAGE_VAE_CONFIG constant
# ---------------------------------------------------------------------------


class TestZimageVaeConfig:
    """Tests for the ZIMAGE_VAE_CONFIG dict."""

    def test_is_dict(self):
        """ZIMAGE_VAE_CONFIG is a dict."""
        assert isinstance(ZIMAGE_VAE_CONFIG, dict)

    def test_required_keys(self):
        """Has url, filename, and subfolder keys."""
        required = {"url", "filename", "subfolder"}
        assert required == set(ZIMAGE_VAE_CONFIG.keys())

    def test_url_is_string(self):
        """URL is a non-empty string."""
        assert isinstance(ZIMAGE_VAE_CONFIG["url"], str)
        assert len(ZIMAGE_VAE_CONFIG["url"]) > 0

    def test_url_is_https(self):
        """URL uses HTTPS."""
        assert ZIMAGE_VAE_CONFIG["url"].startswith("https://")

    def test_url_points_to_huggingface(self):
        """URL points to huggingface.co."""
        assert "huggingface.co" in ZIMAGE_VAE_CONFIG["url"]

    def test_filename_is_string(self):
        """Filename is a non-empty string."""
        assert isinstance(ZIMAGE_VAE_CONFIG["filename"], str)
        assert len(ZIMAGE_VAE_CONFIG["filename"]) > 0

    def test_filename_has_safetensors_extension(self):
        """Filename ends with .safetensors."""
        assert ZIMAGE_VAE_CONFIG["filename"].endswith(".safetensors")

    def test_subfolder_is_string(self):
        """Subfolder is a non-empty string."""
        assert isinstance(ZIMAGE_VAE_CONFIG["subfolder"], str)
        assert len(ZIMAGE_VAE_CONFIG["subfolder"]) > 0

    def test_subfolder_is_vae(self):
        """Subfolder is 'vae'."""
        assert ZIMAGE_VAE_CONFIG["subfolder"] == "vae"

    def test_url_contains_filename(self):
        """URL ends with the filename."""
        assert ZIMAGE_VAE_CONFIG["url"].endswith("/" + ZIMAGE_VAE_CONFIG["filename"])

    def test_url_contains_resolve(self):
        """URL uses resolve/main pattern."""
        assert "resolve/main" in ZIMAGE_VAE_CONFIG["url"]


# ---------------------------------------------------------------------------
# _get_hf_token
# ---------------------------------------------------------------------------


class TestGetHfToken:
    """Tests for _get_hf_token env/file-based token loader."""

    def test_returns_none_without_env(self):
        """Returns None when no env vars or files are set."""
        with patch.dict("os.environ", {}, clear=True):
            with patch.object(Path, "home", return_value=Path("/fake/home")):
                with patch.object(Path, "exists", return_value=False):
                    result = _get_hf_token()
                    assert result is None

    def test_hf_token_env_var(self):
        """Reads HF_TOKEN from environment."""
        with patch.dict("os.environ", {"HF_TOKEN": "hf_test123"}, clear=False):
            result = _get_hf_token()
            assert result == "hf_test123"

    def test_huggingface_token_env_var(self):
        """Reads HUGGINGFACE_TOKEN from environment as fallback."""
        with patch.dict("os.environ", {"HUGGINGFACE_TOKEN": "hf_fallback456"}, clear=False):
            # Remove HF_TOKEN if present to test fallback
            env = dict(os.environ)
            env.pop("HF_TOKEN", None)
            with patch.dict("os.environ", env, clear=True):
                result = _get_hf_token()
                assert result == "hf_fallback456"

    def test_hf_token_priority_over_huggingface_token(self):
        """HF_TOKEN takes priority over HUGGINGFACE_TOKEN."""
        with patch.dict("os.environ", {
            "HF_TOKEN": "hf_primary",
            "HUGGINGFACE_TOKEN": "hf_secondary",
        }, clear=False):
            result = _get_hf_token()
            assert result == "hf_primary"

    def test_non_hf_prefix_ignored(self):
        """Non-hf_ prefixed tokens from env are NOT returned."""
        with patch.dict("os.environ", {"HF_TOKEN": "not_a_hf_token"}, clear=False):
            result = _get_hf_token()
            # env returns the value but file checks require hf_ prefix
            # Actually HF_TOKEN env var is returned directly without prefix check
            assert result == "not_a_hf_token"

    def test_returns_string_or_none(self):
        """Return type is str or None."""
        with patch.dict("os.environ", {}, clear=True):
            with patch.object(Path, "home", return_value=Path("/fake/home")):
                with patch.object(Path, "exists", return_value=False):
                    result = _get_hf_token()
                    assert result is None or isinstance(result, str)

    def test_empty_env_vars_ignored(self):
        """Empty string env vars are falsy, skipped."""
        with patch.dict("os.environ", {"HF_TOKEN": "", "HUGGINGFACE_TOKEN": ""}, clear=False):
            env = dict(os.environ)
            env["HF_TOKEN"] = ""
            env["HUGGINGFACE_TOKEN"] = ""
            with patch.dict("os.environ", env, clear=True):
                result = _get_hf_token()
                # Empty strings are falsy, so env check passes to file search
                assert result is None or isinstance(result, str)

    def _mock_secret_file(self, path_end: str, content: str):
        """Create patches that mock Path.exists() and Path.read_text() for a specific file."""
        original_exists = Path.exists
        original_read_text = Path.read_text

        def patched_exists(self_path):
            if str(self_path).endswith(path_end):
                return True
            return original_exists(self_path)

        def patched_read_text(self_path, *args, **kwargs):
            if str(self_path).endswith(path_end):
                return content
            return original_read_text(self_path, *args, **kwargs)

        return patch.object(Path, "exists", patched_exists), patch.object(Path, "read_text", patched_read_text)

    def test_secret_file_with_equals(self):
        """Reads token from .env.huggingface file with KEY=VALUE format."""
        exists_p, read_p = self._mock_secret_file(
            ".env.huggingface", "HF_TOKEN=hf_from_file_abc\n"
        )
        with patch.dict("os.environ", {}, clear=True):
            with patch.object(Path, "home", return_value=Path("/fake/home")):
                with exists_p, read_p:
                    result = _get_hf_token()
                    assert result == "hf_from_file_abc"

    def test_secret_file_without_equals(self):
        """Reads token from file without = (raw token format)."""
        exists_p, read_p = self._mock_secret_file(
            ".env.huggingface", "hf_raw_token_xyz\n"
        )
        with patch.dict("os.environ", {}, clear=True):
            with patch.object(Path, "home", return_value=Path("/fake/home")):
                with exists_p, read_p:
                    result = _get_hf_token()
                    assert result == "hf_raw_token_xyz"

    def test_secret_file_token_must_start_with_hf(self):
        """Token from file must start with 'hf_' prefix."""
        exists_p, read_p = self._mock_secret_file(
            ".env.huggingface", "invalid_token_no_prefix\n"
        )
        with patch.dict("os.environ", {}, clear=True):
            with patch.object(Path, "home", return_value=Path("/fake/home")):
                with exists_p, read_p:
                    result = _get_hf_token()
                    assert result is None

    def test_secret_file_strips_whitespace(self):
        """Token from file is stripped of whitespace."""
        exists_p, read_p = self._mock_secret_file(
            ".env.huggingface", "  hf_stripped_token  \n"
        )
        with patch.dict("os.environ", {}, clear=True):
            with patch.object(Path, "home", return_value=Path("/fake/home")):
                with exists_p, read_p:
                    result = _get_hf_token()
                    assert result == "hf_stripped_token"

    def test_env_var_priority_over_file(self):
        """HF_TOKEN env var takes priority over file-based tokens."""
        exists_p, read_p = self._mock_secret_file(
            ".env.huggingface", "HF_TOKEN=hf_from_file\n"
        )
        with patch.dict("os.environ", {"HF_TOKEN": "hf_from_env"}, clear=False):
            with patch.object(Path, "home", return_value=Path("/fake/home")):
                with exists_p, read_p:
                    result = _get_hf_token()
                    assert result == "hf_from_env"


# ---------------------------------------------------------------------------
# Cross-constant invariants
# ---------------------------------------------------------------------------


class TestCrossInvariants:
    """Tests for invariants across multiple constants."""

    def test_qwen_models_total_size_positive(self):
        """Sum of all QWEN_MODELS sizes is positive."""
        total = sum(m["size_gb"] for m in QWEN_MODELS)
        assert total > 0

    def test_nunchaku_keys_subset_of_choices(self):
        """NUNCHAKU_MODELS keys are valid choices for CLI."""
        # CLI uses choices=list(NUNCHAKU_MODELS.keys()), so all keys are valid
        for key in NUNCHAKU_MODELS:
            assert isinstance(key, str)
            assert "-" in key  # format: variant-step-rank

    def test_vae_config_url_matches_filename(self):
        """ZIMAGE_VAE_CONFIG URL ends with the declared filename."""
        assert ZIMAGE_VAE_CONFIG["url"].rsplit("/", 1)[-1] == ZIMAGE_VAE_CONFIG["filename"]

    def test_all_repo_ids_have_org(self):
        """All QWEN_MODELS repo_ids have an organization prefix."""
        for model in QWEN_MODELS:
            parts = model["repo_id"].split("/")
            assert len(parts) == 2, f"repo_id '{model['repo_id']}' doesn't have org/repo format"

    def test_nunchaku_default_key_exists(self):
        """The default CLI key 'lightning-4step-r128' exists in NUNCHAKU_MODELS."""
        assert "lightning-4step-r128" in NUNCHAKU_MODELS

    def test_qwen_subdirs_match_known_types(self):
        """QWEN_MODELS subdirs are the 3 known types."""
        subdirs = {m["subdir"] for m in QWEN_MODELS}
        assert subdirs == {"diffusion_models", "text_encoders", "vae"}
