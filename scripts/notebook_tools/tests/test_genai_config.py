"""Tests for scripts/genai-stack/config.py — GenAI stack configuration.

Tests cover: load_env (file parsing), constant structural integrity
(unique ports, required keys, cross-reference consistency between
SERVICES, NOTEBOOK_SERVICE_MAP, GPU_PROFILES, GROUP_GPU_PROFILE,
NOTEBOOK_SERIES, EXECUTION_BATCHES, MODEL_CONFIGS).
"""

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent.parent / "genai-stack"))
from config import (
    ENV_FILE,
    EXECUTION_BATCHES,
    GPU_PROFILES,
    GROUP_GPU_PROFILE,
    MODEL_CONFIGS,
    NOTEBOOK_SEARCH_DIRS,
    NOTEBOOK_SERIES,
    NOTEBOOK_SERVICE_MAP,
    SERVICES,
    SERVICES_DIR,
    load_env,
)


# ---------------------------------------------------------------------------
# load_env
# ---------------------------------------------------------------------------


class TestLoadEnv:
    """Tests for .env file parsing."""

    def test_reads_key_value_pairs(self, tmp_path):
        """Standard KEY=VALUE lines parsed correctly."""
        env_file = tmp_path / ".env"
        env_file.write_text("API_KEY=sk-123\nHOST=localhost\n", encoding="utf-8")
        # Monkeypatch ENV_FILE for this test
        import config as cfg

        orig = cfg.ENV_FILE
        cfg.ENV_FILE = env_file
        try:
            result = load_env()
        finally:
            cfg.ENV_FILE = orig
        assert result == {"API_KEY": "sk-123", "HOST": "localhost"}

    def test_strips_quotes(self, tmp_path):
        """Single and double quotes are stripped from values."""
        env_file = tmp_path / ".env"
        env_file.write_text('KEY1="value1"\nKEY2=\'value2\'\n', encoding="utf-8")
        import config as cfg

        orig = cfg.ENV_FILE
        cfg.ENV_FILE = env_file
        try:
            result = load_env()
        finally:
            cfg.ENV_FILE = orig
        assert result["KEY1"] == "value1"
        assert result["KEY2"] == "value2"

    def test_skips_comments(self, tmp_path):
        """Lines starting with # are ignored."""
        env_file = tmp_path / ".env"
        env_file.write_text("# comment\nKEY=val\n", encoding="utf-8")
        import config as cfg

        orig = cfg.ENV_FILE
        cfg.ENV_FILE = env_file
        try:
            result = load_env()
        finally:
            cfg.ENV_FILE = orig
        assert result == {"KEY": "val"}

    def test_skips_empty_lines(self, tmp_path):
        """Empty and whitespace-only lines are ignored."""
        env_file = tmp_path / ".env"
        env_file.write_text("\nKEY=val\n   \n", encoding="utf-8")
        import config as cfg

        orig = cfg.ENV_FILE
        cfg.ENV_FILE = env_file
        try:
            result = load_env()
        finally:
            cfg.ENV_FILE = orig
        assert result == {"KEY": "val"}

    def test_skips_no_equals(self, tmp_path):
        """Lines without = are ignored."""
        env_file = tmp_path / ".env"
        env_file.write_text("NOEQUALS\nKEY=val\n", encoding="utf-8")
        import config as cfg

        orig = cfg.ENV_FILE
        cfg.ENV_FILE = env_file
        try:
            result = load_env()
        finally:
            cfg.ENV_FILE = orig
        assert result == {"KEY": "val"}

    def test_value_with_equals_sign(self, tmp_path):
        """Value containing = is preserved (split on first = only)."""
        env_file = tmp_path / ".env"
        env_file.write_text("URL=https://a=b\n", encoding="utf-8")
        import config as cfg

        orig = cfg.ENV_FILE
        cfg.ENV_FILE = env_file
        try:
            result = load_env()
        finally:
            cfg.ENV_FILE = orig
        assert result["URL"] == "https://a=b"

    def test_empty_file(self, tmp_path):
        """Empty .env file returns empty dict."""
        env_file = tmp_path / ".env"
        env_file.write_text("", encoding="utf-8")
        import config as cfg

        orig = cfg.ENV_FILE
        cfg.ENV_FILE = env_file
        try:
            result = load_env()
        finally:
            cfg.ENV_FILE = orig
        assert result == {}

    def test_missing_file(self, tmp_path):
        """Non-existent .env returns empty dict."""
        import config as cfg

        orig = cfg.ENV_FILE
        cfg.ENV_FILE = tmp_path / "nonexistent.env"
        try:
            result = load_env()
        finally:
            cfg.ENV_FILE = orig
        assert result == {}

    def test_strips_whitespace_around_key_value(self, tmp_path):
        """Whitespace around keys and values is stripped."""
        env_file = tmp_path / ".env"
        env_file.write_text("  KEY  =  value  \n", encoding="utf-8")
        import config as cfg

        orig = cfg.ENV_FILE
        cfg.ENV_FILE = env_file
        try:
            result = load_env()
        finally:
            cfg.ENV_FILE = orig
        assert result == {"KEY": "value"}


# ---------------------------------------------------------------------------
# SERVICES structural integrity
# ---------------------------------------------------------------------------


class TestServices:
    """Tests for SERVICES constant structural integrity."""

    def test_all_services_have_required_keys(self):
        """Each service has compose_dir, container_name, port, health_endpoint."""
        required = {"compose_dir", "container_name", "port", "health_endpoint"}
        for name, svc in SERVICES.items():
            missing = required - set(svc.keys())
            assert not missing, f"Service {name} missing keys: {missing}"

    def test_ports_are_unique(self):
        """No two services share the same port."""
        ports = {}
        for name, svc in SERVICES.items():
            port = svc["port"]
            if port in ports:
                assert False, f"Duplicate port {port}: {ports[port]} and {name}"
            ports[port] = name

    def test_container_names_are_unique(self):
        """No two services share the same container_name."""
        names = {}
        for name, svc in SERVICES.items():
            cn = svc["container_name"]
            if cn in names:
                assert False, f"Duplicate container_name {cn}: {names[cn]} and {name}"
            names[cn] = name

    def test_ports_are_positive_integers(self):
        """All ports are positive integers."""
        for name, svc in SERVICES.items():
            port = svc["port"]
            assert isinstance(port, int) and port > 0, f"Service {name}: invalid port {port}"

    def test_compose_dirs_are_paths(self):
        """All compose_dir values are Path objects."""
        for name, svc in SERVICES.items():
            assert isinstance(svc["compose_dir"], Path), f"Service {name}: compose_dir not Path"

    def test_auth_type_values(self):
        """auth_type is None, 'bearer', or 'basic'."""
        valid = {None, "bearer", "basic"}
        for name, svc in SERVICES.items():
            auth = svc.get("auth_type")
            assert auth in valid, f"Service {name}: invalid auth_type {auth!r}"

    def test_gpu_id_is_int(self):
        """All services with gpu_id have integer values."""
        for name, svc in SERVICES.items():
            assert isinstance(svc.get("gpu_id"), int), f"Service {name}: gpu_id not int"

    def test_remote_url_starts_with_https(self):
        """All services have remote_url starting with https://."""
        for name, svc in SERVICES.items():
            url = svc.get("remote_url", "")
            assert url.startswith("https://"), f"Service {name}: remote_url {url!r}"

    def test_services_count(self):
        """Expected 10 services."""
        assert len(SERVICES) == 10

    def test_known_services_exist(self):
        """Core services are present."""
        for svc_name in ["comfyui-qwen", "forge-turbo", "vllm-zimage", "comfyui-video"]:
            assert svc_name in SERVICES, f"Missing service: {svc_name}"


# ---------------------------------------------------------------------------
# NOTEBOOK_SERVICE_MAP integrity
# ---------------------------------------------------------------------------


class TestNotebookServiceMap:
    """Tests for NOTEBOOK_SERVICE_MAP structural integrity."""

    def test_all_groups_are_lists(self):
        """Each group maps to a list of notebook filenames."""
        for group, notebooks in NOTEBOOK_SERVICE_MAP.items():
            assert isinstance(notebooks, list), f"Group {group}: not a list"

    def test_notebooks_end_with_ipynb(self):
        """All notebook filenames end with .ipynb."""
        for group, notebooks in NOTEBOOK_SERVICE_MAP.items():
            for nb in notebooks:
                assert nb.endswith(".ipynb"), f"Group {group}: {nb} doesn't end with .ipynb"

    def test_unique_notebook_filenames(self):
        """All notebook filenames across groups are unique."""
        all_nbs = []
        for notebooks in NOTEBOOK_SERVICE_MAP.values():
            all_nbs.extend(notebooks)
        assert len(all_nbs) == len(set(all_nbs)), "Duplicate notebook filenames found"

    def test_groups_are_non_empty(self):
        """Each group has at least one notebook."""
        for group, notebooks in NOTEBOOK_SERVICE_MAP.items():
            assert len(notebooks) > 0, f"Group {group} is empty"

    def test_group_names_are_strings(self):
        """All group names are non-empty strings."""
        for group in NOTEBOOK_SERVICE_MAP:
            assert isinstance(group, str) and group, f"Invalid group name: {group!r}"


# ---------------------------------------------------------------------------
# NOTEBOOK_SERIES cross-reference
# ---------------------------------------------------------------------------


class TestNotebookSeries:
    """Tests for NOTEBOOK_SERIES cross-reference with NOTEBOOK_SERVICE_MAP."""

    def test_series_groups_exist_in_service_map(self):
        """Every group in NOTEBOOK_SERIES exists in NOTEBOOK_SERVICE_MAP."""
        for series, groups in NOTEBOOK_SERIES.items():
            for group in groups:
                assert group in NOTEBOOK_SERVICE_MAP, (
                    f"Series {series}: group {group} not in NOTEBOOK_SERVICE_MAP"
                )

    def test_all_service_map_groups_covered(self):
        """Every group in NOTEBOOK_SERVICE_MAP appears in some NOTEBOOK_SERIES."""
        all_series_groups = set()
        for groups in NOTEBOOK_SERIES.values():
            all_series_groups.update(groups)
        for group in NOTEBOOK_SERVICE_MAP:
            assert group in all_series_groups, (
                f"Group {group} not covered by any NOTEBOOK_SERIES"
            )

    def test_series_count(self):
        """Expected 3 series: image, audio, video."""
        assert set(NOTEBOOK_SERIES.keys()) == {"image", "audio", "video"}

    def test_series_groups_are_unique(self):
        """No group appears in multiple series."""
        all_groups = []
        for groups in NOTEBOOK_SERIES.values():
            all_groups.extend(groups)
        assert len(all_groups) == len(set(all_groups)), "Group in multiple series"


# ---------------------------------------------------------------------------
# GPU_PROFILES integrity
# ---------------------------------------------------------------------------


class TestGpuProfiles:
    """Tests for GPU_PROFILES structural integrity."""

    def test_all_profiles_have_required_keys(self):
        """Each profile has description, services_up, services_down."""
        required = {"description", "services_up", "services_down"}
        for name, profile in GPU_PROFILES.items():
            missing = required - set(profile.keys())
            assert not missing, f"Profile {name} missing keys: {missing}"

    def test_services_up_are_lists(self):
        """services_up is a list."""
        for name, profile in GPU_PROFILES.items():
            assert isinstance(profile["services_up"], list), f"Profile {name}: services_up not list"

    def test_services_down_are_lists(self):
        """services_down is a list."""
        for name, profile in GPU_PROFILES.items():
            assert isinstance(profile["services_down"], list), f"Profile {name}: services_down not list"

    def test_services_up_exist_in_services(self):
        """All services_up names exist in SERVICES."""
        for name, profile in GPU_PROFILES.items():
            for svc in profile["services_up"]:
                assert svc in SERVICES, f"Profile {name}: services_up {svc!r} not in SERVICES"

    def test_services_down_exist_in_services(self):
        """All services_down names exist in SERVICES."""
        for name, profile in GPU_PROFILES.items():
            for svc in profile["services_down"]:
                assert svc in SERVICES, f"Profile {name}: services_down {svc!r} not in SERVICES"

    def test_profiles_count(self):
        """Expected GPU profiles."""
        assert len(GPU_PROFILES) >= 8  # 8 profiles at minimum

    def test_descriptions_are_strings(self):
        """All profile descriptions are non-empty strings."""
        for name, profile in GPU_PROFILES.items():
            desc = profile.get("description", "")
            assert isinstance(desc, str) and desc, f"Profile {name}: bad description"


# ---------------------------------------------------------------------------
# GROUP_GPU_PROFILE cross-reference
# ---------------------------------------------------------------------------


class TestGroupGpuProfile:
    """Tests for GROUP_GPU_PROFILE cross-reference integrity."""

    def test_all_groups_in_service_map(self):
        """Every group in GROUP_GPU_PROFILE exists in NOTEBOOK_SERVICE_MAP."""
        for group in GROUP_GPU_PROFILE:
            assert group in NOTEBOOK_SERVICE_MAP, (
                f"GROUP_GPU_PROFILE group {group!r} not in NOTEBOOK_SERVICE_MAP"
            )

    def test_all_service_map_groups_have_profile(self):
        """Every group in NOTEBOOK_SERVICE_MAP has a GPU profile."""
        for group in NOTEBOOK_SERVICE_MAP:
            assert group in GROUP_GPU_PROFILE, (
                f"NOTEBOOK_SERVICE_MAP group {group!r} missing from GROUP_GPU_PROFILE"
            )

    def test_all_profiles_exist_in_gpu_profiles(self):
        """Every profile reference in GROUP_GPU_PROFILE exists in GPU_PROFILES."""
        for group, profile_name in GROUP_GPU_PROFILE.items():
            assert profile_name in GPU_PROFILES, (
                f"Group {group}: profile {profile_name!r} not in GPU_PROFILES"
            )


# ---------------------------------------------------------------------------
# EXECUTION_BATCHES integrity
# ---------------------------------------------------------------------------


class TestExecutionBatches:
    """Tests for EXECUTION_BATCHES structural integrity."""

    def test_all_batches_have_required_keys(self):
        """Each batch has name, profile, groups."""
        required = {"name", "profile", "groups"}
        for batch_id, batch in EXECUTION_BATCHES.items():
            missing = required - set(batch.keys())
            assert not missing, f"Batch {batch_id} missing keys: {missing}"

    def test_batch_profiles_exist(self):
        """Each batch's profile exists in GPU_PROFILES."""
        for batch_id, batch in EXECUTION_BATCHES.items():
            assert batch["profile"] in GPU_PROFILES, (
                f"Batch {batch_id}: profile {batch['profile']!r} not in GPU_PROFILES"
            )

    def test_batch_groups_exist_in_service_map(self):
        """Each batch's groups exist in NOTEBOOK_SERVICE_MAP."""
        for batch_id, batch in EXECUTION_BATCHES.items():
            for group in batch["groups"]:
                assert group in NOTEBOOK_SERVICE_MAP, (
                    f"Batch {batch_id}: group {group!r} not in NOTEBOOK_SERVICE_MAP"
                )

    def test_batch_ids_are_sequential(self):
        """Batch IDs are sequential starting from 1."""
        ids = sorted(EXECUTION_BATCHES.keys())
        assert ids == list(range(1, len(ids) + 1))

    def test_batch_groups_are_lists(self):
        """Each batch groups field is a list."""
        for batch_id, batch in EXECUTION_BATCHES.items():
            assert isinstance(batch["groups"], list), f"Batch {batch_id}: groups not list"

    def test_batch_names_are_strings(self):
        """Each batch name is a non-empty string."""
        for batch_id, batch in EXECUTION_BATCHES.items():
            assert isinstance(batch["name"], str) and batch["name"], (
                f"Batch {batch_id}: bad name"
            )

    def test_batches_count(self):
        """Expected 8 execution batches."""
        assert len(EXECUTION_BATCHES) == 8


# ---------------------------------------------------------------------------
# MODEL_CONFIGS integrity
# ---------------------------------------------------------------------------


class TestModelConfigs:
    """Tests for MODEL_CONFIGS structural integrity."""

    def test_all_configs_have_vram(self):
        """Each model config specifies vram_required_mb."""
        for name, cfg in MODEL_CONFIGS.items():
            assert "vram_required_mb" in cfg, f"Model {name} missing vram_required_mb"

    def test_vram_values_are_positive(self):
        """vram_required_mb values are positive integers."""
        for name, cfg in MODEL_CONFIGS.items():
            vram = cfg["vram_required_mb"]
            assert isinstance(vram, int) and vram > 0, (
                f"Model {name}: invalid vram_required_mb {vram}"
            )

    def test_known_models_exist(self):
        """Core model configs are present."""
        for model_name in ["nunchaku", "qwen", "qwen_fp8", "zimage"]:
            assert model_name in MODEL_CONFIGS, f"Missing model config: {model_name}"

    def test_configs_count(self):
        """Expected 4 model configs."""
        assert len(MODEL_CONFIGS) == 4


# ---------------------------------------------------------------------------
# NOTEBOOK_SEARCH_DIRS integrity
# ---------------------------------------------------------------------------


class TestNotebookSearchDirs:
    """Tests for NOTEBOOK_SEARCH_DIRS structural integrity."""

    def test_series_match_notebook_series(self):
        """Keys match NOTEBOOK_SERIES keys."""
        assert set(NOTEBOOK_SEARCH_DIRS.keys()) == set(NOTEBOOK_SERIES.keys())

    def test_dirs_are_paths(self):
        """All values are Path objects."""
        for series, dir_path in NOTEBOOK_SEARCH_DIRS.items():
            assert isinstance(dir_path, Path), f"Series {series}: not a Path"


# ---------------------------------------------------------------------------
# Path constants
# ---------------------------------------------------------------------------


class TestPathConstants:
    """Tests for path constant types."""

    def test_services_dir_is_path(self):
        assert isinstance(SERVICES_DIR, Path)

    def test_env_file_is_path(self):
        assert isinstance(ENV_FILE, Path)

    def test_services_dir_under_docker_config(self):
        """SERVICES_DIR is under docker-configurations/."""
        assert "docker-configurations" in str(SERVICES_DIR)
