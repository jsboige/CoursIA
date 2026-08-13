"""Tests for validate_qc_project_configs.py — QC project config.json schema audit (issue #6891 RESCOPE step 1)."""

import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from validate_qc_project_configs import (  # noqa: E402
    RESCOPE_TARGETS,
    NAME_FOLDER_WHITELIST,
    audit_all,
    audit_project_config,
    format_text,
    main,
)


def _make_project(root: Path, name: str, cfg: dict) -> Path:
    """Create a project folder with config.json under root."""
    proj_dir = root / "MyIA.AI.Notebooks" / "QuantConnect" / "projects" / name
    proj_dir.mkdir(parents=True, exist_ok=True)
    cfg_path = proj_dir / "config.json"
    cfg_path.write_text(json.dumps(cfg, indent=4), encoding="utf-8")
    return cfg_path


def _canonical(name: str) -> dict:
    """Return a RESCOPE-conformant config (name + id + canonical fields)."""
    return {
        "algorithm-language": "Python",
        "name": name,
        "id": 1,
        "parameters": {},
        "description": f"Test description for {name}",
        "organization-id": "d600793ee4caecb03441a09fc2d00f7f",
    }


# --- audit_project_config: conformant RESCOPE targets ---


class TestAuditConformant:
    """RESCOPE-conformant configs return [] (no violations)."""

    @pytest.mark.parametrize("name", sorted(RESCOPE_TARGETS))
    def test_rescope_target_canonical(self, name):
        cfg = _canonical(name)
        assert audit_project_config(name, cfg) == []

    def test_whitelisted_name_alias(self):
        """EMA-Cross-Stocks whitelisted as Framework-EMA-Cross-Stocks."""
        cfg = _canonical("Framework-EMA-Cross-Stocks")
        cfg["name"] = "Framework-EMA-Cross-Stocks"
        assert audit_project_config("EMA-Cross-Stocks", cfg) == []

    def test_empty_parameters_object_allowed(self):
        """`parameters: {}` is canonique for RESCOPE targets."""
        cfg = _canonical("FuturesTrend")
        cfg["parameters"] = {}
        assert audit_project_config("FuturesTrend", cfg) == []

    def test_id_can_be_2(self):
        """id field is int; value 1 is canonical but other ints are valid."""
        cfg = _canonical("FuturesTrend")
        cfg["id"] = 2
        assert audit_project_config("FuturesTrend", cfg) == []


# --- audit_project_config: violations ---


class TestAuditViolations:
    def test_missing_name(self):
        cfg = _canonical("FuturesTrend")
        del cfg["name"]
        msgs = audit_project_config("FuturesTrend", cfg)
        assert any("name" in m for m in msgs)

    def test_missing_id(self):
        cfg = _canonical("FuturesTrend")
        del cfg["id"]
        msgs = audit_project_config("FuturesTrend", cfg)
        assert any("'id'" in m for m in msgs)

    def test_id_must_be_int(self):
        cfg = _canonical("FuturesTrend")
        cfg["id"] = "1"  # string, pas int
        msgs = audit_project_config("FuturesTrend", cfg)
        assert any("id" in m and "int" in m for m in msgs)

    def test_id_must_be_int_float(self):
        cfg = _canonical("FuturesTrend")
        cfg["id"] = 1.0  # float, pas int
        msgs = audit_project_config("FuturesTrend", cfg)
        assert any("id" in m and "int" in m for m in msgs)

    def test_name_must_match_folder(self):
        cfg = _canonical("FuturesTrend")
        cfg["name"] = "FuturesTranche"  # typo (incident fondateur)
        msgs = audit_project_config("FuturesTrend", cfg)
        assert any("name" in m and "FuturesTranche" in m for m in msgs)

    def test_missing_algorithm_language(self):
        cfg = _canonical("FuturesTrend")
        del cfg["algorithm-language"]
        msgs = audit_project_config("FuturesTrend", cfg)
        assert any("algorithm-language" in m for m in msgs)

    def test_missing_parameters(self):
        cfg = _canonical("FuturesTrend")
        del cfg["parameters"]
        msgs = audit_project_config("FuturesTrend", cfg)
        assert any("parameters" in m for m in msgs)

    def test_missing_organization_id(self):
        cfg = _canonical("FuturesTrend")
        del cfg["organization-id"]
        msgs = audit_project_config("FuturesTrend", cfg)
        assert any("organization-id" in m for m in msgs)


# --- audit_project_config: hors scope (early-return) ---


class TestAuditOutOfScope:
    """Configs hors scope ne produisent pas de violations (early-return)."""

    def test_legacy_cloud_id_schema(self):
        """`language: Py` schema = legacy cloud-id holder, hors scope."""
        cfg = {
            "cloud-id": 28692516,
            "language": "Py",
            "local-id": "abc123",
            "organization-id": "d600793ee4caecb03441a09fc2d00f7f",
        }
        assert audit_project_config("DualMomentum", cfg) == []

    def test_cloud_id_only(self):
        """Projet deja pousse au cloud (champ cloud-id present)."""
        cfg = {
            "cloud-id": 28692516,
            "language": "Py",
            "local-id": "abc123",
            "organization-id": "d600793ee4caecb03441a09fc2d00f7f",
        }
        assert audit_project_config("SomeProject", cfg) == []

    def test_bare_local_id_only(self):
        """Bare `{local-id}` config minimal = hors scope."""
        cfg = {"local-id": "abc123"}
        assert audit_project_config("SomeProject", cfg) == []

    def test_empty_config(self):
        """Empty {} config = hors scope (early-return sur not cfg)."""
        assert audit_project_config("SomeProject", {}) == []

    def test_legacy_with_algorithm_language_skipped_via_cloud_id(self):
        """Has both legacy `language` AND `cloud-id` = skip via cloud-id branch."""
        cfg = {
            "cloud-id": 12345,
            "language": "Py",
            "local-id": "x",
            "organization-id": "d600793ee4caecb03441a09fc2d00f7f",
        }
        assert audit_project_config("SomeProject", cfg) == []

    def test_migrated_legacy_algorithm_language_with_cloud_id(self):
        """Migration cible (issue #6891 etape 2):
        `algorithm-language: Python` + `cloud-id` (integer) + pas de name/id/parameters
        = legacy_cloud_id_holders (informationnel), pas de violation.

        Couvre les 4 projets migres : DualMomentum, MeanReversion,
        Trend-Following, VolTarget-Momentum. Avant migration, ils utilisaient
        `language: Py` ; apres migration, ils gardent `cloud-id` legitime et
        le validator les classe comme cloud-id holders (early-return L174).
        """
        cfg = {
            "cloud-id": 28692516,
            "algorithm-language": "Python",
            "organization-id": "d600793ee4caecb03441a09fc2d00f7f",
        }
        assert audit_project_config("DualMomentum", cfg) == []


# --- audit_all: integration ---


class TestAuditAll:
    def test_audit_rescope_targets_pass(self, tmp_path):
        """5 RESCOPE targets normalized -> 0 violations, 5 conformant_rescope."""
        for name in RESCOPE_TARGETS:
            _make_project(tmp_path, name, _canonical(name))
        report = audit_all(tmp_path)
        assert report["violations"] == []
        assert sorted(report["conformant_rescope"]) == sorted(RESCOPE_TARGETS)
        assert report["conformant_other"] == []

    def test_audit_legacy_projects_listed_but_not_failing(self, tmp_path):
        """Legacy cloud-id holders listed as legacy, not violations."""
        for name in RESCOPE_TARGETS:
            _make_project(tmp_path, name, _canonical(name))
        legacy_cfg = {
            "cloud-id": 28692516,
            "language": "Py",
            "local-id": "x",
            "organization-id": "d600793ee4caecb03441a09fc2d00f7f",
        }
        _make_project(tmp_path, "DualMomentum", legacy_cfg)
        _make_project(tmp_path, "MeanReversion", legacy_cfg)

        report = audit_all(tmp_path)
        assert report["violations"] == []
        assert "DualMomentum" in report["legacy_cloud_id_holders"]
        assert "MeanReversion" in report["legacy_cloud_id_holders"]

    def test_audit_missing_name_on_rescope_target(self, tmp_path):
        """FuturesTrend missing `name` field -> 1 violation on rescope target."""
        cfg = _canonical("FuturesTrend")
        del cfg["name"]
        _make_project(tmp_path, "FuturesTrend", cfg)
        # Other 4 OK
        for name in RESCOPE_TARGETS - {"FuturesTrend"}:
            _make_project(tmp_path, name, _canonical(name))

        report = audit_all(tmp_path)
        assert len(report["violations"]) == 1
        assert report["violations"][0]["project"] == "FuturesTrend"
        assert any("name" in m for m in report["violations"][0]["messages"])

    def test_audit_no_projects_dir(self, tmp_path):
        """No projects dir -> empty report, no crash."""
        report = audit_all(tmp_path)
        assert report["violations"] == []
        assert report["legacy_cloud_id_holders"] == []
        assert report["conformant_rescope"] == []
        assert report["conformant_other"] == []

    def test_audit_invalid_json_skipped(self, tmp_path):
        """Unparseable config.json -> parse_errors entry, NOT conformant."""
        proj_dir = tmp_path / "MyIA.AI.Notebooks" / "QuantConnect" / "projects" / "FuturesTrend"
        proj_dir.mkdir(parents=True, exist_ok=True)
        (proj_dir / "config.json").write_text("{invalid json,", encoding="utf-8")
        # Other 4 OK
        for name in RESCOPE_TARGETS - {"FuturesTrend"}:
            _make_project(tmp_path, name, _canonical(name))

        report = audit_all(tmp_path)
        # Broken FuturesTrend = parse error, NOT a violation (different category)
        assert report["violations"] == []
        assert "FuturesTrend" not in report["conformant_rescope"]
        assert any(e["project"] == "FuturesTrend" for e in report["parse_errors"])

    def test_audit_non_dict_json_parse_error(self, tmp_path):
        """Top-level array = parse error (wrong JSON type), not silent skip."""
        proj_dir = tmp_path / "MyIA.AI.Notebooks" / "QuantConnect" / "projects" / "FuturesTrend"
        proj_dir.mkdir(parents=True, exist_ok=True)
        (proj_dir / "config.json").write_text("[]", encoding="utf-8")

        report = audit_all(tmp_path)
        assert any(e["project"] == "FuturesTrend" for e in report["parse_errors"])
        assert "FuturesTrend" not in report["conformant_rescope"]

    def test_audit_real_repo(self, tmp_path):
        """Run audit_all on a synthetic-but-realistic 35-project layout."""
        # 5 RESCOPE conformant
        for name in RESCOPE_TARGETS:
            _make_project(tmp_path, name, _canonical(name))
        # 13 legacy cloud-id holders
        legacy_names = ["AllWeather", "DualMomentum", "MeanReversion",
                        "Trend-Following", "VolTarget-Momentum", "Framework_Alpha",
                        "Alpha-MyStrategy", "Test_Staging", "BackupProject",
                        "StrategyA", "StrategyB", "StrategyC", "StrategyD"]
        for name in legacy_names:
            cfg = {
                "cloud-id": 12345,
                "language": "Py",
                "local-id": "x",
                "organization-id": "d600793ee4caecb03441a09fc2d00f7f",
            }
            _make_project(tmp_path, name, cfg)
        # Other (non-RESCOPE) bare local-id-only
        _make_project(tmp_path, "BareProject", {"local-id": "z"})

        report = audit_all(tmp_path)
        assert report["violations"] == []
        assert len(report["legacy_cloud_id_holders"]) == 13
        assert len(report["conformant_rescope"]) == 5


# --- format_text ---


class TestFormatText:
    def test_format_text_no_violations(self):
        report = {
            "scope_target": sorted(RESCOPE_TARGETS),
            "conformant_rescope": sorted(RESCOPE_TARGETS),
            "conformant_other": [],
            "legacy_cloud_id_holders": ["DualMomentum"],
            "violations": [],
            "parse_errors": [],
        }
        out = format_text(report)
        assert "=== QC project config schema audit ===" in out
        assert "scope target (5)" in out
        assert "conformant (rescope, 5)" in out
        assert "legacy cloud-id (1)" in out
        assert "(none)" in out
        assert "Summary: 0 violation" in out

    def test_format_text_with_violations(self):
        report = {
            "scope_target": sorted(RESCOPE_TARGETS),
            "conformant_rescope": ["RiskParity"],
            "conformant_other": [],
            "legacy_cloud_id_holders": [],
            "violations": [{"project": "FuturesTrend", "messages": ["missing name"]}],
            "parse_errors": [],
        }
        out = format_text(report)
        assert "=== VIOLATIONS ===" in out
        assert "FuturesTrend:" in out
        assert "missing name" in out
        assert "Summary: 1 violation" in out


# --- main() CLI ---


class TestMain:
    def test_main_check_exits_zero_when_rescope_clean(self, tmp_path, capsys):
        """All 5 RESCOPE targets conformant + --check -> exit 0."""
        for name in RESCOPE_TARGETS:
            _make_project(tmp_path, name, _canonical(name))

        rc = main(["--root", str(tmp_path), "--check"])
        assert rc == 0

    def test_main_check_exits_one_when_rescope_violates(self, tmp_path, capsys):
        """RESCOPE target missing name + --check -> exit 1."""
        cfg = _canonical("FuturesTrend")
        del cfg["name"]
        _make_project(tmp_path, "FuturesTrend", cfg)
        for name in RESCOPE_TARGETS - {"FuturesTrend"}:
            _make_project(tmp_path, name, _canonical(name))

        rc = main(["--root", str(tmp_path), "--check"])
        assert rc == 1

    def test_main_check_exits_zero_for_out_of_scope_violations(self, tmp_path, capsys):
        """Out-of-scope violations don't block --check."""
        # RESCOPE clean
        for name in RESCOPE_TARGETS:
            _make_project(tmp_path, name, _canonical(name))
        # Non-RESCOPE project missing name -> violation but NOT a blocker
        bad_cfg = {
            "algorithm-language": "Python",
            "id": 1,
            "parameters": {},
            "description": "x",
            "organization-id": "d600793ee4caecb03441a09fc2d00f7f",
        }
        # missing name
        _make_project(tmp_path, "OutOfScopeProject", bad_cfg)

        rc = main(["--root", str(tmp_path), "--check"])
        # Out-of-scope violations don't block --check (anti-regression rule D)
        assert rc == 0

    def test_main_json_output(self, tmp_path, capsys):
        for name in RESCOPE_TARGETS:
            _make_project(tmp_path, name, _canonical(name))

        rc = main(["--root", str(tmp_path), "--json"])
        assert rc == 0
        out = capsys.readouterr().out
        import json as _json
        parsed = _json.loads(out)
        assert "violations" in parsed
        assert parsed["violations"] == []


if __name__ == "__main__":
    pytest.main([__file__, "-v"])