#!/usr/bin/env python3
"""Tests pour scripts/audit/populate_quantconnect_cost.py — population de
metadata.cost pour les notebooks QuantConnect (Epic #8056 P1).

Couvre les fonctions pures hermétiques du cost-populator QC :
  - build_cost      : construit le dict metadata.cost canonique depuis PROFILES
  - populate_notebook : idempotent (skip si cost existe), dry-run vs apply, LF
  - audit_gap       : scan couverture QC (notebooks with/without cost)
  - main            : exit codes, --audit/--apply/--tranche/--by/--today

Aucun réseau, aucun subprocess. stdlib uniquement (argparse/datetime/json/sys/
pathlib). Notebooks synthétiques sous tmp_path (json minimal). audit_gap() lit
un chemin relatif au cwd -> tests via monkeypatch.chdir(tmp_path).

Logique métier testée :
  - sentinels cost-matrix QC (api_usd_est=0, api_provider=none, qcc_tokens_est=0,
    free_alternative="self" = le NB est sa propre alternative locale)
  - gpu_required propagation selon profil (CPU-only vs TFT/LSTM GPU)
  - idempotency : un NB déjà peuplé N'est JAMAIS écrasé (skipped-has-cost)
  - dry-run ne mute pas le fichier ; apply écrit LF-only (pas de CRLF)
"""

import importlib.util
import json
import sys
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
CHECK_PATH = HERE.parent / "populate_quantconnect_cost.py"


def _load_mod():
    spec = importlib.util.spec_from_file_location("populate_quantconnect_cost", CHECK_PATH)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


# --------------------------------------------------------------------------
# Helpers — notebooks synthétiques
# --------------------------------------------------------------------------

def _write_notebook(path: Path, metadata: dict | None = None) -> Path:
    """Notebook minimal valide : metadata optionnelle (ex {'cost': {...}})."""
    path.parent.mkdir(parents=True, exist_ok=True)
    nb = {"cells": [], "metadata": metadata or {}, "nbformat": 4, "nbformat_minor": 5}
    path.write_text(json.dumps(nb, ensure_ascii=False), encoding="utf-8")
    return path


# --------------------------------------------------------------------------
# PROFILES — structure canonique (sentinels QC)
# --------------------------------------------------------------------------

def test_profiles_nonempty_with_cpu_and_gpu_entries():
    mod = _load_mod()
    assert len(mod.PROFILES) > 0
    # au moins un profil CPU-only et un profil GPU-required
    assert any(not p.get("gpu_required") for p in mod.PROFILES.values())
    assert any(p.get("gpu_required") for p in mod.PROFILES.values())


def test_tranches_reference_valid_profile_keys():
    """TRANCHES[1].names doit être un sous-ensemble des clés PROFILES."""
    mod = _load_mod()
    for tranche, spec in mod.TRANCHES.items():
        for name in spec["names"]:
            assert name in mod.PROFILES, f"tranche {tranche} name {name} absent de PROFILES"
        assert "dir" in spec and "names" in spec


# --------------------------------------------------------------------------
# build_cost — construction du dict metadata.cost canonique
# --------------------------------------------------------------------------

def test_build_cost_cpu_only_profile_canonical_sentinels():
    mod = _load_mod()
    # research_l1_tsmom = profil CPU pur (pas de gpu_required/gpu_min/vram)
    cost = mod.build_cost("research_l1_tsmom", by="bot:test", today="2026-01-01")
    # sentinels QC : pas d'API, pas de QCC, alternative = lui-même
    assert cost["api_usd_est"] == 0.0
    assert cost["api_provider"] == "none"
    assert cost["qcc_tokens_est"] == 0
    assert cost["free_alternative"] == "self"
    assert cost["external_account"] == "none"
    assert cost["network"] is False
    # CPU-only defaults
    assert cost["gpu_required"] is False
    assert cost["gpu_min"] == 0
    assert cost["vram_gb"] == 0
    assert cost["vram_tier"] == "NONE"
    # provenance + date
    assert cost["metadata_written"] == "2026-01-01"
    assert cost["reproducibility"] == "HIGH"


def test_build_cost_gpu_profile_propagates_gpu_fields():
    mod = _load_mod()
    # m9_tft_vol_research = profil GPU (gpu_required=True, vram_gb=4, tier LOW)
    cost = mod.build_cost("m9_tft_vol_research", by="bot", today="2026-01-02")
    assert cost["gpu_required"] is True
    assert cost["gpu_min"] == 10
    assert cost["vram_gb"] == 4
    assert cost["vram_tier"] == "LOW"


def test_build_cost_carries_profile_notes_and_cpu_min():
    mod = _load_mod()
    cost = mod.build_cost("research_l3_trend", by="bot", today="2026-01-01")
    assert cost["cpu_min"] == mod.PROFILES["research_l3_trend"]["cpu_min"]
    assert cost["notes"] == mod.PROFILES["research_l3_trend"]["notes"]
    assert cost["validator"] == "papermill"


def test_build_cost_unknown_profile_raises():
    mod = _load_mod()
    with pytest.raises(KeyError):
        mod.build_cost("nonexistent_profile", by="bot", today="2026-01-01")


def test_build_cost_gpu_defaults_when_profile_has_no_gpu_keys():
    """Un profil sans gpu_min/vram_gb/vram_tier doit donner les defaults 0/NONE."""
    mod = _load_mod()
    # ML-Research-Template = profil CPU sans clés GPU
    cost = mod.build_cost("ML-Research-Template", by="bot", today="2026-01-01")
    assert cost["gpu_min"] == 0
    assert cost["vram_gb"] == 0
    assert cost["vram_tier"] == "NONE"
    assert cost["gpu_required"] is False


def test_build_cost_reduced_pedagogical_is_none():
    """Pas de réduction pédagogique documentée pour les NBs QC research."""
    mod = _load_mod()
    cost = mod.build_cost("research_l1_tsmom", by="bot", today="2026-01-01")
    assert cost["reduced_pedagogical"] is None


# --------------------------------------------------------------------------
# populate_notebook — idempotent, dry-run vs apply, LF, error handling
# --------------------------------------------------------------------------

def test_populate_notebook_skipped_no_profile(tmp_path):
    """Un notebook dont le nom ne matche aucune clé PROFILES -> skipped-no-profile."""
    mod = _load_mod()
    nb = _write_notebook(tmp_path / "UnknownNB.ipynb")
    status = mod.populate_notebook(nb, by="bot", today="2026-01-01", apply=True)
    assert status.startswith("skipped-no-profile")
    # fichier inchangé (pas de cost ajouté)
    assert "cost" not in json.loads(nb.read_text(encoding="utf-8")).get("metadata", {})


def test_populate_notebook_unreadable_returns_error(tmp_path):
    mod = _load_mod()
    nb = tmp_path / "research_l1_tsmom.ipynb"
    nb.write_text("{ ceci n'est pas du json valide }}}", encoding="utf-8")
    status = mod.populate_notebook(nb, by="bot", today="2026-01-01", apply=True)
    assert status.startswith("error:")


def test_populate_notebook_idempotent_skip_when_cost_exists(tmp_path):
    """CRITIQUE : un NB déjà peuplé (metadata.cost présent) N'est JAMAIS écrasé."""
    mod = _load_mod()
    existing_cost = {"api_usd_est": 999.0, "manual": True}  # valeur sentinelle arbitraire
    nb = _write_notebook(tmp_path / "research_l1_tsmom.ipynb", metadata={"cost": existing_cost})
    status = mod.populate_notebook(nb, by="bot", today="2026-01-01", apply=True)
    assert status == "skipped-has-cost"
    # le cost existant est préservé (pas écrasé par build_cost)
    meta = json.loads(nb.read_text(encoding="utf-8"))["metadata"]
    assert meta["cost"] == existing_cost


def test_populate_notebook_dry_run_does_not_write(tmp_path):
    """apply=False (dry-run) -> 'populated' retourné MAIS fichier inchangé."""
    mod = _load_mod()
    nb = _write_notebook(tmp_path / "research_l1_tsmom.ipynb")
    original = nb.read_bytes()
    status = mod.populate_notebook(nb, by="bot", today="2026-01-01", apply=False)
    assert status == "populated"
    assert nb.read_bytes() == original  # aucune mutation
    assert "cost" not in json.loads(nb.read_text(encoding="utf-8")).get("metadata", {})


def test_populate_notebook_apply_writes_cost_block(tmp_path):
    mod = _load_mod()
    nb = _write_notebook(tmp_path / "research_l1_tsmom.ipynb")
    status = mod.populate_notebook(nb, by="bot", today="2026-01-01", apply=True)
    assert status == "populated"
    data = json.loads(nb.read_text(encoding="utf-8"))
    cost = data["metadata"]["cost"]
    # le bloc écrit matche build_cost
    expected = mod.build_cost("research_l1_tsmom", by="bot", today="2026-01-01")
    assert cost == expected


def test_populate_notebook_apply_writes_lf_only(tmp_path):
    """Le write post-apply doit être LF-only (pas de CRLF), même sur Windows."""
    mod = _load_mod()
    nb = _write_notebook(tmp_path / "research_l1_tsmom.ipynb")
    mod.populate_notebook(nb, by="bot", today="2026-01-01", apply=True)
    assert b"\r\n" not in nb.read_bytes()


def test_populate_notebook_apply_preserves_existing_metadata(tmp_path):
    """Les metadata existantes (kernelspec, etc.) sont préservées, cost ajouté."""
    mod = _load_mod()
    existing_meta = {"kernelspec": {"name": "python3", "display_name": "Python 3"},
                     "language_info": {"name": "python"}}
    nb = _write_notebook(tmp_path / "research_l1_tsmom.ipynb", metadata=existing_meta)
    mod.populate_notebook(nb, by="bot", today="2026-01-01", apply=True)
    meta = json.loads(nb.read_text(encoding="utf-8"))["metadata"]
    assert meta["kernelspec"]["name"] == "python3"  # préservé
    assert "language_info" in meta
    assert "cost" in meta  # ajouté


def test_populate_notebook_apply_creates_metadata_if_absent(tmp_path):
    """Un notebook sans clé metadata du tout -> metadata créée avec cost."""
    mod = _load_mod()
    nb = tmp_path / "research_l1_tsmom.ipynb"
    nb.write_text(json.dumps({"cells": [], "nbformat": 4}), encoding="utf-8")
    mod.populate_notebook(nb, by="bot", today="2026-01-01", apply=True)
    meta = json.loads(nb.read_text(encoding="utf-8"))["metadata"]
    assert "cost" in meta


# --------------------------------------------------------------------------
# audit_gap — scan couverture QC (with/without cost)
# --------------------------------------------------------------------------

def test_audit_gap_counts_with_and_without_cost(tmp_path, monkeypatch, capsys):
    """audit_gap() scan un qc_root synthétique et compte les NBs avec/sans cost."""
    mod = _load_mod()
    qc_root = tmp_path / "MyIA.AI.Notebooks" / "QuantConnect"
    # 2 NBs avec cost, 1 sans, 1 _output (exclu)
    _write_notebook(qc_root / "sub" / "With1.ipynb", metadata={"cost": {"api_usd_est": 0}})
    _write_notebook(qc_root / "sub" / "With2.ipynb", metadata={"cost": {"x": 1}})
    _write_notebook(qc_root / "sub" / "Without.ipynb")
    _write_notebook(qc_root / "sub" / "nb_output.ipynb")  # exclu par filtre _output
    monkeypatch.chdir(tmp_path)
    rc = mod.audit_gap()
    out = capsys.readouterr().out
    assert rc == 0
    assert "2 WITH cost" in out
    assert "1 WITHOUT cost" in out
    assert "total 3" in out  # _output exclu -> 3 et non 4
    # le NB sans cost est listé
    assert "Without.ipynb" in out


def test_audit_gap_skips_unreadable_notebooks(tmp_path, monkeypatch, capsys):
    mod = _load_mod()
    qc_root = tmp_path / "MyIA.AI.Notebooks" / "QuantConnect"
    _write_notebook(qc_root / "Ok.ipynb", metadata={"cost": {"a": 1}})
    bad = qc_root / "Bad.ipynb"
    bad.parent.mkdir(parents=True, exist_ok=True)
    bad.write_text("not json", encoding="utf-8")
    monkeypatch.chdir(tmp_path)
    rc = mod.audit_gap()
    out = capsys.readouterr().out
    assert rc == 0
    # 1 lisible (WITH), 1 illisible (ignoré silencieusement, pas dans le total)
    assert "1 WITH cost" in out


def test_audit_gap_empty_dir(tmp_path, monkeypatch, capsys):
    mod = _load_mod()
    (tmp_path / "MyIA.AI.Notebooks" / "QuantConnect").mkdir(parents=True)
    monkeypatch.chdir(tmp_path)
    rc = mod.audit_gap()
    out = capsys.readouterr().out
    assert rc == 0
    assert "0 WITH cost" in out
    assert "0 WITHOUT cost" in out


# --------------------------------------------------------------------------
# main() — exit codes, --audit/--apply/--tranche/--by/--today
# --------------------------------------------------------------------------

def test_main_unknown_tranche_returns_2(tmp_path, monkeypatch, capsys):
    mod = _load_mod()
    monkeypatch.chdir(tmp_path)
    monkeypatch.setattr(sys, "argv", ["x", "--tranche", "99"])
    rc = mod.main()
    assert rc == 2
    assert "pas encore implémentée" in capsys.readouterr().err.lower() or "implement" in capsys.readouterr().err.lower()


def test_main_audit_route_calls_audit_gap(tmp_path, monkeypatch):
    mod = _load_mod()
    (tmp_path / "MyIA.AI.Notebooks" / "QuantConnect").mkdir(parents=True)
    monkeypatch.chdir(tmp_path)
    monkeypatch.setattr(sys, "argv", ["x", "--audit"])
    rc = mod.main()
    assert rc == 0  # audit_gap retourne 0


def test_main_dry_run_does_not_apply(tmp_path, monkeypatch, capsys):
    """Sans --apply, main() est dry-run : les NBs existants ne sont pas mutés."""
    mod = _load_mod()
    spec = mod.TRANCHES[1]
    base = tmp_path / spec["dir"]
    # crée UN NB valide de la tranche (nom matchant un profil)
    nb = _write_notebook(base / "research_l1_tsmom.ipynb")
    original = nb.read_bytes()
    # main utilise cwd relatif -> chdir tmp_path
    monkeypatch.chdir(tmp_path)
    monkeypatch.setattr(sys, "argv", ["x", "--tranche", "1", "--by", "bot:test"])
    rc = mod.main()
    assert rc == 0
    out = capsys.readouterr().out
    assert "DRY-RUN" in out
    assert nb.read_bytes() == original  # aucune mutation en dry-run


def test_main_apply_populates_notebook(tmp_path, monkeypatch, capsys):
    mod = _load_mod()
    spec = mod.TRANCHES[1]
    base = tmp_path / spec["dir"]
    nb = _write_notebook(base / "research_l1_tsmom.ipynb")
    monkeypatch.chdir(tmp_path)
    monkeypatch.setattr(sys, "argv", ["x", "--tranche", "1", "--apply", "--by", "bot:test",
                                      "--today", "2026-01-01"])
    rc = mod.main()
    assert rc == 0
    out = capsys.readouterr().out
    assert "APPLY" in out
    assert "populated" in out
    cost = json.loads(nb.read_text(encoding="utf-8"))["metadata"]["cost"]
    assert cost["metadata_written"] == "2026-01-01"


def test_main_apply_idempotent_second_run_skips(tmp_path, monkeypatch, capsys):
    """Un 2e run --apply sur un NB déjà peuplé -> skipped (idempotency via main)."""
    mod = _load_mod()
    spec = mod.TRANCHES[1]
    base = tmp_path / spec["dir"]
    nb = _write_notebook(base / "research_l1_tsmom.ipynb")
    monkeypatch.chdir(tmp_path)
    # 1er run : populate
    monkeypatch.setattr(sys, "argv", ["x", "--tranche", "1", "--apply", "--today", "2026-01-01"])
    mod.main()
    first = nb.read_bytes()
    # 2e run : doit skipper
    monkeypatch.setattr(sys, "argv", ["x", "--tranche", "1", "--apply", "--today", "2026-01-02"])
    rc = mod.main()
    assert rc == 0
    out = capsys.readouterr().out
    assert "skipped" in out
    assert nb.read_bytes() == first  # inchangé (metadata_written reste 2026-01-01)


def test_main_warns_on_missing_notebook(tmp_path, monkeypatch, capsys):
    """Un NB de la tranche absent du disque -> WARN, pas de crash."""
    mod = _load_mod()
    monkeypatch.chdir(tmp_path)
    monkeypatch.setattr(sys, "argv", ["x", "--tranche", "1", "--apply", "--today", "2026-01-01"])
    rc = mod.main()
    assert rc == 0  # les NBs manquants sont des WARN, pas des erreurs fatales
    out = capsys.readouterr().out
    assert "WARN" in out or "introuvable" in out.lower()


def test_main_today_defaults_to_today_iso(tmp_path, monkeypatch):
    """Sans --today, main() utilise datetime.date.today().isoformat()."""
    mod = _load_mod()
    spec = mod.TRANCHES[1]
    base = tmp_path / spec["dir"]
    nb = _write_notebook(base / "research_l1_tsmom.ipynb")
    monkeypatch.chdir(tmp_path)
    monkeypatch.setattr(sys, "argv", ["x", "--tranche", "1", "--apply"])
    mod.main()
    import datetime as _dt
    expected_today = _dt.date.today().isoformat()
    cost = json.loads(nb.read_text(encoding="utf-8"))["metadata"]["cost"]
    assert cost["metadata_written"] == expected_today
