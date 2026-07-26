"""Tests for scripts/audit/check_cost_metadata.py — cost-matrix coherence checker.

Issue #8056 / schema #8376. Covers the 7 litmus cross-checks and the canonical
vs legacy cost-meta extraction. Special attention to the three FP-guard fixes:
  - Litmus 2 (api_used_but_cost_zero): local-provider suppress (#8589)
  - Litmus 4 (free_alternative_missing): sentinel + dual-base (#8588)
  - Litmus 7 (qc_notebook_no_qcc_estimate): QCC estimate presence (#8587)

Uses synthetic mini-notebooks under tmp_path so tests do not depend on the live
repo state.
"""
import importlib.util
from pathlib import Path

import nbformat
from nbformat.v4 import new_code_cell, new_markdown_cell, new_notebook

HERE = Path(__file__).resolve().parent
CHECK_PATH = HERE.parent / "check_cost_metadata.py"


def _load_check():
    spec = importlib.util.spec_from_file_location("check_cost_metadata", CHECK_PATH)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def _notebook(path: Path, code_sources, cost_meta=None, legacy_cost_md=None) -> None:
    """Write a minimal valid .ipynb (constructed via nbformat.v4 so it passes
    nbformat.read validation in check_notebook).

    - cost_meta: dict placed at nb.metadata['cost'] (canonical form, #8056).
    - legacy_cost_md: if set, prepend a markdown `--- cost: ... ---` cell
      (legacy fallback) INSTEAD of canonical metadata.
    """
    path.parent.mkdir(parents=True, exist_ok=True)
    nb = new_notebook()
    cells = []
    if legacy_cost_md is not None:
        cells.append(new_markdown_cell(legacy_cost_md))
    cells.extend(new_code_cell(src) for src in code_sources)
    nb.cells = cells
    if cost_meta:
        nb.metadata["cost"] = cost_meta
    with path.open("w", encoding="utf-8") as f:
        nbformat.write(nb, f, version=4)


def _findings_for(tmp_path, code_source, cost_meta, legacy_cost_md=None, repo_root=None):
    """Run check_notebook on a 1-code-cell notebook, return the findings list."""
    mod = _load_check()
    nb_path = tmp_path / "nb.ipynb"
    _notebook(nb_path, [code_source], cost_meta=cost_meta, legacy_cost_md=legacy_cost_md)
    root = repo_root if repo_root is not None else tmp_path
    return mod.check_notebook(nb_path, root)


def _patterns(findings):
    return {f["pattern"] for f in findings}


# ---------------------------------------------------------------------------
# Cost-meta extraction (canonical vs legacy fallback)
# ---------------------------------------------------------------------------


def test_cost_meta_canonical_from_metadata(tmp_path):
    """nb.metadata['cost'] is the canonical source (design-gate c.866, #8056)."""
    nb_path = tmp_path / "nb.ipynb"
    _notebook(nb_path, ["x = 1"], cost_meta={"api_provider": "openai"})
    mod = _load_check()
    res = mod.check_notebook(nb_path, tmp_path)
    assert res["cost_meta_found"] is True
    assert res["cost_source"] == "metadata"
    assert res["cost_meta"]["api_provider"] == "openai"


def test_cost_meta_legacy_markdown_fallback(tmp_path):
    """When no metadata.cost, the legacy `--- cost: ---` markdown cell is read."""
    legacy = "---\ncost:\n  api_provider: openai\n  api_usd_est: 0.5\n---\n"
    mod = _load_check()
    nb_path = tmp_path / "legacy.ipynb"
    _notebook(nb_path, ["x = 1"], legacy_cost_md=legacy)
    res = mod.check_notebook(nb_path, tmp_path)
    assert res["cost_meta_found"] is True
    assert res["cost_source"] == "markdown_cell"
    assert res["cost_meta"]["api_provider"] == "openai"


def test_cost_meta_absent(tmp_path):
    """No cost metadata at all -> cost_meta_found False, no spurious findings."""
    res = _findings_for(tmp_path, "x = 1", cost_meta=None)
    assert res["cost_meta_found"] is False
    assert res["findings"] == []


# ---------------------------------------------------------------------------
# Litmus 1 — gpu_used_but_not_declared
# ---------------------------------------------------------------------------


def test_litmus1_gpu_used_not_declared(tmp_path):
    code = "import torch\nmodel = net.cuda()"
    res = _findings_for(tmp_path, code, cost_meta={"gpu_required": False})
    assert "gpu_used_but_not_declared" in _patterns(res["findings"])


def test_litmus1_gpu_declared_no_finding(tmp_path):
    code = "import torch\nmodel = net.cuda()"
    res = _findings_for(tmp_path, code, cost_meta={"gpu_required": True})
    assert "gpu_used_but_not_declared" not in _patterns(res["findings"])


# ---------------------------------------------------------------------------
# Litmus 2 — api_used_but_cost_zero (FP guard: local provider, #8589)
# ---------------------------------------------------------------------------


def test_litmus2_api_used_cost_zero_cloud_provider(tmp_path):
    """Cloud/paid provider + api_usd_est=0 -> CRITICAL finding fires."""
    code = "from openai import OpenAI\nclient = OpenAI()"
    res = _findings_for(
        tmp_path, code, cost_meta={"api_usd_est": 0.0, "api_provider": "none"}
    )
    pats = _patterns(res["findings"])
    assert "api_used_but_cost_zero" in pats
    finding = next(f for f in res["findings"] if f["pattern"] == "api_used_but_cost_zero")
    assert finding["severity"] == "CRITICAL"


def test_litmus2_api_used_cost_zero_local_provider_suppressed(tmp_path):
    """Local/free provider + openai keyword -> NO finding (OpenAI-compatible
    client pointed at a local vLLM/Ollama/HF server, not a paid cloud call)."""
    code = "from openai import OpenAI\nclient = OpenAI(base_url='http://localhost:8000/v1')"
    for provider in ("local", "hf", "huggingface", "ollama"):
        res = _findings_for(
            tmp_path, code, cost_meta={"api_usd_est": 0.0, "api_provider": provider}
        )
        assert "api_used_but_cost_zero" not in _patterns(res["findings"]), (
            f"provider={provider} should suppress the FP"
        )


# ---------------------------------------------------------------------------
# Litmus 3 — token_required_but_no_account
# ---------------------------------------------------------------------------


def test_litmus3_token_required_no_account(tmp_path):
    code = "import os\ntoken = os.getenv('HF_TOKEN')"
    res = _findings_for(
        tmp_path, code, cost_meta={"external_account": "none"}
    )
    assert "token_required_but_no_account" in _patterns(res["findings"])


def test_litmus3_token_required_with_account(tmp_path):
    code = "import os\ntoken = os.getenv('HF_TOKEN')"
    res = _findings_for(
        tmp_path, code, cost_meta={"external_account": "hf"}
    )
    assert "token_required_but_no_account" not in _patterns(res["findings"])


# ---------------------------------------------------------------------------
# Litmus 4 — free_alternative_missing (sentinel + dual-base, #8588)
# ---------------------------------------------------------------------------


def test_litmus4_free_alternative_missing_path(tmp_path):
    """A path-shaped free_alternative pointing nowhere -> finding."""
    res = _findings_for(
        tmp_path, "x = 1", cost_meta={"free_alternative": "does/not/exist.ipynb"}
    )
    assert "free_alternative_missing" in _patterns(res["findings"])


def test_litmus4_free_alternative_sentinels_suppressed(tmp_path):
    """Sentinel values (self/none/null/N/A) are semantic labels, not paths."""
    for sentinel in ("self", "none", "null", "n/a", "N/A", ""):
        res = _findings_for(
            tmp_path, "x = 1", cost_meta={"free_alternative": sentinel}
        )
        assert "free_alternative_missing" not in _patterns(res["findings"]), (
            f"sentinel={sentinel!r} should be silent"
        )


def test_litmus4_free_alternative_dual_base_resolves(tmp_path):
    """A basename free_alternative resolves under MyIA.AI.Notebooks/ (dual-base
    check) -> NO finding. Reproduces the GenAI/Texte pattern surfaced by #8588."""
    # create the target under the notebooks subtree of the repo_root
    target = tmp_path / "MyIA.AI.Notebooks" / "GenAI" / "Texte" / "10_LocalLlama.ipynb"
    _notebook(target, ["x = 1"])
    res = _findings_for(
        tmp_path, "x = 1", cost_meta={"free_alternative": "GenAI/Texte/10_LocalLlama.ipynb"}
    )
    assert "free_alternative_missing" not in _patterns(res["findings"])


# ---------------------------------------------------------------------------
# Litmus 5 — qc_notebook_no_validator
# ---------------------------------------------------------------------------


def test_litmus5_qc_notebook_no_validator(tmp_path):
    """QuantBook used + validator != qc_cloud -> finding."""
    code = "qb = QuantBook()\nsymbol = qb.AddEquity('SPY').Symbol"
    res = _findings_for(
        tmp_path,
        code,
        cost_meta={"validator": "manual", "qcc_tokens_est": 800},
    )
    assert "qc_notebook_no_validator" in _patterns(res["findings"])


def test_litmus5_qc_notebook_with_qc_cloud_validator(tmp_path):
    code = "qb = QuantBook()"
    res = _findings_for(
        tmp_path,
        code,
        cost_meta={"validator": "qc_cloud", "qcc_tokens_est": 800},
    )
    pats = _patterns(res["findings"])
    assert "qc_notebook_no_validator" not in pats
    assert "qc_notebook_no_qcc_estimate" not in pats  # qcc set, litmus 7 silent


# ---------------------------------------------------------------------------
# Litmus 6 — gpu_no_visual_validator
# ---------------------------------------------------------------------------


def test_litmus6_gpu_no_visual_validator(tmp_path):
    """gpu_required=True + validator not sk_visual/papermill -> finding."""
    res = _findings_for(
        tmp_path, "x = 1", cost_meta={"gpu_required": True, "validator": "manual"}
    )
    assert "gpu_no_visual_validator" in _patterns(res["findings"])


def test_litmus6_gpu_with_sk_visual_ok(tmp_path):
    res = _findings_for(
        tmp_path, "x = 1", cost_meta={"gpu_required": True, "validator": "sk_visual"}
    )
    assert "gpu_no_visual_validator" not in _patterns(res["findings"])


# ---------------------------------------------------------------------------
# Litmus 7 — qc_notebook_no_qcc_estimate (#8587)
# ---------------------------------------------------------------------------


def test_litmus7_qc_notebook_no_qcc_estimate(tmp_path):
    """QuantBook used + qcc_tokens_est absent/0 -> finding."""
    code = "qb = QuantBook()"
    res = _findings_for(
        tmp_path, code, cost_meta={"validator": "qc_cloud"}
    )
    assert "qc_notebook_no_qcc_estimate" in _patterns(res["findings"])


def test_litmus7_qc_notebook_with_qcc_estimate_ok(tmp_path):
    code = "qb = QuantBook()"
    res = _findings_for(
        tmp_path,
        code,
        cost_meta={"validator": "qc_cloud", "qcc_tokens_est": 1200},
    )
    assert "qc_notebook_no_qcc_estimate" not in _patterns(res["findings"])
