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


def test_litmus2_gemini_bare_word_fp_suppressed(tmp_path):
    """FP-c.1172 : bare `gemini` matched the Conway's Game of Life self-replicator
    pattern (Andrew Wade, 2010) in notebooks Lean-16b/16c — variable `gemini_node`,
    file `gemini.rle`, print("Gemini ..."). A bare word is never an API call.
    The GoL code must NOT trigger api_used_but_cost_zero."""
    code = (
        'gemini_node, gemini_cells = load_pattern("gemini.rle")\n'
        'print("Gemini (Andrew Wade, 2010) - self-replicator oblique")\n'
    )
    res = _findings_for(
        tmp_path, code, cost_meta={"api_usd_est": 0.0, "api_provider": "none"}
    )
    assert "api_used_but_cost_zero" not in _patterns(res["findings"]), (
        "bare 'gemini' (GoL pattern) must not be detected as a Google API call"
    )


def test_litmus2_gemini_real_api_call_still_detected(tmp_path):
    """Real Gemini API references (SDK import or versioned model name) are still
    detected after the c.1172 tightening."""
    for code in (
        "import google.generativeai as genai\ngenai.GenerativeModel('gemini-1.5-flash')",
        "model = 'gemini-pro'\nresp = client.generate(model)",
    ):
        res = _findings_for(
            tmp_path, code, cost_meta={"api_usd_est": 0.0, "api_provider": "none"}
        )
        assert "api_used_but_cost_zero" in _patterns(res["findings"]), (
            f"real Gemini API call should still fire; code=\n{code}"
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


# ---------------------------------------------------------------------------
# Litmus 8 — api_cost_breakdown falsifiable gate (design-gate #8056)
# ---------------------------------------------------------------------------

def test_litmus8_breakdown_absent_ok(tmp_path):
    """Mono-provider: no api_cost_breakdown -> no finding (optional field)."""
    res = _findings_for(
        tmp_path, "x = 1", cost_meta={"api_usd_est": 0.0, "api_provider": "none"}
    )
    pats = _patterns(res["findings"])
    assert not any(p.startswith("api_cost_breakdown") for p in pats)


def test_litmus8_breakdown_sum_equals_total_ok(tmp_path):
    """Multi-provider with breakdown summing exactly to api_usd_est -> ok."""
    res = _findings_for(
        tmp_path,
        "x = 1",
        cost_meta={
            "api_usd_est": 0.42,
            "api_cost_breakdown": {"openai": 0.30, "anthropic": 0.12},
        },
    )
    pats = _patterns(res["findings"])
    assert "api_cost_breakdown_sum_mismatch" not in pats


def test_litmus8_breakdown_sum_mismatch_fails(tmp_path):
    """Breakdown sum != api_usd_est -> finding (the falsifiable gate bites)."""
    res = _findings_for(
        tmp_path,
        "x = 1",
        cost_meta={
            "api_usd_est": 0.50,
            "api_cost_breakdown": {"openai": 0.30, "anthropic": 0.12},  # 0.42 != 0.50
        },
    )
    assert "api_cost_breakdown_sum_mismatch" in _patterns(res["findings"])


def test_litmus8_breakdown_float_rounding_ok(tmp_path):
    """0.1+0.2-style float drift within 1-cent tolerance -> ok (no FP)."""
    res = _findings_for(
        tmp_path,
        "x = 1",
        cost_meta={
            "api_usd_est": 0.30,
            "api_cost_breakdown": {"openai": 0.10, "anthropic": 0.20},  # 0.30000000004
        },
    )
    assert "api_cost_breakdown_sum_mismatch" not in _patterns(res["findings"])


def test_litmus8_breakdown_malformed_fails(tmp_path):
    """Breakdown present but not a non-empty dict -> malformed finding."""
    res = _findings_for(
        tmp_path,
        "x = 1",
        cost_meta={"api_usd_est": 0.42, "api_cost_breakdown": "openai+anthropic"},
    )
    assert "api_cost_breakdown_malformed" in _patterns(res["findings"])


def test_litmus8_breakdown_non_numeric_values_fails(tmp_path):
    """Breakdown with non-numeric values -> non_numeric finding."""
    res = _findings_for(
        tmp_path,
        "x = 1",
        cost_meta={
            "api_usd_est": 0.42,
            "api_cost_breakdown": {"openai": 0.30, "anthropic": "twelve cents"},
        },
    )
    assert "api_cost_breakdown_non_numeric" in _patterns(res["findings"])


def test_litmus8_breakdown_without_numeric_total_fails(tmp_path):
    """Breakdown present but api_usd_est missing/non-numeric -> finding."""
    res = _findings_for(
        tmp_path,
        "x = 1",
        cost_meta={"api_cost_breakdown": {"openai": 0.30, "anthropic": 0.12}},
    )
    assert "api_usd_est_not_numeric" in _patterns(res["findings"])


def test_litmus8_breakdown_bool_value_rejected(tmp_path):
    """Un bool n'est pas un montant USD : float(True)==1.0 en Python trompe la
    sommation (bool est subclass de int). Le gate doit le rejeter explicitement
    (NIT Hermes review #8688), sinon {"openai": true} passerait en silence."""
    res = _findings_for(
        tmp_path,
        "x = 1",
        cost_meta={"api_usd_est": 1.0, "api_cost_breakdown": {"openai": True}},
    )
    pats = _patterns(res["findings"])
    assert "api_cost_breakdown_non_numeric" in pats
    assert "api_cost_breakdown_sum_mismatch" not in pats  # le bool est rejeté avant sommation


def test_litmus8_breakdown_int_value_accepted(tmp_path):
    """Un int (non-bool) est un montant USD valide : {openai: 1} -> somme 1.0 == total.
    Garde-fou anti-regression : le guard bool ne doit pas rejeter les ints légitimes."""
    res = _findings_for(
        tmp_path,
        "x = 1",
        cost_meta={"api_usd_est": 1.0, "api_cost_breakdown": {"openai": 1}},
    )
    pats = _patterns(res["findings"])
    assert "api_cost_breakdown_non_numeric" not in pats
    assert "api_cost_breakdown_sum_mismatch" not in pats


# ---------------------------------------------------------------------------
# Litmus 9 — validator_asserts_execution_but_cells_unexecuted
#
# Rend `validator` / `metadata_written` falsifiables : avant ce litmus, rien dans
# le dépôt ne pouvait les contredire. Cf docs/notebook-metadata/cost-matrix.md.
# ---------------------------------------------------------------------------

_LITMUS9_PATTERN = "validator_asserts_execution_but_cells_unexecuted"


def _notebook_cells(path: Path, specs, cost_meta=None) -> None:
    """Écrit un notebook dont chaque cellule code est décrite par un spec.

    spec = (source, execution_count, tags). `execution_count=None` = cellule
    jamais exécutée ; `tags` = liste de tags de cellule (ou None).
    Nécessaire pour le litmus 9 : les autres helpers laissent
    `execution_count: None` partout (défaut de `new_code_cell`), ce qui ne
    permet pas de distinguer exécuté / non exécuté.
    """
    path.parent.mkdir(parents=True, exist_ok=True)
    nb = new_notebook()
    cells = []
    for source, exec_count, tags in specs:
        cell = new_code_cell(source)
        cell["execution_count"] = exec_count
        if tags:
            cell["metadata"]["tags"] = list(tags)
        cells.append(cell)
    nb.cells = cells
    if cost_meta:
        nb.metadata["cost"] = cost_meta
    with path.open("w", encoding="utf-8") as f:
        nbformat.write(nb, f, version=4)


def _litmus9_patterns(tmp_path, specs, cost_meta):
    mod = _load_check()
    nb_path = tmp_path / "nb.ipynb"
    _notebook_cells(nb_path, specs, cost_meta=cost_meta)
    return _patterns(mod.check_notebook(nb_path, tmp_path)["findings"])


def test_litmus9_papermill_with_unexecuted_cell_flags(tmp_path):
    """`validator: papermill` affirme une exécution end-to-end. nbclient exécute
    toute cellule code non vide (même celles qui échouent) : un
    execution_count null PROUVE que la cellule n'a pas tourné."""
    pats = _litmus9_patterns(
        tmp_path,
        [("x = 1", 1, None), ("from AlgorithmImports import *", None, None)],
        {"validator": "papermill", "metadata_written": "2026-07-23T01:30Z"},
    )
    assert _LITMUS9_PATTERN in pats


def test_litmus9_papermill_all_executed_ok(tmp_path):
    """Toutes les cellules exécutées : la déclaration n'est contredite par rien."""
    pats = _litmus9_patterns(
        tmp_path,
        [("x = 1", 1, None), ("y = 2", 2, None)],
        {"validator": "papermill", "metadata_written": "2026-07-23T01:30Z"},
    )
    assert _LITMUS9_PATTERN not in pats


def test_litmus9_empty_cell_is_not_a_finding(tmp_path):
    """FP guard : nbclient SKIPPE les cellules code vides (`not source.strip()`),
    leur execution_count reste null après un run complet. Les flagger pousserait
    à modifier un notebook sain — même garde-fou que
    audit_quantbooks_unexec._is_unexecuted_code."""
    pats = _litmus9_patterns(
        tmp_path,
        [("x = 1", 1, None), ("   \n", None, None)],
        {"validator": "papermill"},
    )
    assert _LITMUS9_PATTERN not in pats


def test_litmus9_skip_tagged_cell_is_exempt(tmp_path):
    """Échappatoire honnête : une cellule délibérément non exécutable (code de
    référence destiné à un autre runtime) se DÉCLARE par un tag de skip. Le
    notebook cesse d'être contredit sans mentir, et le tag est visible dans le
    fichier — contrairement à une exception codée en dur dans l'outil."""
    for tag in ("skip-execution", "skip", "no-execute"):
        pats = _litmus9_patterns(
            tmp_path,
            [("x = 1", 1, None), ("reference_only()", None, [tag])],
            {"validator": "papermill"},
        )
        assert _LITMUS9_PATTERN not in pats, f"tag {tag} devrait exempter la cellule"


def test_litmus9_qc_cloud_validator_exempt(tmp_path):
    """`qc_cloud` = carve-out H.3 documenté : le runtime research QC n'existe sur
    aucune machine worker. Le validator n'affirme pas une exécution locale."""
    pats = _litmus9_patterns(
        tmp_path,
        [("qb = QuantBook()", None, None)],
        {"validator": "qc_cloud", "qcc_tokens_est": 400},
    )
    assert _LITMUS9_PATTERN not in pats


def test_litmus9_manual_validator_exempt(tmp_path):
    """`manual` = un humain a relu. Aucune affirmation d'exécution, donc rien à
    contredire — c'est aussi la valeur canonique vers laquelle un notebook non
    exécutable localement doit être corrigé."""
    pats = _litmus9_patterns(
        tmp_path,
        [("x = 1", None, None)],
        {"validator": "manual"},
    )
    assert _LITMUS9_PATTERN not in pats


def test_litmus9_absent_validator_exempt(tmp_path):
    """Pas de `validator` déclaré = pas de claim. Le défaut `manual` ne doit pas
    fabriquer un finding sur un notebook qui n'affirme rien."""
    pats = _litmus9_patterns(
        tmp_path,
        [("x = 1", None, None)],
        {"api_usd_est": 0.0},
    )
    assert _LITMUS9_PATTERN not in pats


def test_litmus9_dotnet_interactive_validator_flags(tmp_path):
    """`dotnet-interactive` affirme l'exécution du kernel .NET local, exigée par
    l'advisory #5214 (`execution_count != null` = preuve d'exécution locale)."""
    pats = _litmus9_patterns(
        tmp_path,
        [("Console.WriteLine(1);", None, None)],
        {"validator": "dotnet-interactive"},
    )
    assert _LITMUS9_PATTERN in pats


def test_litmus9_sk_visual_validator_flags(tmp_path):
    """`sk_visual` = vision check sur figures RENDUES : les figures viennent des
    sorties du notebook, donc l'exécution est entraînée par la déclaration."""
    pats = _litmus9_patterns(
        tmp_path,
        [("plt.show()", None, None)],
        {"validator": "sk_visual", "gpu_required": True},
    )
    assert _LITMUS9_PATTERN in pats


def test_litmus9_detail_names_the_cell_indices(tmp_path):
    """Le finding doit être actionnable : nommer les index de cellules, pas
    seulement leur nombre — sinon la remédiation demande de re-scanner."""
    mod = _load_check()
    nb_path = tmp_path / "nb.ipynb"
    _notebook_cells(
        nb_path,
        [("a = 1", 1, None), ("b = 2", None, None), ("c = 3", None, None)],
        cost_meta={"validator": "papermill", "metadata_written": "2026-07-23T01:30Z"},
    )
    findings = mod.check_notebook(nb_path, tmp_path)["findings"]
    detail = next(f["detail"] for f in findings if f["pattern"] == _LITMUS9_PATTERN)
    assert "1, 2" in detail
    assert "2026-07-23T01:30Z" in detail


# ---------------------------------------------------------------------------
# Mode flotte (c.58) — agregation par pattern + recensement par validator
# ---------------------------------------------------------------------------


def _fleet_notebooks(tmp_path):
    """Trois notebooks : deux porteurs de findings distincts, un sain."""
    a = tmp_path / "a.ipynb"
    _notebook(a, ["import torch; torch.cuda.is_available()"],
              cost_meta={"validator": "papermill", "gpu_required": False})
    b = tmp_path / "sub" / "b.ipynb"
    _notebook(b, ["import torch; torch.cuda.is_available()"],
              cost_meta={"validator": "manual", "gpu_required": False})
    clean = tmp_path / "clean.ipynb"
    _notebook(clean, ["x = 1"], cost_meta={"validator": "manual", "gpu_required": False})
    return [a, b, clean]


def test_aggregate_fleet_counts_patterns_and_validators(tmp_path):
    """Le mode flotte apporte deux comptes qu'aucun appel notebook-unique ne
    donne : findings PAR PATTERN, et recensement des validators declares."""
    mod = _load_check()
    agg = mod.aggregate_fleet(_fleet_notebooks(tmp_path), tmp_path)

    assert agg["scanned"] == 3
    assert agg["errors"] == []
    assert agg["patterns"]["gpu_used_but_not_declared"] == 2
    assert agg["validators"] == {"manual": 2, "papermill": 1}


def test_aggregate_fleet_excludes_clean_notebooks_from_detail(tmp_path):
    """`notebooks` porte le detail des SEULS notebooks a finding : un rapport
    ou 941 lignes saines noient 71 lignes utiles ne se lit pas."""
    mod = _load_check()
    agg = mod.aggregate_fleet(_fleet_notebooks(tmp_path), tmp_path)

    listed = {entry["notebook"] for entry in agg["notebooks"]}
    assert listed == {"a.ipynb", "sub/b.ipynb"}


def test_aggregate_fleet_unreadable_notebook_is_recorded_not_fatal(tmp_path):
    """Un .ipynb corrompu est compte dans `errors` et laisse la marche
    continuer : un audit qui s'arrete au premier fichier casse ne mesure rien.
    L'erreur reste VISIBLE — elle n'est pas avalee."""
    mod = _load_check()
    broken = tmp_path / "broken.ipynb"
    broken.write_text("{ pas du json", encoding="utf-8")
    good = tmp_path / "good.ipynb"
    _notebook(good, ["x = 1"], cost_meta={"validator": "manual"})

    agg = mod.aggregate_fleet([broken, good], tmp_path)

    assert agg["scanned"] == 1
    assert len(agg["errors"]) == 1
    assert agg["errors"][0]["notebook"] == "broken.ipynb"
    assert agg["errors"][0]["error"]


def test_format_fleet_report_shows_counts_and_offenders(tmp_path):
    """Le rapport humain doit porter les comptes agreges ET nommer les
    notebooks concernes (sinon il faut re-scanner pour agir)."""
    mod = _load_check()
    agg = mod.aggregate_fleet(_fleet_notebooks(tmp_path), tmp_path)
    report = mod.format_fleet_report(agg)

    assert "Notebooks scannes        : 3" in report
    assert "gpu_used_but_not_declared" in report
    assert "papermill" in report
    assert "a.ipynb" in report
    assert "clean.ipynb" not in report


def test_format_fleet_report_handles_empty_fleet(tmp_path):
    """Zero notebook scanne ne doit pas produire un rapport trompeur (ni
    planter) : les sections vides s'annoncent explicitement."""
    mod = _load_check()
    report = mod.format_fleet_report(mod.aggregate_fleet([], tmp_path))

    assert "Notebooks scannes        : 0" in report
    assert "(aucun)" in report
