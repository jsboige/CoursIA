"""Tests unitaires des fonctions pures de check_lean4_wsl_repl (#11874).

Les sondes reelles (WSL + repl) sont couvertes par le run documente dans la PR
(REPL_LAKE_ONLY sur po-2026) — pas par ces tests.
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from check_lean4_wsl_repl import classify, parse_repl_json  # noqa: E402


def P(positive, label, **kw):
    r = {"label": label, "positive": positive, "positive_data": None, "bogus_mute": None}
    r.update(kw)
    return r


def test_parse_extracts_json_from_noisy_output():
    raw = 'some lake warning\n{"messages": [{"severity": "info", "data": "4"}], "env": 0}\n'
    parsed = parse_repl_json(raw)
    assert parsed is not None and parsed["env"] == 0


def test_parse_returns_none_on_garbage():
    assert parse_repl_json("no json here") is None
    assert parse_repl_json("") is None


def test_classify_healthy_all_paths():
    verdict, _ = classify([P("OK", "bare_path_tmp"), P("OK", "stub_fallback"), P("OK", "lake")])
    assert verdict == "REPL_HEALTHY"


def test_classify_healthy_notes_mute_imports():
    verdict, detail = classify([P("OK", "bare_path_tmp", bogus_mute=True), P("OK", "lake")])
    assert verdict == "REPL_HEALTHY"
    assert "MUET" in detail and "bare_path_tmp" in detail


def test_classify_lake_only_latent_state():
    # etat documente sur po-2026 : repl nu et stub casses, lake OK
    verdict, detail = classify([
        P("STDLIB_BROKEN", "bare_path_tmp", positive_data="Unknown constant `OfNat`"),
        P("STDLIB_BROKEN", "stub_fallback", positive_data="Unknown constant `OfNat`"),
        P("OK", "lake", toolchain="leanprover/lean4:v4.32.1"),
    ])
    assert verdict == "REPL_LAKE_ONLY"
    assert "v4.32.1" in detail and "bare_path_tmp" in detail


def test_classify_fully_broken_ai01_state():
    # etat documente sur ai-01 avant remede : meme via lake, le controle echoue
    verdict, _ = classify([
        P("STDLIB_BROKEN", "bare_path_tmp", positive_data="Unknown constant `OfNat`"),
        P("STDLIB_BROKEN", "lake", positive_data="Unknown constant `OfNat`"),
    ])
    assert verdict == "REPL_STDLIB_BROKEN"


def test_classify_all_timeout():
    verdict, _ = classify([P("TIMEOUT_OR_UNPARSEABLE", "bare_path_tmp"),
                           P("TIMEOUT_OR_UNPARSEABLE", "lake")])
    assert verdict == "REPL_TIMEOUT"


def test_classify_empty_is_missing():
    verdict, _ = classify([])
    assert verdict == "REPL_MISSING"


def test_classify_heterogeneous_is_uncertain():
    verdict, _ = classify([P("OTHER", "bare_path_tmp"), P("OK", "lake")])
    assert verdict == "REPL_UNCERTAIN"
