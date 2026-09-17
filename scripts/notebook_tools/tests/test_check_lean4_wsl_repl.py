"""Tests unitaires des fonctions pures de check_lean4_wsl_repl (#11874).

Les sondes reelles (WSL + repl) sont couvertes par le run documente dans la PR
(REPL_LAKE_ONLY sur po-2026) — pas par ces tests.
"""

import json
import subprocess
import sys
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from check_lean4_wsl_repl import (  # noqa: E402
    TIMEOUT_RC,
    classify,
    main,
    parse_repl_json,
    wsl_bash,
)


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


def test_classify_lake_only_when_bare_path_times_out():
    """Le repl nu qui PEND est un chemin casse, au meme titre qu'un `Unknown
    constant` : la docstring range explicitement « le fallback stub et /tmp sont
    casses » dans REPL_LAKE_ONLY (#16176, finding 2)."""
    verdict, detail = classify([
        P("TIMEOUT_OR_UNPARSEABLE", "bare_path_tmp"),
        P("OK", "lake", toolchain="leanprover/lean4:v4.32.1"),
    ])
    assert verdict == "REPL_LAKE_ONLY"
    assert "bare_path_tmp" in detail


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


# --- une expiration est un verdict, pas un traceback (#16176, finding 2) ---


def test_wsl_bash_returns_timeout_rc_instead_of_raising():
    with patch("check_lean4_wsl_repl.subprocess.run",
               side_effect=subprocess.TimeoutExpired(cmd="repl", timeout=90)):
        assert wsl_bash("#eval 2+2") == (TIMEOUT_RC, "")


def test_main_renders_a_verdict_when_every_probe_times_out(capsys):
    """Reproduction du defaut mesure : sur une machine ou le repl pend, `main()`
    mourait en traceback (exit 1) a `probe_path("/tmp", ...)` au lieu de rendre
    le verdict `REPL_TIMEOUT` que sa propre taxonomie prevoit."""
    with patch("check_lean4_wsl_repl.wsl_bash", return_value=(TIMEOUT_RC, "")), \
            patch.object(sys, "argv", ["check_lean4_wsl_repl.py", "--json", "--skip-stub"]):
        rc = main()
    out = capsys.readouterr()
    assert rc == 2, out.err
    report = json.loads(out.out)
    assert report["verdict"] == "REPL_TIMEOUT"
    assert report["probes"] == []
    assert "expiration WSL" in report["detail"]
