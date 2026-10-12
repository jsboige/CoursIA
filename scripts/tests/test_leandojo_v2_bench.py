#!/usr/bin/env python3
"""Anti-drift pins pour le banc volet B (#18430) : leandojo_v2_bench.py.

Le banc compare le prouveur LeanDojo-v2 au harnais maison sur le rung 52
(CALIBRATION_CONWAY_LAS_ROUND_TRIP). Sa validite repose sur des joints que
rien ne garde coherents entre eux : le modele LLM doit rester celui des
traces maison (sinon la comparaison porte sur le moteur, pas l'organe), le
budget doit rester aligne sur la passe 17 (1 800 s), l'enonce doit rester
celui du rung, et le contournement LEAN_PATH doit continuer a parser la
sortie integrale de ``lake env printenv`` (les deux bugs mesures de
pantograph 0.3.15). Ce test pince chaque joint sans reseau ni WSL : tout
drift leve ici avant de fausser une mesure.

Run: python -m pytest scripts/tests/test_leandojo_v2_bench.py
"""
import importlib.util
import subprocess
import sys
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parents[2]
BENCH = (
    REPO
    / "MyIA.AI.Notebooks/SymbolicAI/Lean/agent_tests/prover"
    / "integration/leandojo_v2_bench.py"
)


def _load_bench():
    spec = importlib.util.spec_from_file_location("leandojo_v2_bench", BENCH)
    mod = importlib.util.module_from_spec(spec)
    sys.modules["leandojo_v2_bench"] = mod  # requis par les dataclasses
    spec.loader.exec_module(mod)
    return mod


@pytest.fixture(scope="module")
def bench():
    return _load_bench()


def test_bench_file_exists():
    assert BENCH.is_file(), f"banc introuvable: {BENCH}"


def test_model_matches_house_traces(bench):
    # config.py PROVIDERS["openrouter"] : anthropic/claude-opus-4.7 par defaut,
    # non surcharge par les .env locaux (mesure du 2026-10-12). Si ce pin casse,
    # la comparaison porte sur un autre moteur que les traces maison.
    assert bench.HOUSE_MODEL == "anthropic/claude-opus-4.7"


def test_budget_matches_house_pass17(bench):
    assert bench.HOUSE_REASONING_BUDGET_S == 1800.0


def test_rung_statement_is_round_trip(bench):
    assert bench.RUNG_NAME == "CALIBRATION_CONWAY_LAS_ROUND_TRIP"
    # Identifiants qualifies : le REPL Pantograph ne charge pas le namespace
    # Conway (mesure du 2026-10-12, "Unknown identifier digitsToNat").
    assert bench.RUNG_STATEMENT == (
        "forall (n : Nat), Conway.digitsToNat (Conway.natToDigits n) = n"
    )


def test_protocol_gap_documents_toolchain_pin(bench):
    # L'ecart de protocole doit citer la toolchain EXACTE du wheel
    # (pantograph/lean-toolchain = v4.29.1, mesure du 2026-10-12), pas une
    # approximation : c'est ce qui rend le mini-lake reproductible.
    import inspect

    src = inspect.getsource(bench)
    assert "v4.29.1" in src
    assert "lean-toolchain" in src


def test_lake_lean_path_parses_full_printenv(bench, monkeypatch):
    # Bug mesure : `lake env printenv LEAN_PATH` rend VIDE sur lake 5.0.0 ;
    # seul `lake env printenv` integral porte LEAN_PATH. Le parseur doit
    # extraire la ligne exacte, pas la premiere ligne contenant "LEAN".
    fake = subprocess.CompletedProcess(
        args=[],
        returncode=0,
        stdout=(
            "DBUS_SESSION_BUS_ADDRESS=unix:path=/run/user/1000/bus\n"
            "LEAN_RECURSION_COUNT=1\n"
            "LEAN_PATH=/pkg/build/lib/lean:/proj/.lake/build/lib/lean:"
            "/toolchain/lib/lean\n"
            "LEAN_SRC_PATH=/pkg:/proj\n"
        ),
    )
    monkeypatch.setattr(subprocess, "run", lambda *a, **k: fake)
    assert bench.lake_lean_path("/proj") == (
        "/pkg/build/lib/lean:/proj/.lake/build/lib/lean:/toolchain/lib/lean"
    )


def test_lake_lean_path_missing_raises(bench, monkeypatch):
    fake = subprocess.CompletedProcess(
        args=[], returncode=0, stdout="PATH=/usr/bin\n"
    )
    monkeypatch.setattr(subprocess, "run", lambda *a, **k: fake)
    with pytest.raises(bench.ConfigError):
        bench.lake_lean_path("/proj")


def test_openrouter_key_missing_raises(bench, monkeypatch):
    monkeypatch.delenv("OPENROUTER_API_KEY", raising=False)
    with pytest.raises(bench.ConfigError):
        bench._openrouter_key()


def test_bench_result_shape(bench):
    r = bench.BenchResult(
        rung=bench.RUNG_NAME, mode="step_by_step",
        model=bench.HOUSE_MODEL, budget_s=1800.0, success=False,
    )
    d = r.__dataclass_fields__
    for key in (
        "llm_calls", "tactic_steps", "elapsed_s", "termination",
        "tactics_tried", "proof_mode_output",
    ):
        assert key in d, f"champ de mesure manquant: {key}"


def test_no_secrets_in_source():
    src = BENCH.read_text(encoding="utf-8")
    assert "sk-" not in src
    assert "OPENROUTER_API_KEY" in src  # lu de l'env, jamais en dur
    assert 'os.environ.get("OPENROUTER_API_KEY"' in src
