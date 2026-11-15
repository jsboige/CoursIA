"""Contrats conservateurs du driver fleet; aucun appel de provider n'est lancé."""
import json
import os
import subprocess
import sys
from pathlib import Path
from unittest.mock import patch

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent))
import fleet_bench
sys.path.insert(0, str(fleet_bench.AGENT_TESTS_DIR))
import run_prover_bg as prover_launcher


def test_endpoint_requires_absolute_http_url():
    with pytest.raises(fleet_bench.BenchError, match="URL HTTP"):
        fleet_bench.validate_endpoint("connector.local/v1")


def test_endpoint_probe_fails_closed_on_http_error():
    with patch.object(fleet_bench, "urlopen", side_effect=fleet_bench.HTTPError(
            "http://localhost/v1/models", 401, "unauthorized", {}, None)):
        with pytest.raises(fleet_bench.BenchError, match="HTTP 401") as error:
            fleet_bench.probe_endpoint("http://localhost/v1", "secret", 0.1)
    assert error.value.code == "FLEET_ENDPOINT_UNREACHABLE"


def test_endpoint_probe_rejects_non_openai_payload():
    class Response:
        status = 200

        def __enter__(self):
            return self

        def __exit__(self, *_args):
            return False

        def read(self):
            return b'{"html":"not a models response"}'

    with patch.object(fleet_bench, "urlopen", return_value=Response()):
        with pytest.raises(fleet_bench.BenchError) as error:
            fleet_bench.probe_endpoint("http://localhost/v1", None, 0.1)
    assert error.value.code == "FLEET_ENDPOINT_UNREACHABLE"


def test_missing_trace_does_not_turn_unknown_usage_into_zero():
    assert fleet_bench._trace_metrics(None) == {
        "tokens": None, "routing": {}, "evidence": "indisponible"
    }


def test_trace_sums_only_explicit_usage_and_models(tmp_path):
    trace = tmp_path / "trace.json"
    trace.write_text(json.dumps([
        {"model": "route-a", "tokens": {"input": 4, "output": 3}},
        {"model": "route-a"},
        {"tokens": {"input": "4", "output": 1}},
    ]), encoding="utf-8")
    assert fleet_bench._trace_metrics(str(trace)) == {
        "tokens": {"input": 4, "output": 3, "total": 7},
        "routing": {"route-a": 2},
        "evidence": "trace_prover",
    }


def test_otel_metrics_records_observed_model_and_usage(tmp_path):
    spans = tmp_path / "spans.jsonl"
    spans.write_text(json.dumps({
        "attributes": {
            "gen_ai.request.model": "fleet-model-a",
            "gen_ai.usage.input_tokens": 8,
            "gen_ai.usage.output_tokens": 5,
        }
    }) + "\n", encoding="utf-8")
    metrics = fleet_bench._otel_metrics(f"[OTEL] spans -> {spans}\n")
    assert metrics == {
        "tokens": {"input": 8, "output": 5, "total": 13},
        "routing": {"fleet-model-a": 1},
        "evidence": "otel",
    }


def test_provider_gate_is_reported_as_unconfigured():
    completed = fleet_bench.subprocess.CompletedProcess(
        args=[], returncode=5,
        stdout="[BG] PROVIDER_GATE missing credentials\n"
        "[BG] PROVIDER_GATE refusing to launch\n[BG] EXIT code=5\n")
    with patch.object(fleet_bench.subprocess, "run", return_value=completed):
        arm = fleet_bench._launch_arm("baseline", 0, "local", 1, 1)
    assert arm["success"] is False
    assert arm["proof_success"] is False
    assert arm["error_code"] == "PROVIDER_UNCONFIGURED"


def test_unmaterialized_demo_target_cannot_be_reported_as_a_proof():
    completed = fleet_bench.subprocess.CompletedProcess(
        args=[], returncode=0,
        stdout="[BG] FILE  (no file — synthetic theorem demo)\n")
    with patch.object(fleet_bench.subprocess, "run", return_value=completed):
        arm = fleet_bench._launch_arm("baseline", 0, "local", 1, 10)
    assert arm["success"] is False
    assert arm["proof_success"] is False
    assert arm["error_code"] == "DEMO_TARGET_UNAVAILABLE"


def test_demo_config_requires_a_materialized_lean_file(tmp_path):
    lean_file = tmp_path / "Smoke.lean"
    lean_file.write_text("theorem smoke : True := trivial\n", encoding="utf-8")
    assert fleet_bench._demo_file(0, {0: {"file": str(lean_file)}}) == lean_file
    with pytest.raises(fleet_bench.BenchError) as error:
        fleet_bench._demo_file(0, {0: {"file": ""}})
    assert error.value.code == "DEMO_TARGET_UNAVAILABLE"


def test_arguments_match_real_outer_prover_parser(monkeypatch):
    command = fleet_bench._prover_command(0, "claudish", 2, 30, 12345)
    monkeypatch.setattr(sys, "argv", [command[2], *command[3:]])
    args = prover_launcher.parse_args()
    assert args.demo_id == 0
    assert args.provider == args.local_provider == "claudish"
    assert args.max_iter == 2
    assert args.workflow_timeout == 30
    assert args.coordinator_provider == args.tactic_provider == "claudish"
    assert args.search_provider == args.critic_provider == "claudish"
    assert args.diagnosis_provider == args.director_provider == "claudish"
    assert args.reuse_lock_pid == 12345
    assert set(prover_launcher._effective_agent_providers(args).values()) == {"claudish"}


def test_between_arms_and_finally_restore_exact_original_bytes(tmp_path):
    target = tmp_path / "target.lean"
    original = b"theorem original : True := by\n  sorry\n"
    target.write_bytes(original)
    seen_by_fleet = []

    def baseline():
        target.write_bytes(b"baseline mutation")
        return {"success": True}

    def fleet():
        seen_by_fleet.append(target.read_bytes())
        target.write_bytes(b"fleet mutation")
        raise RuntimeError("fleet arm failed")

    with pytest.raises(RuntimeError, match="fleet arm failed"):
        fleet_bench._run_arms_with_restore(target, baseline, fleet)
    assert seen_by_fleet == [original]
    assert target.read_bytes() == original


def test_runner_reuses_only_the_live_parent_tree_lock(tmp_path):
    from prover.tree_lock import acquire_tree_lock, release_tree_lock

    lock_path, _message = acquire_tree_lock(tmp_path, demo_id=0)
    assert lock_path is not None
    try:
        # Le détenteur vivant doit être le vrai parent du lanceur enfant,
        # pas seulement un PID connu copié depuis le fichier de verrou.
        assert not prover_launcher._parent_lock_is_valid(tmp_path, os.getpid())
        child = subprocess.run(
            [sys.executable, "-c",
             "import os,sys;from pathlib import Path;"
             "import run_prover_bg as r;"
             "sys.exit(0 if r._parent_lock_is_valid(Path(sys.argv[1]), os.getppid()) else 1)",
             str(tmp_path)],
            cwd=fleet_bench.AGENT_TESTS_DIR, capture_output=True, text=True,
            timeout=30,
        )
        assert child.returncode == 0, child.stdout + child.stderr
        assert not prover_launcher._parent_lock_is_valid(tmp_path, os.getpid() + 1)
    finally:
        release_tree_lock(lock_path)


def test_result_success_alone_does_not_claim_proof_without_zero_sorry(tmp_path):
    trace = tmp_path / "trace.json"
    trace.write_text("[]", encoding="utf-8")
    completed = fleet_bench.subprocess.CompletedProcess(
        args=[], returncode=0,
        stdout=(
            f"[OTEL] spans -> {tmp_path / 'spans.jsonl'}\n"
            f"Trace saved: {trace} (0 entries)\n"
            "[BG] PRE_FILE_SORRY_COUNT 1\n"
            "[BG] POST_FILE_SORRY_COUNT 1\n"
            "[BG] RESULT_SUCCESS True\n"
            "[BG] RESULT_ALREADY_SOLVED False\n"
            "[BG] RESULT_ITERATIONS 1\n"
            "[BG] FINAL ok=True kind=structural_only sorry_after=1 elapsed=2.0\n"
            "[BG] EXIT code=0\n"
        ))
    with patch.object(fleet_bench.subprocess, "run", return_value=completed):
        arm = fleet_bench._launch_arm("baseline", 0, "local", 1, 10)
    assert arm["build_verified"] is True
    assert arm["proof_success"] is False
    assert arm["success"] is False


def test_timeout_is_failure_without_proof_or_invented_measurements():
    with patch.object(fleet_bench.subprocess, "run",
                      side_effect=fleet_bench.subprocess.TimeoutExpired("runner", 1)):
        arm = fleet_bench._launch_arm("baseline", 0, "local", 1, 0.01)
    assert arm["error_code"] == "PROVER_TIMEOUT"
    assert arm["success"] is False
    assert arm["proof_success"] is False
    assert arm["tokens"] is None
    assert arm["actual_iterations"] is None


def test_output_inside_repository_is_rejected(tmp_path):
    repository = fleet_bench.PROVER_DIR.parents[4]
    with pytest.raises(fleet_bench.BenchError) as error:
        fleet_bench.write_outputs(repository / "comparison.json", {"arms": []})
    assert error.value.code == "OUTPUT_INSIDE_REPOSITORY"


def test_boolean_token_counts_are_not_integer_measurements(tmp_path):
    trace = tmp_path / "trace.json"
    trace.write_text(json.dumps([{"tokens": {"input": True, "output": 3}}]), encoding="utf-8")
    assert fleet_bench._trace_metrics(str(trace))["tokens"] is None
    spans = tmp_path / "spans.jsonl"
    spans.write_text(json.dumps({"attributes": {
        "gen_ai.usage.input_tokens": 2, "gen_ai.usage.output_tokens": False,
    }}) + "\n", encoding="utf-8")
    assert fleet_bench._otel_metrics(f"[OTEL] spans -> {spans}\n")["tokens"] is None


def test_routing_evidence_tracks_source_when_metrics_are_mixed(tmp_path):
    trace = tmp_path / "trace.json"
    trace.write_text(json.dumps([{"model": "route-trace"}]), encoding="utf-8")
    spans = tmp_path / "spans.jsonl"
    spans.write_text(json.dumps({"attributes": {
        "gen_ai.usage.input_tokens": 8, "gen_ai.usage.output_tokens": 5,
    }}) + "\n", encoding="utf-8")
    stdout = (f"[OTEL] spans -> {spans}\nTrace saved: {trace} (1 entries)\n"
              "[BG] PRE_FILE_SORRY_COUNT 1\n[BG] POST_FILE_SORRY_COUNT 0\n"
              "[BG] RESULT_SUCCESS True\n[BG] RESULT_ALREADY_SOLVED False\n"
              "[BG] RESULT_ITERATIONS 1\n"
              "[BG] FINAL ok=True kind=proved sorry_after=0 elapsed=2.0\n"
              "[BG] EXIT code=0\n")
    completed = subprocess.CompletedProcess(args=[], returncode=0, stdout=stdout)
    with patch.object(fleet_bench.subprocess, "run", return_value=completed):
        arm = fleet_bench._launch_arm("baseline", 0, "local", 1, 10)
    assert arm["tokens"] == {"input": 8, "output": 5, "total": 13}
    assert arm["routing"] == {"route-trace": 1}
    assert arm["routing_evidence"] == "trace_prover"


def test_zero_token_counts_remain_measured(tmp_path):
    trace = tmp_path / "trace.json"
    trace.write_text(json.dumps([{"tokens": {"input": 0, "output": 0}}]), encoding="utf-8")
    assert fleet_bench._trace_metrics(str(trace))["tokens"] == {
        "input": 0, "output": 0, "total": 0,
    }
    spans = tmp_path / "spans.jsonl"
    spans.write_text(json.dumps({"attributes": {
        "gen_ai.usage.input_tokens": 0, "gen_ai.usage.output_tokens": 0,
    }}) + "\n", encoding="utf-8")
    assert fleet_bench._otel_metrics(f"[OTEL] spans -> {spans}\n")["tokens"] == {
        "input": 0, "output": 0, "total": 0,
    }
