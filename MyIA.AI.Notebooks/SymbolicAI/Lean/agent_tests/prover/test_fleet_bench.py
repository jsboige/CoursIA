"""Contrats conservateurs du driver fleet; aucun appel de provider n'est lancé."""
import json
import sys
from pathlib import Path
from unittest.mock import patch

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent))
import fleet_bench


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
        stdout="[GATE] provider credentials missing\n[GATE] refusing to launch\n")
    with patch.object(fleet_bench.subprocess, "run", return_value=completed):
        arm = fleet_bench._launch_arm("baseline", 0, "local", 1, 1)
    assert arm["success"] is False
    assert arm["proof_success"] is False
    assert arm["error_code"] == "PROVIDER_UNCONFIGURED"


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
