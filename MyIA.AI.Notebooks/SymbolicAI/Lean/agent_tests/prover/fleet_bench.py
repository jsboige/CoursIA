#!/usr/bin/env python3
"""Compare les runs du prouveur existant sur une baseline et l'endpoint fleet."""
from __future__ import annotations

import argparse
import csv
import json
import os
import re
import subprocess
import sys
import time
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path
from urllib.error import HTTPError, URLError
from urllib.parse import urlparse
from urllib.request import Request, urlopen

PROVER_DIR = Path(__file__).resolve().parent
RUNNER = PROVER_DIR / "run_prover_bg.py"
SUMMARY_RE = re.compile(r"^Summary:\s*(.+?)\s*$", re.MULTILINE)
OTEL_RE = re.compile(r"^\s*\[OTEL\] spans -> (.+?)\s*$", re.MULTILINE)


class BenchError(RuntimeError):
    def __init__(self, code: str, message: str):
        super().__init__(message)
        self.code = code


def validate_endpoint(endpoint: str) -> str:
    value = endpoint.strip()
    parsed = urlparse(value)
    if parsed.scheme not in {"http", "https"} or not parsed.netloc:
        raise BenchError("FLEET_ENDPOINT_INVALID", "L’endpoint doit être une URL HTTP(S) absolue.")
    return value.rstrip("/")


def probe_endpoint(endpoint: str, token: str | None, timeout_s: float) -> None:
    """Vérifie un GET /models OpenAI-compatible, sans exposer le jeton."""
    request = Request(validate_endpoint(endpoint) + "/models", method="GET",
                      headers={"Accept": "application/json",
                               **({"Authorization": f"Bearer {token}"} if token else {})})
    try:
        with urlopen(request, timeout=timeout_s) as response:
            payload = json.loads(response.read().decode("utf-8"))
            if not 200 <= response.status < 300 or not (
                    isinstance(payload, dict) and isinstance(payload.get("data"), list)):
                raise BenchError("FLEET_ENDPOINT_UNREACHABLE",
                                 "GET /models ne retourne pas un payload OpenAI-compatible.")
    except BenchError:
        raise
    except HTTPError as exc:
        raise BenchError("FLEET_ENDPOINT_UNREACHABLE", f"GET /models a retourné HTTP {exc.code}.") from exc
    except (URLError, TimeoutError, OSError, ValueError) as exc:
        raise BenchError("FLEET_ENDPOINT_UNREACHABLE",
                         f"GET /models a échoué ({type(exc).__name__}).") from exc


def _trace_metrics(path_value: str | None) -> dict:
    if not path_value:
        return {"tokens": None, "routing": {}, "evidence": "indisponible"}
    try:
        entries = json.loads(Path(path_value).read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {"tokens": None, "routing": {}, "evidence": "trace_illisible"}
    if not isinstance(entries, list):
        return {"tokens": None, "routing": {}, "evidence": "format_inattendu"}
    ins = outs = 0
    tokens_seen = False
    models: Counter[str] = Counter()
    for entry in entries:
        if not isinstance(entry, dict):
            continue
        model = entry.get("model")
        if isinstance(model, str) and model.strip():
            models[model.strip()] += 1
        usage = entry.get("tokens")
        if isinstance(usage, dict):
            i, o = usage.get("input"), usage.get("output")
            if isinstance(i, int) and i >= 0 and isinstance(o, int) and o >= 0:
                ins += i
                outs += o
                tokens_seen = True
    return {
        "tokens": {"input": ins, "output": outs, "total": ins + outs} if tokens_seen else None,
        "routing": dict(sorted(models.items())),
        "evidence": "trace_prover" if tokens_seen or models else "trace_sans_metriques",
    }


def _otel_metrics(stdout: str) -> dict:
    """Agrège les spans disponibles; un modèle absent reste non observé."""
    match = OTEL_RE.search(stdout)
    if not match:
        return {"tokens": None, "routing": {}, "evidence": "otel_indisponible"}
    models: Counter[str] = Counter()
    ins = outs = 0
    usage_seen = False
    try:
        with Path(match.group(1).strip()).open(encoding="utf-8") as stream:
            for line in stream:
                try:
                    span = json.loads(line)
                except json.JSONDecodeError:
                    continue
                attributes = span.get("attributes", {}) if isinstance(span, dict) else {}
                if not isinstance(attributes, dict):
                    continue
                model = attributes.get("gen_ai.request.model") or attributes.get("gen_ai.response.model")
                if isinstance(model, str) and model.strip():
                    models[model.strip()] += 1
                i = attributes.get("gen_ai.usage.input_tokens")
                o = attributes.get("gen_ai.usage.output_tokens")
                if isinstance(i, int) and i >= 0 and isinstance(o, int) and o >= 0:
                    ins += i
                    outs += o
                    usage_seen = True
    except OSError:
        return {"tokens": None, "routing": {}, "evidence": "otel_illisible"}
    return {
        "tokens": {"input": ins, "output": outs, "total": ins + outs} if usage_seen else None,
        "routing": dict(sorted(models.items())),
        "evidence": "otel" if usage_seen or models else "otel_sans_metriques",
    }


def _launch_arm(arm: str, demo_id: int, provider: str, iterations: int,
                timeout_s: float, endpoint: str | None = None,
                token: str | None = None) -> dict:
    env = os.environ.copy()
    roles = ["--provider", provider, "--local-provider", provider,
             "--coordinator-provider", provider, "--tactic-provider", provider,
             "--search-provider", provider, "--critic-provider", provider]
    if arm == "fleet":
        provider = "claudish"
        for index in (1, 3, 5, 7, 9, 11):
            roles[index] = provider
        env["CLAUDISH_BASE_URL"] = endpoint or ""
        env["CLAUDISH_PROXY_KEY"] = token or ""
    command = [sys.executable, "-u", str(RUNNER), "--demo", str(demo_id),
               "--mode", "multi", "--iterations", str(iterations), *roles]
    started = time.monotonic()
    try:
        completed = subprocess.run(command, cwd=PROVER_DIR.parent, env=env,
                                   text=True, stdout=subprocess.PIPE,
                                   stderr=subprocess.STDOUT, timeout=timeout_s,
                                   check=False)
    except subprocess.TimeoutExpired:
        return {"arm": arm, "provider": provider, "status": "timeout",
                "success": False, "error_code": "PROVER_TIMEOUT",
                "elapsed_s": round(time.monotonic() - started, 3),
                "iterations_budget": iterations, "actual_iterations": None,
                "proof_success": False, "original_sorry": None,
                "final_sorry": None, "tokens": None, "routing": {}}
    elapsed = time.monotonic() - started
    match = SUMMARY_RE.search(completed.stdout)
    summary = None
    if match:
        try:
            loaded = json.loads(Path(match.group(1)).read_text(encoding="utf-8"))
            summary = loaded if isinstance(loaded, dict) else None
        except (OSError, json.JSONDecodeError):
            pass
    if summary is None:
        diagnostic = completed.stdout[-2000:]
        error_code = ("PROVIDER_UNCONFIGURED" if "[GATE] refusing to launch" in completed.stdout
                      else "PROVER_TREE_LOCKED" if "[LOCKED]" in completed.stdout
                      else "PROVER_RESULT_MISSING")
        return {"arm": arm, "provider": provider, "status": "runner_error",
                "success": False, "error_code": error_code,
                "elapsed_s": round(elapsed, 3), "iterations_budget": iterations,
                "actual_iterations": None, "proof_success": False,
                "original_sorry": None, "final_sorry": None, "tokens": None,
                "routing": {}, "diagnostic": diagnostic}
    result = summary.get("result")
    provider_gate = summary.get("result_kind") == "provider_gate"
    proof_success = (isinstance(result, dict) and result.get("success") is True
                     and summary.get("final_sorry") == 0)
    trace_metrics = _trace_metrics(summary.get("trace_file"))
    otel_metrics = _otel_metrics(completed.stdout)
    metrics = {
        "tokens": otel_metrics["tokens"] or trace_metrics["tokens"],
        "routing": otel_metrics["routing"] or trace_metrics["routing"],
        "evidence": otel_metrics["evidence"] if (
            otel_metrics["routing"] or otel_metrics["tokens"]) else trace_metrics["evidence"],
    }
    return {
        "arm": arm, "provider": provider,
        "status": "completed" if completed.returncode == 0 else "runner_error",
        "success": completed.returncode == 0 and proof_success,
        "error_code": ("PROVIDER_UNCONFIGURED" if provider_gate else
                       None if completed.returncode == 0 else "PROVER_FAILED"),
        "elapsed_s": round(elapsed, 3), "iterations_budget": iterations,
        "actual_iterations": summary.get("actual_iterations"),
        "proof_success": proof_success, "result_kind": summary.get("result_kind"),
        "original_sorry": summary.get("original_sorry"),
        "final_sorry": summary.get("final_sorry"), "tokens": metrics["tokens"],
        "cost_usd": None,
        "routing": metrics["routing"], "routing_evidence": metrics["evidence"],
        "summary_file": match.group(1).strip(), "returncode": completed.returncode,
        "diagnostic": (result.get("reason") if provider_gate and isinstance(result, dict) else None),
    }


def write_outputs(path: Path, payload: dict) -> tuple[Path, Path]:
    path = path.expanduser().resolve()
    repo = PROVER_DIR.parents[4].resolve()
    if path == repo or repo in path.parents:
        raise BenchError("OUTPUT_INSIDE_REPOSITORY", "Les résultats doivent rester hors du dépôt.")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    csv_path = path.with_suffix(".csv")
    columns = ["arm", "provider", "status", "success", "elapsed_s",
               "iterations_budget", "actual_iterations", "proof_success",
               "original_sorry", "final_sorry", "cost_usd", "input_tokens",
               "output_tokens", "total_tokens", "routing", "error_code"]
    with csv_path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=columns)
        writer.writeheader()
        for arm in payload.get("arms", []):
            tokens = arm.get("tokens") or {}
            writer.writerow({
                **{key: arm.get(key) for key in columns if key not in {
                    "input_tokens", "output_tokens", "total_tokens", "routing"}},
                "input_tokens": tokens.get("input"), "output_tokens": tokens.get("output"),
                "total_tokens": tokens.get("total"),
                "routing": json.dumps(arm.get("routing", {}), ensure_ascii=False, sort_keys=True),
            })
    return path, csv_path


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Compare un DEMO Lean sur baseline et endpoint fleet.")
    parser.add_argument("demo_id", type=int)
    parser.add_argument("--endpoint", required=True)
    parser.add_argument("--token-env", help="Variable contenant le jeton fleet")
    parser.add_argument("--baseline-provider", required=True,
                        choices=("local", "zai", "openrouter"))
    parser.add_argument("--iterations", type=int, default=3)
    parser.add_argument("--timeout-s", type=float, default=900.0)
    parser.add_argument("--probe-timeout-s", type=float, default=5.0)
    parser.add_argument("--output", type=Path, default=Path("/tmp/fleet-bench") /
                        f"comparison-{datetime.now(timezone.utc):%Y%m%dT%H%M%SZ}.json")
    return parser


def main(argv: list[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    if args.iterations < 1 or args.timeout_s <= 0 or args.probe_timeout_s <= 0:
        print("FLEET_BENCH_ARGUMENT_INVALID: budgets et timeouts doivent être positifs.", file=sys.stderr)
        return 2
    try:
        endpoint = validate_endpoint(args.endpoint)
    except BenchError as exc:
        print(f"{exc.code}: {exc}", file=sys.stderr)
        return 2
    token = os.environ.get(args.token_env) if args.token_env else None
    if args.token_env and not token:
        print(f"FLEET_TOKEN_ENV_MISSING: variable {args.token_env} absente ou vide.", file=sys.stderr)
        return 2
    payload = {
        "schema_version": 1, "issue": 24581,
        "created_at": datetime.now(timezone.utc).isoformat(),
        "demo_id": args.demo_id, "endpoint": endpoint,
        "baseline_provider": args.baseline_provider,
        "iteration_budget": args.iterations, "timeout_s_per_arm": args.timeout_s,
        "seed": {"value": None, "applied": False,
                 "limitation": "Le lanceur existant n’expose pas de seed de génération."},
        "arms": [], "comparison": {"status": "incomplete"},
    }
    try:
        # Baseline d'abord : un endpoint absent produit tout de même un rapport
        # partiel avec la mesure baseline si son backend est disponible.
        baseline = _launch_arm("baseline", args.demo_id, args.baseline_provider,
                               args.iterations, args.timeout_s)
        payload["arms"].append(baseline)
        if not baseline["success"]:
            diagnostic = baseline.get("diagnostic")
            message = "La baseline n’a pas fourni une preuve vérifiée."
            if diagnostic:
                message += f" Diagnostic: {diagnostic}"
            raise BenchError(baseline.get("error_code") or "BASELINE_FAILED", message)
        probe_endpoint(endpoint, token, args.probe_timeout_s)
        fleet = _launch_arm("fleet", args.demo_id, "claudish", args.iterations,
                            args.timeout_s, endpoint, token)
        payload["arms"].append(fleet)
        payload["comparison"] = {
            "status": "measured" if fleet["success"] else "inconclusive",
            "same_demo": True, "same_iteration_budget": True,
            "same_seed_applied": False,
            "proof_parity": baseline["proof_success"] == fleet["proof_success"],
            "latency_delta_s_fleet_minus_baseline": round(
                fleet["elapsed_s"] - baseline["elapsed_s"], 3),
            "latency_improved": fleet["elapsed_s"] < baseline["elapsed_s"],
            "cost_delta_usd_fleet_minus_baseline": None,
            "cost_limitation": "Le harnais ne fournit pas de coût vérifiable.",
        }
        if not fleet["success"]:
            diagnostic = fleet.get("diagnostic")
            message = "Le bras fleet n’a pas fourni une preuve vérifiée."
            if diagnostic:
                message += f" Diagnostic: {diagnostic}"
            raise BenchError(fleet.get("error_code") or "FLEET_RUN_FAILED", message)
    except BenchError as exc:
        payload["error"] = {"code": exc.code, "message": str(exc)}
        try:
            json_path, csv_path = write_outputs(args.output, payload)
        except BenchError as output_error:
            print(f"{output_error.code}: {output_error}", file=sys.stderr)
            return 2
        print(f"{exc.code}: {exc}", file=sys.stderr)
        print(f"Comparaison partielle: {json_path} ; {csv_path}", file=sys.stderr)
        return 1
    try:
        json_path, csv_path = write_outputs(args.output, payload)
    except BenchError as exc:
        print(f"{exc.code}: {exc}", file=sys.stderr)
        return 2
    print(f"Comparaison: {json_path}\nCSV: {csv_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
