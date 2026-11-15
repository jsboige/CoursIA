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
AGENT_TESTS_DIR = PROVER_DIR.parent
RUNNER = AGENT_TESTS_DIR / "run_prover_bg.py"
OTEL_RE = re.compile(r"^\s*\[OTEL\] spans -> (.+?)\s*$", re.MULTILINE)
TRACE_RE = re.compile(r"^Trace saved:\s*(.+?)\s+\(\d+ entries\)\s*$", re.MULTILINE)
RESULT_RE = re.compile(r"^\[BG\] RESULT_SUCCESS (True|False)\s*$", re.MULTILINE)
ALREADY_RE = re.compile(r"^\[BG\] RESULT_ALREADY_SOLVED (True|False)\s*$", re.MULTILINE)
PRE_SORRY_RE = re.compile(r"^\[BG\] PRE_FILE_SORRY_COUNT (-?\d+)\s*$", re.MULTILINE)
POST_SORRY_RE = re.compile(r"^\[BG\] POST_FILE_SORRY_COUNT (-?\d+)\s*$", re.MULTILINE)
ITERATIONS_RE = re.compile(r"^\[BG\] RESULT_ITERATIONS (None|\d+)\s*$", re.MULTILINE)
FINAL_RE = re.compile(
    r"^\[BG\] FINAL ok=(True|False) kind=([^\s]+) "
    r"sorry_after=([^\s]+) elapsed=([0-9.]+)\s*$",
    re.MULTILINE,
)
EXIT_RE = re.compile(r"^\[BG\] EXIT code=(\d+)\s*$", re.MULTILINE)
FILE_RE = re.compile(r"^\[BG\] FILE\s+(.+?)\s*$", re.MULTILINE)


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
            if type(i) is int and i >= 0 and type(o) is int and o >= 0:
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
                if type(i) is int and i >= 0 and type(o) is int and o >= 0:
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


def _prover_command(demo_id: int, provider: str, iterations: int,
                    workflow_timeout_s: int,
                    lock_owner_pid: int | None = None) -> list[str]:
    """Construit la commande du lanceur racine, dont la CLI est positional."""
    return [
        sys.executable, "-u", str(RUNNER), str(demo_id),
        "--max-iter", str(iterations),
        "--workflow-timeout", str(workflow_timeout_s),
        "--provider", provider, "--local-provider", provider,
        "--coordinator-provider", provider, "--tactic-provider", provider,
        "--search-provider", provider, "--critic-provider", provider,
        "--diagnosis-provider", provider, "--director-provider", provider,
        *(["--reuse-lock-pid", str(lock_owner_pid)]
          if lock_owner_pid is not None else []),
    ]


def _demo_file(demo_id: int, demos: dict) -> Path:
    demo = demos.get(demo_id)
    file_value = demo.get("file") if isinstance(demo, dict) else None
    if not isinstance(file_value, str) or not file_value.strip():
        raise BenchError("DEMO_TARGET_UNAVAILABLE",
                         f"DEMO {demo_id} ne référence aucun fichier Lean.")
    path = Path(file_value).expanduser().resolve()
    if not path.is_file():
        raise BenchError("DEMO_TARGET_UNAVAILABLE",
                         f"Le fichier Lean du DEMO {demo_id} n’est pas matérialisé: {path}.")
    return path


def _validate_demo_target(demo_id: int) -> Path:
    """Charge la config réelle pour refuser un DEMO sparse avant tout appel LLM."""
    if str(AGENT_TESTS_DIR) not in sys.path:
        sys.path.insert(0, str(AGENT_TESTS_DIR))
    try:
        from prover.config import DEMOS
    except Exception as exc:
        raise BenchError("PROVER_BACKEND_IMPORT_FAILED",
                         f"Import de la configuration prouveur impossible ({type(exc).__name__}).") from exc
    return _demo_file(demo_id, DEMOS)


def _run_arms_with_restore(target: Path, run_baseline, run_fleet) -> tuple[dict, dict]:
    """Relance le second bras depuis les bytes d’origine et restaure toujours."""
    original = target.read_bytes()
    try:
        baseline = run_baseline()
        target.write_bytes(original)
        fleet = run_fleet()
        return baseline, fleet
    finally:
        target.write_bytes(original)


def _execute_comparison(args, endpoint: str, token: str | None,
                        payload: dict) -> None:
    target = _validate_demo_target(args.demo_id)
    if str(AGENT_TESTS_DIR) not in sys.path:
        sys.path.insert(0, str(AGENT_TESTS_DIR))
    from prover.tree_lock import (
        acquire_tree_lock, find_lean_project_root, release_tree_lock,
    )
    tree_root = find_lean_project_root(target)
    if tree_root is None:
        raise BenchError("DEMO_PROJECT_UNAVAILABLE",
                         f"Aucun projet Lean ne contient {target}.")
    lock_path, lock_message = acquire_tree_lock(tree_root, args.demo_id)
    if lock_path is None:
        raise BenchError("PROVER_TREE_LOCKED", lock_message)
    try:
        def baseline_run():
            result = _launch_arm(
                "baseline", args.demo_id, args.baseline_provider,
                args.iterations, args.timeout_s, lock_owner_pid=os.getpid(),
            )
            payload["arms"].append(result)
            if not result["success"]:
                diagnostic = result.get("diagnostic")
                message = "La baseline n’a pas fourni une preuve vérifiée."
                if diagnostic:
                    message += f" Diagnostic: {diagnostic}"
                raise BenchError(result.get("error_code") or "BASELINE_FAILED", message)
            return result

        def fleet_run():
            probe_endpoint(endpoint, token, args.probe_timeout_s)
            result = _launch_arm(
                "fleet", args.demo_id, "claudish", args.iterations,
                args.timeout_s, endpoint, token, lock_owner_pid=os.getpid(),
            )
            payload["arms"].append(result)
            return result

        baseline, fleet = _run_arms_with_restore(target, baseline_run, fleet_run)
        payload["comparison"] = {
            "status": "measured" if fleet["success"] else "inconclusive",
            "same_demo": True, "same_iteration_budget": True,
            "same_seed_applied": False,
            "same_original_file_bytes": True,
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
    finally:
        # The canonical prover lock remains held while bytes are restored.
        release_tree_lock(lock_path)


def _launch_arm(arm: str, demo_id: int, provider: str, iterations: int,
                timeout_s: float, endpoint: str | None = None,
                token: str | None = None,
                lock_owner_pid: int | None = None) -> dict:
    env = os.environ.copy()
    if arm == "fleet":
        provider = "claudish"
        env["CLAUDISH_BASE_URL"] = endpoint or ""
        env["CLAUDISH_PROXY_KEY"] = token or ""
    command = _prover_command(demo_id, provider, iterations, int(timeout_s),
                              lock_owner_pid)
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
    stdout = completed.stdout
    gate = "PROVIDER_GATE refusing to launch" in stdout
    lock = "[BG] LOCKED " in stdout
    exit_match = EXIT_RE.search(stdout)
    if gate:
        return {"arm": arm, "provider": provider, "status": "runner_error",
                "success": False, "error_code": "PROVIDER_UNCONFIGURED",
                "elapsed_s": round(elapsed, 3), "iterations_budget": iterations,
                "actual_iterations": None, "proof_success": False,
                "original_sorry": None, "final_sorry": None, "tokens": None,
                "routing": {}, "diagnostic": stdout[-2000:]}
    file_match = FILE_RE.search(stdout)
    if file_match and "no file" in file_match.group(1).lower():
        return {"arm": arm, "provider": provider, "status": "runner_error",
                "success": False, "error_code": "DEMO_TARGET_UNAVAILABLE",
                "elapsed_s": round(elapsed, 3), "iterations_budget": iterations,
                "actual_iterations": None, "proof_success": False,
                "original_sorry": None, "final_sorry": None, "tokens": None,
                "routing": {}, "diagnostic": file_match.group(1)}
    if not (FINAL_RE.search(stdout) and exit_match and int(exit_match.group(1)) == 0):
        diagnostic = completed.stdout[-2000:]
        error_code = ("PROVIDER_UNCONFIGURED" if gate else
                      "PROVER_TREE_LOCKED" if lock else
                      "PROVER_FAILED")
        return {"arm": arm, "provider": provider, "status": "runner_error",
                "success": False, "error_code": error_code,
                "elapsed_s": round(elapsed, 3), "iterations_budget": iterations,
                "actual_iterations": None, "proof_success": False,
                "original_sorry": None, "final_sorry": None, "tokens": None,
                "routing": {}, "diagnostic": diagnostic}
    final_match = FINAL_RE.search(stdout)
    success_match = RESULT_RE.search(stdout)
    already_match = ALREADY_RE.search(stdout)
    pre_match = PRE_SORRY_RE.search(stdout)
    post_match = POST_SORRY_RE.search(stdout)
    iterations_match = ITERATIONS_RE.search(stdout)
    if not (success_match and already_match and pre_match and post_match and final_match):
        return {"arm": arm, "provider": provider, "status": "runner_error",
                "success": False, "error_code": "PROVER_RESULT_INCOMPLETE",
                "elapsed_s": round(elapsed, 3), "iterations_budget": iterations,
                "actual_iterations": None, "proof_success": False,
                "original_sorry": None, "final_sorry": None, "tokens": None,
                "routing": {}, "diagnostic": stdout[-2000:]}
    backend_success = success_match.group(1) == "True"
    final_success = final_match.group(1) == "True"
    already_solved = already_match.group(1) == "True"
    original_sorry = int(pre_match.group(1))
    final_sorry = int(post_match.group(1))
    if (backend_success != final_success
            or final_match.group(3) != str(final_sorry)
            or original_sorry < 0 or final_sorry < 0):
        return {"arm": arm, "provider": provider, "status": "runner_error",
                "success": False, "error_code": "PROVER_RESULT_INCONSISTENT",
                "elapsed_s": round(elapsed, 3), "iterations_budget": iterations,
                "actual_iterations": None, "proof_success": False,
                "original_sorry": None, "final_sorry": None, "tokens": None,
                "routing": {}, "diagnostic": stdout[-2000:]}
    # MultiAgentSorryProver.success is only true after its mandatory final
    # verification build (provers.py final_build_ok gate). A proof also has to
    # eliminate a real pre-run sorry in the target; already-solved/structural
    # outcomes are not proof successes for this comparison.
    proof_success = (backend_success and original_sorry > final_sorry
                     and final_sorry == 0 and not already_solved)
    trace_match = TRACE_RE.search(stdout)
    trace_metrics = _trace_metrics(trace_match.group(1) if trace_match else None)
    otel_metrics = _otel_metrics(stdout)
    metrics = {
        "tokens": otel_metrics["tokens"] or trace_metrics["tokens"],
        "routing": otel_metrics["routing"] or trace_metrics["routing"],
        "evidence": (otel_metrics["evidence"] if otel_metrics["routing"]
                     else trace_metrics["evidence"]),
    }
    return {
        "arm": arm, "provider": provider,
        "status": "completed" if completed.returncode == 0 else "runner_error",
        "success": completed.returncode == 0 and proof_success,
        "error_code": None if completed.returncode == 0 and proof_success else "PROOF_NOT_VERIFIED",
        "elapsed_s": round(elapsed, 3), "iterations_budget": iterations,
        "prover_elapsed_s": float(final_match.group(4)),
        "actual_iterations": (int(iterations_match.group(1))
                              if iterations_match and iterations_match.group(1) != "None" else None),
        "proof_success": proof_success, "build_verified": backend_success,
        "result_kind": final_match.group(2),
        "original_sorry": original_sorry,
        "final_sorry": final_sorry, "tokens": metrics["tokens"],
        "cost_usd": None,
        "routing": metrics["routing"], "routing_evidence": metrics["evidence"],
        "trace_file": trace_match.group(1).strip() if trace_match else None,
        "otel_file": (OTEL_RE.search(stdout).group(1).strip()
                      if OTEL_RE.search(stdout) else None),
        "returncode": completed.returncode,
        "diagnostic": None if proof_success else stdout[-2000:],
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
        _execute_comparison(args, endpoint, token, payload)
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
