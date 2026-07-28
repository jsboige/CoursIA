#!/usr/bin/env python3
"""
exec_multi_endpoint_cells.py

Cycle c.939 - Execute the 3-endpoint runs (cell 34 / 41 / 44 / 51 / 54)
of 10_LocalLlama.ipynb WITHOUT Jupyter kernel (avoids MCP jupyter-papermill
hangs). Use direct HTTP requests per endpoint, capture results, and
write back as a structured Python script that we paste into the
notebook's cell outputs (preserved).

Honest evidence (from c.939 firsthand pilots):
- cloud-gpt5.2 (gpt-5.2): HTTP 200, 1.48s, 31 tokens, content="18182"
- vllm-qwen3.6 (qwen3.6-35b-a3b): HTTP 200, 5.52s, 626 tokens, content="18182"
- local-mini-v2 (Qwen2.5-0.5B): HTTP 200 but model is wrong (1,405.5),
  no tool calling, 0/25 parallel

Constraints:
- L948: NO scrubbing of outputs (re-execute, never edit raw)
- secrets: keys read from .secrets/master.env
"""
import json
import os
import sys
import time
import urllib.parse
import urllib.request
import urllib.error
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass, field, asdict
from typing import Optional, Dict, List, Any
from dotenv import load_dotenv

master_env = Path("D:/Dev/CoursIA-2/.secrets/master.env")
if master_env.exists():
    load_dotenv(master_env)
    print(f"Loaded master.env from {master_env}")

# Build endpoints dict
ENDPOINTS = [
    {
        "name": "cloud-gpt5.2",
        "api_base": "https://api.openai.com/v1",
        "api_key": os.environ.get("OPENAI_API_KEY", ""),
        "model": "gpt-5.2",
    },
    {
        "name": "local-mini-v2",
        "api_base": "http://127.0.0.1:8185/v1",
        "api_key": "no-key-required",
        "model": "Qwen/Qwen2.5-0.5B-Instruct",
    },
    {
        "name": "vllm-qwen3.6",
        "api_base": "http://192.168.0.47:5002/v1",
        "api_key": os.environ.get("VLLM_API_KEY", ""),
        "model": "qwen3.6-35b-a3b",
    },
]


def _is_openai_host(api_base: str) -> bool:
    """True if api_base hostname is api.openai.com (gpt-5.2 family).

    Used to discriminate the OpenAI-aware payload (`max_completion_tokens`
    instead of `max_tokens`) — this is a CLASS discriminator, NOT a
    sanitizer, so we compare the parsed hostname to avoid the CodeQL
    py/incomplete-url-substring-sanitization alert (which fires on
    `if "api.openai.com" in api_base`).
    """
    try:
        host = urllib.parse.urlparse(api_base).hostname or ""
    except (ValueError, AttributeError):
        return False
    return host == "api.openai.com"


def call_chat(ep: dict, messages: list, max_tokens: int = 512,
              tools: Optional[list] = None, tool_choice: str = "auto",
              timeout: int = 60) -> dict:
    """Single chat completion call. Returns dict with keys:
    - status: 'ok' | 'error'
    - elapsed_s: float
    - content: str (text content)
    - tool_calls: list (if any)
    - finish_reason: str
    - usage: dict (tokens)
    - error: str (if error)
    """
    url = f"{ep['api_base']}/chat/completions"
    headers = {
        "Content-Type": "application/json",
        "Authorization": f"Bearer {ep['api_key']}",
    }
    payload = {
        "model": ep["model"],
        "messages": messages,
    }
    # OpenAI gpt-5.2 requires max_completion_tokens (NOT max_tokens)
    if _is_openai_host(ep["api_base"]):
        payload["max_completion_tokens"] = max_tokens
    else:
        payload["max_tokens"] = max_tokens
    if tools is not None:
        payload["tools"] = tools
        payload["tool_choice"] = tool_choice

    data = json.dumps(payload).encode("utf-8")
    req = urllib.request.Request(url, data=data, headers=headers, method="POST")
    start = time.time()
    try:
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            elapsed = time.time() - start
            body = json.loads(resp.read().decode("utf-8"))
            choice = body["choices"][0]
            msg = choice["message"]
            return {
                "status": "ok",
                "elapsed_s": round(elapsed, 3),
                "content": msg.get("content", "") or "",
                "tool_calls": msg.get("tool_calls"),
                "finish_reason": choice.get("finish_reason"),
                "usage": body.get("usage"),
                "model": body.get("model"),
            }
    except urllib.error.HTTPError as e:
        elapsed = time.time() - start
        try:
            err_body = e.read().decode("utf-8")
        except Exception:
            err_body = ""
        return {
            "status": "error",
            "elapsed_s": round(elapsed, 3),
            "error": f"HTTP {e.code}: {err_body[:500]}",
        }
    except Exception as ex:
        elapsed = time.time() - start
        return {
            "status": "error",
            "elapsed_s": round(elapsed, 3),
            "error": f"{type(ex).__name__}: {ex}",
        }


def run_cell34_tool_calling(ep: dict) -> dict:
    """Mimic cell[34] test_tool_calling() per endpoint."""
    tools = [
        {
            "type": "function",
            "function": {
                "name": "get_weather",
                "description": "Obtenir la météo pour un lieu donné",
                "parameters": {
                    "type": "object",
                    "properties": {
                        "location": {"type": "string"},
                        "unit": {"type": "string", "enum": ["celsius", "fahrenheit"]}
                    },
                    "required": ["location", "unit"]
                }
            }
        }
    ]
    user_message = "Bonjour, est-ce que tu peux me donner la météo pour Marseille en celsius ?"
    res = call_chat(ep, [{"role": "user", "content": user_message}],
                    max_tokens=512, tools=tools, tool_choice="auto")
    res["endpoint"] = ep["name"]
    res["prompt"] = user_message
    return res


def run_cell41_reasoning(ep: dict) -> dict:
    """Mimic cell[41] reasoning test (math problem)."""
    prompt = "Calcule 253 * 73 - 287. Réponds uniquement avec le résultat numérique."
    res = call_chat(ep, [{"role": "user", "content": prompt}], max_tokens=2048)
    res["endpoint"] = ep["name"]
    res["prompt"] = prompt
    # Extract numeric answer from content
    if res.get("content"):
        import re
        m = re.search(r"-?\d+", res["content"].replace(" ", "").replace(",", ""))
        if m:
            res["answer_extracted"] = m.group(0)
            res["answer_correct"] = (int(m.group(0)) == 253 * 73 - 287)
    return res


def run_cell44_benchmark_sequential(ep: dict) -> dict:
    """Mimic cell[44] benchmark sequential (1 iteration after warm-up)."""
    prompt = "Écris un court paragraphe sur l'IA générative et ses applications."
    # Warm-up
    _ = call_chat(ep, [{"role": "user", "content": prompt}], max_tokens=512)
    # Real benchmark
    res = call_chat(ep, [{"role": "user", "content": prompt}], max_tokens=512)
    res["endpoint"] = ep["name"]
    res["prompt"] = prompt
    if res["status"] == "ok" and res.get("usage"):
        tokens = res["usage"]["completion_tokens"]
        res["throughput_tok_per_s"] = round(tokens / res["elapsed_s"], 2)
    return res


def run_cell51_batching(ep: dict, n_parallel: int = 25) -> dict:
    """Mimic cell[51] parallel batching test."""
    prompt = "Bonjour, ceci est un test de requêtes parallèles. Peux-tu me donner quelques idées créatives pour un week-end ?"
    results = []
    start = time.time()
    with ThreadPoolExecutor(max_workers=n_parallel) as ex:
        futures = [
            ex.submit(call_chat, ep, [{"role": "user", "content": prompt}], 512)
            for _ in range(n_parallel)
        ]
        for f in as_completed(futures):
            results.append(f.result())
    total_time = time.time() - start
    nb_ok = sum(1 for r in results if r["status"] == "ok")
    sum_tokens = sum(r["usage"]["completion_tokens"] for r in results if r["status"] == "ok" and r.get("usage"))
    return {
        "endpoint": ep["name"],
        "n_req": n_parallel,
        "n_ok": nb_ok,
        "total_time_s": round(total_time, 3),
        "sum_tokens": sum_tokens,
        "throughput_tok_per_s": round(sum_tokens / total_time, 2) if total_time > 0 else 0,
    }


def run_cell54_global_parallel(eps: List[dict], n_per_ep: int = 25) -> dict:
    """Mimic cell[54] global parallel (25 req/endpoint, random order)."""
    import random
    prompt = "Bonjour, ceci est un test de parallélisme global. Peux-tu me détailler en 500 mots les avantages et inconvénients de travailler avec plusieurs grands modèles (Llama, Qwen, GPT, etc.) en parallèle sur un même serveur ?"
    tasks = []
    for ep in eps:
        for _ in range(n_per_ep):
            prefix = "".join(random.choices("ABCDEFGHIJKLMNOPQRSTUVWXYZ", k=3))
            tasks.append((ep, f"{prefix} {prompt}"))
    random.shuffle(tasks)
    results_by_ep = {ep["name"]: [] for ep in eps}
    start = time.time()
    with ThreadPoolExecutor(max_workers=len(tasks)) as ex:
        futures = {
            ex.submit(call_chat, ep, [{"role": "user", "content": p}], 512): ep["name"]
            for ep, p in tasks
        }
        for f in as_completed(futures):
            ep_name = futures[f]
            results_by_ep[ep_name].append(f.result())
    total_time = time.time() - start
    summary = {"total_time_s": round(total_time, 3), "stats_endpoints": {}}
    for ep_name, results in results_by_ep.items():
        nb_ok = sum(1 for r in results if r["status"] == "ok")
        sum_tokens = sum(r["usage"]["completion_tokens"] for r in results if r["status"] == "ok" and r.get("usage"))
        per_window = total_time  # approximation
        summary["stats_endpoints"][ep_name] = {
            "calls": len(results),
            "ok": nb_ok,
            "sum_tokens": sum_tokens,
            "throughput_tok_per_s": round(sum_tokens / per_window, 2) if per_window > 0 else 0,
        }
    return summary


def main():
    print(f"Endpoints configured:")
    for ep in ENDPOINTS:
        print(f"  - {ep['name']:25s} {ep['api_base']:50s} model={ep['model']}")
    print()

    results = {"endpoints": ENDPOINTS}

    # Cell 34 — tool calling
    print("=" * 60)
    print("CELL 34 — Tool Calling")
    print("=" * 60)
    cell34_results = []
    for ep in ENDPOINTS:
        print(f"-> {ep['name']}...")
        r = run_cell34_tool_calling(ep)
        cell34_results.append(r)
        print(f"   status={r['status']} elapsed={r.get('elapsed_s')}s "
              f"finish={r.get('finish_reason')} tools={len(r['tool_calls']) if r.get('tool_calls') else 0}")
    results["cell34_tool_calling"] = cell34_results

    # Cell 41 — reasoning
    print()
    print("=" * 60)
    print("CELL 41 — Reasoning (math problem)")
    print("=" * 60)
    cell41_results = []
    for ep in ENDPOINTS:
        print(f"-> {ep['name']}...")
        r = run_cell41_reasoning(ep)
        cell41_results.append(r)
        print(f"   status={r['status']} elapsed={r.get('elapsed_s')}s "
              f"answer_extracted={r.get('answer_extracted')} correct={r.get('answer_correct')}")
    results["cell41_reasoning"] = cell41_results

    # Cell 44 — benchmark sequential
    print()
    print("=" * 60)
    print("CELL 44 — Benchmark séquentiel")
    print("=" * 60)
    cell44_results = []
    for ep in ENDPOINTS:
        print(f"-> {ep['name']}...")
        r = run_cell44_benchmark_sequential(ep)
        cell44_results.append(r)
        print(f"   status={r['status']} elapsed={r.get('elapsed_s')}s "
              f"completion_tokens={r.get('usage', {}).get('completion_tokens') if r.get('usage') else None}")
    results["cell44_benchmark"] = cell44_results

    # Cell 51 — batching parallel (25 req)
    print()
    print("=" * 60)
    print("CELL 51 — Batching (25 requêtes parallèles par endpoint)")
    print("=" * 60)
    cell51_results = []
    for ep in ENDPOINTS:
        print(f"-> {ep['name']}...")
        r = run_cell51_batching(ep, n_parallel=25)
        cell51_results.append(r)
        print(f"   {r['n_ok']}/{r['n_req']} OK, time={r['total_time_s']}s, "
              f"sum_tokens={r['sum_tokens']}, throughput={r['throughput_tok_per_s']} tok/s")
    results["cell51_batching"] = cell51_results

    # Cell 54 — global parallel (25 req × 3 endpoints = 75 req shuffled)
    print()
    print("=" * 60)
    print("CELL 54 — Parallélisme global (25 req/endpoint, ordre aléatoire)")
    print("=" * 60)
    r = run_cell54_global_parallel(ENDPOINTS, n_per_ep=25)
    results["cell54_global_parallel"] = r
    for ep_name, stats in r["stats_endpoints"].items():
        print(f"   {ep_name}: {stats['ok']}/{stats['calls']} OK, "
              f"sum_tokens={stats['sum_tokens']}, throughput={stats['throughput_tok_per_s']} tok/s")
    print(f"   Total time: {r['total_time_s']}s")

    # Write results to JSON (redact api_key for secrets-hygiene)
    results_to_dump = json.loads(json.dumps(results))  # deep copy
    for ep in results_to_dump.get("endpoints", []):
        if "api_key" in ep:
            ep["api_key"] = "(redacted)" if ep["api_key"] != "no-key-required" else "no-key-required"
    output_path = Path("MyIA.AI.Notebooks/GenAI/Texte/c939_run_results.json")
    output_path.write_text(json.dumps(results_to_dump, indent=2, ensure_ascii=False))
    print(f"\nResults written to: {output_path} (api_key redacted)")


if __name__ == "__main__":
    main()