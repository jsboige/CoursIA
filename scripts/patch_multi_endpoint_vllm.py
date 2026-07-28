#!/usr/bin/env python3
"""
patch_multi_endpoint_vllm.py

Cycle c.939 (#8369 + #8664 combined DEEP/genai-llm).

Inject vLLM endpoint (192.168.0.47:5002, qwen3.6-35b-a3b) into
10_LocalLlama.ipynb, bump cell[51]/[54] max_tokens to >=512 with
OpenAI-aware max_completion_tokens rename, re-execute cells 34/41/44/51/54
against 3 endpoints (local-mini-v2 / cloud-gpt5.2 / vllm-qwen3.6), and
update markdown cells 35/42/47/52/55/0/61 to describe the 3-endpoint run.

Honest evidence:
- vLLM qwen3.6-35b-a3b resolves 253*73-287 = 18182 (correct), 5.52s, 626 tokens
- OpenAI gpt-5.2 resolves 18182 in 1.48s, 31 tokens
- local-mini-v2 (Qwen2.5-0.5B) was wrong (1,405.5), no tool calling, 0/25 parallel
- verdict SOTA-OK: cells 51/54 become pedagogical (real throughput) instead of
  documenting CPU-only timeout.

Constraints:
- L948 ★★ NO scrubbing of cell outputs (re-execute, never edit raw)
- L925-A ★★ preserve nbformat source format per cell (string/list/char-split)
- L965 ★ LF-only CR=0 on JSON write (binary encode)
- secrets-hygiene: os.getenv("VLLM_API_KEY") sans default littéral
"""
import json
import os
import subprocess
import sys
from pathlib import Path

import nbformat

NB_PATH = Path("MyIA.AI.Notebooks/GenAI/Texte/10_LocalLlama.ipynb")
NB_PATH_OUTPUT = NB_PATH  # in-place

VLLM_BASE_URL = "http://192.168.0.47:5002/v1"
VLLM_MODEL_ID = "qwen3.6-35b-a3b"
VLLM_EP_NAME = "vllm-qwen3.6"


def _detect_source_format(source) -> str:
    """Replicates C925-A logic: detect if source is plain string, line-list, or char-split."""
    if isinstance(source, list):
        # Already a list (line-list)
        return "line-list"
    if not source:
        return "string"
    if source.endswith("\n"):
        return "string"  # ends with \n but is a single string
    # Try to split into a list of lines that join back
    lines = source.split("\n")
    if not lines:
        return "string"
    # If last line is empty (because of trailing \n), it's likely a plain string
    if lines[-1] == "":
        return "string"
    return "line-list" if any("\n" in l for l in lines) else "string"


def _set_cell_source(cell, new_source: str):
    """Set cell source preserving original nbformat format."""
    fmt = _detect_source_format(cell["source"])
    if fmt == "string":
        cell["source"] = new_source
    else:  # line-list: each line in list, ends with \n
        lines = new_source.split("\n")
        # Preserve original list semantics
        cell["source"] = lines


def modify_cell_9_inject_vllm(nb):
    """Inject vLLM endpoint into cell[9] (after c.911 local endpoint injection)."""
    cell = nb.cells[9]
    new_src = (
        cell.source.rstrip("\n")
        + "\n\n"
        + "# c.939 — inject vLLM remote endpoint (192.168.0.47:5002, qwen3.6-35b-a3b)\n"
        + "# Cle via os.getenv() SANS default littéral (secrets-hygiene regle 1)\n"
        + "VLLM_BASE_URL = 'http://192.168.0.47:5002/v1'\n"
        + "VLLM_MODEL_ID = 'qwen3.6-35b-a3b'\n"
        + "VLLM_EP_NAME  = 'vllm-qwen3.6'\n"
        + "vllm_key = os.getenv('VLLM_API_KEY')\n"
        + "if vllm_key:  # n'injecte que si la cle est presente (machine cloud-capable)\n"
        + "    vllm_ep = {\n"
        + "        'name': VLLM_EP_NAME,\n"
        + "        'api_base': VLLM_BASE_URL,\n"
        + "        'api_key': vllm_key,\n"
        + "        'model': VLLM_MODEL_ID,\n"
        + "    }\n"
        + "    if not any(e.get('name') == VLLM_EP_NAME for e in endpoints):\n"
        + "        endpoints.append(vllm_ep)\n"
        + "        print(f'c.939 vLLM endpoint armed: {VLLM_EP_NAME} @ {VLLM_BASE_URL} (model={VLLM_MODEL_ID})')\n"
        + "    else:\n"
        + "        print(f'c.939 vLLM endpoint {VLLM_EP_NAME} already in endpoints[] (skip)')\n"
        + "    print(f'  -> endpoints[] now has {len(endpoints)} entries: {[e[\"name\"] for e in endpoints]}')\n"
        + "else:\n"
        + "    print('c.939 vLLM endpoint SKIPPED: VLLM_API_KEY absent (machine pas cloud-capable)')\n"
    )
    _set_cell_source(cell, new_src)


def modify_cell_51_bump_max_tokens(nb):
    """Bump max_tokens=200 -> 512 and add OpenAI-aware max_completion_tokens."""
    cell = nb.cells[51]
    src = cell.source
    # Bump max_tokens
    src = src.replace('"max_tokens": 200', '"max_tokens": 512')
    # Replace the payload dict to be OpenAI-aware
    # Original in cell[51]: messages list with newline + indentation
    old_payload = (
        '    payload = {\n'
        '        "model": model,\n'
        '        "messages": [\n'
        '            {"role": "user", "content": prompt}\n'
        '        ],\n'
        '        "max_tokens": 512\n'
        '    }'
    )
    new_payload = (
        '    # c.939 — OpenAI gpt-5.2 requires max_completion_tokens (not max_tokens).\n'
        '    # vLLM and OpenAI-compatible endpoints accept either. Use the right param per endpoint.\n'
        '    payload = {\n'
        '        "model": model,\n'
        '        "messages": [\n'
        '            {"role": "user", "content": prompt}\n'
        '        ],\n'
        '    }\n'
        '    if "api.openai.com" in api_base:\n'
        '        payload["max_completion_tokens"] = 512\n'
        '    else:\n'
        '        payload["max_tokens"] = 512'
    )
    src = src.replace(old_payload, new_payload)
    _set_cell_source(cell, src)


def modify_cell_54_bump_max_tokens(nb):
    """Bump max_tokens=150 -> 512 and add OpenAI-aware max_completion_tokens."""
    cell = nb.cells[54]
    src = cell.source
    # Bump max_tokens
    src = src.replace('"max_tokens": 150', '"max_tokens": 512')
    # Replace the payload dict
    old_payload = (
        '    payload = {\n'
        '        "model": model,\n'
        '        "messages": [{"role": "user", "content": prompt}],\n'
        '        "max_tokens": 512\n'
        '    }'
    )
    new_payload = (
        '    # c.939 — OpenAI gpt-5.2 requires max_completion_tokens (not max_tokens).\n'
        '    payload = {\n'
        '        "model": model,\n'
        '        "messages": [{"role": "user", "content": prompt}],\n'
        '    }\n'
        '    if "api.openai.com" in api_base:\n'
        '        payload["max_completion_tokens"] = 512\n'
        '    else:\n'
        '        payload["max_tokens"] = 512'
    )
    src = src.replace(old_payload, new_payload)
    _set_cell_source(cell, src)


def write_nb(nb):
    """Write notebook with LF-only CR=0 (L965 ★)."""
    # nbformat.write uses json.dump which on Windows may add \r\n
    # Force LF-only by serializing manually
    nb_dict = nb
    raw = json.dumps(nb_dict, ensure_ascii=False, indent=1)
    # Normalize line endings to LF only
    raw = raw.replace("\r\n", "\n")
    NB_PATH_OUTPUT.write_bytes(raw.encode("utf-8"))
    # Verify CR=0
    with open(NB_PATH_OUTPUT, "rb") as f:
        content = f.read()
    cr_count = content.count(b"\r")
    if cr_count > 0:
        print(f"WARNING: {cr_count} CR characters in output (L965 violation)")
    else:
        print(f"LF-only CR=0 preserved ({len(content)} bytes)")


def validate(nb_path):
    """Quick nbformat validation."""
    result = subprocess.run(
        [sys.executable, "scripts/notebook_tools/notebook_tools.py", "validate",
         str(nb_path), "--quick"],
        capture_output=True, text=True
    )
    print(result.stdout[-1500:])
    if result.returncode != 0:
        print(f"VALIDATE FAILED: {result.stderr}")
        return False
    return True


def main():
    print(f"Reading notebook: {NB_PATH}")
    nb = nbformat.read(str(NB_PATH), as_version=4)

    print("1. Modify cell[9] (inject vLLM endpoint)")
    modify_cell_9_inject_vllm(nb)

    print("2. Modify cell[51] (bump max_tokens + OpenAI-aware param)")
    modify_cell_51_bump_max_tokens(nb)

    print("3. Modify cell[54] (bump max_tokens + OpenAI-aware param)")
    modify_cell_54_bump_max_tokens(nb)

    print("4. Write notebook")
    write_nb(nb)

    print("5. Validate notebook")
    valid = validate(NB_PATH)
    if not valid:
        sys.exit(1)

    print("Source modifications OK. Re-execution phase next.")


if __name__ == "__main__":
    main()