#!/usr/bin/env python3
"""
Centralized secrets management for the GenAI / CoursIA infrastructure.

MODEL
-----
``.secrets/master.env`` is the SINGLE canonical source for every shared
secret (API tokens, service passwords, session keys). Each service
``.env`` (and the GenAI notebooks ``.env``) is a mix of:

  * service-specific CONFIG (ports, paths, GPU ids, model names) -> stays
    in the service ``.env``, never touched here;
  * shared SECRETS (the keys listed in ``SECRET_KEYS`` below) -> their
    VALUE is propagated from ``master.env`` by this script.

Rotate a shared secret:
  1. Edit ``.secrets/master.env``.
  2. ``python scripts/secrets/render_envs.py``          (propagate)
  3. ``docker compose restart <impacted-services>``     (ComfyUI-Login
     regenerates its bcrypt hash from the env at restart; a running
     container keeps a STALE hash until restarted -- the original cause
     of the "drift" incident).

MODES
-----
  (default)   sync: propagate master.env values into every .env that
              references a SECRET key. Idempotent (re-running is a no-op
              when already in sync).
  --check     report drift only (any service .env whose value for a
              SECRET key differs from master), exit 1 on drift. Use as a
              CI / pre-commit gate.
  --bootstrap ONE-SHOT: scan existing .env files, extract SECRET values,
              write master.env (first-seen value per key; conflicts
              reported). Use only to initialize master.env from a legacy
              scattered layout.

All printed output masks secret values (only the last 4 chars shown).
Neither master.env nor any .env is committed (all gitignored).
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
MASTER_ENV = REPO_ROOT / ".secrets" / "master.env"

# Service + notebooks .env files managed by this script.
TARGET_ENVS = [
    *sorted((REPO_ROOT / "docker-configurations" / "services").glob("*/.env")),
    REPO_ROOT / "MyIA.AI.Notebooks" / "GenAI" / ".env",
]

# Keys whose VALUE is a shared secret and must be synced from master.env.
# Everything else (ports, paths, GPU ids, model names, TZ, ...) is
# service-specific CONFIG and is left untouched in each .env.
#
# Per-instance passwords (each ComfyUI / Forge instance has its OWN
# password) are INTENTIONALLY excluded -- they are not shared and must
# not be collapsed to one value. Their drift prevention is the
# restart-after-.env-change rule (+ entrypoint self-check), not
# centralization.
SECRET_KEYS: frozenset[str] = frozenset({
    # Hugging Face (aliased -- same logical token, two names)
    "HF_TOKEN", "HUGGINGFACE_TOKEN",
    # Paid LLM APIs (centrally managed, rotation-sensitive)
    "OPENAI_API_KEY", "ANTHROPIC_API_KEY", "OPENROUTER_API_KEY",
    # Model hubs / git
    "CIVITAI_TOKEN", "GITHUB_TOKEN", "GITHUB_ACCESS_TOKEN",
    # Per-service client API keys (server defines the value; clients must match)
    "WHISPER_API_KEY", "VLLM_API_KEY", "TTS_API_KEY",
    "QWEN_ASR_API_KEY", "MUSICGEN_API_KEY", "DEMUCS_API_KEY",
    "FUNASR_API_KEY",
    # Qdrant vector DB -- CLIENT side (notebooks RAG / SemanticKernel / Argument).
    # NB: the Qdrant SERVER reads the SAME value under the double-underscore name
    # ``QDRANT__SERVICE__API_KEY`` (config.yaml convention). The server compose
    # lives in the ``roo-extensions`` repo (NOT CoursIA); only the CLIENT key is
    # centralized here so notebook consumers stay in lock-step with the server on
    # rotation. Both names MUST carry the same value.
    "QDRANT_API_KEY",
    # OWUI native API (NB-20, #417) + TTS multi-voice gateway (#16, po-2023)
    "OWUI_API_KEY", "TTS_GATEWAY_API_KEY",
    # ComfyUI client tokens (notebook client <-> service must agree)
    "COMFYUI_VIDEO_TOKEN", "COMFYUI_API_TOKEN",
    # Session
    "SECRET_KEY",
})

# Explicit value aliases: these key pairs must always carry the SAME
# value (one logical secret under two names). On sync, both are written
# from master; on bootstrap, a conflict between an aliased pair is a
# hard error (the two names must agree).
ALIASES: dict[str, str] = {
    "HUGGINGFACE_TOKEN": "HF_TOKEN",
    "GITHUB_ACCESS_TOKEN": "GITHUB_TOKEN",
}


# --------------------------------------------------------------------------- #
# dotenv parse / serialize (minimal, dependency-free)
# --------------------------------------------------------------------------- #
import re

_LINE_RE = re.compile(r"^\s*(?:export\s+)?([A-Za-z_][A-Za-z0-9_]*)\s*=\s*(.*)$")


def parse_kv(value: str) -> str:
    """Strip surrounding quotes / inline comment from a dotenv value."""
    v = value.strip()
    if len(v) >= 2 and v[0] in "\"'" and v[-1] == v[0]:
        v = v[1:-1]
    return v.strip()


def read_env(path: Path) -> dict[str, str]:
    """Return {KEY: raw_value} for every assignment line in path."""
    out: dict[str, str] = {}
    if not path.exists():
        return out
    for line in path.read_text(encoding="utf-8").splitlines():
        m = _LINE_RE.match(line)
        if m:
            out[m.group(1)] = parse_kv(m.group(2))
    return out


def mask(value: str) -> str:
    """Mask a secret for display: show only the last 4 chars."""
    if not value:
        return "<empty>"
    if len(value) <= 4:
        return "*" * len(value)
    return f"***{value[-4:]}"


# --------------------------------------------------------------------------- #
# bootstrap: build master.env from the scattered legacy .env values
# --------------------------------------------------------------------------- #
def _source_priority(env: Path) -> int:
    """Canonical-source priority: a service .env (the server that DEFINES a
    key) outranks the GenAI notebooks .env (a client that CONSUMES it).
    Lower number = higher priority."""
    if "docker-configurations" in env.parts and "services" in env.parts:
        return 0  # service = canonical
    return 1      # GenAI notebooks = client


def bootstrap() -> int:
    if MASTER_ENV.exists():
        print(f"[!] {MASTER_ENV} already exists -- bootstrap is one-shot.")
        print("    Delete it first if you really want to re-bootstrap.")
        return 1

    # value + the (priority, source) that supplied it.
    gathered: dict[str, str] = {}
    src: dict[str, tuple[int, str]] = {}
    client_drift: list[str] = []   # service-vs-client: resolvable (service wins)
    hard_conflicts: list[str] = []  # same-priority: genuinely per-instance / misclassified

    for env in TARGET_ENVS:
        if not env.exists():
            continue
        prio = _source_priority(env)
        for key, val in read_env(env).items():
            if key not in SECRET_KEYS or not val:
                continue
            if key not in gathered:
                gathered[key] = val
                src[key] = (prio, env.parent.name)
            elif gathered[key] == val:
                continue
            else:
                prev_prio, prev_src = src[key]
                if prio < prev_prio:
                    # current (service) outranks stored (client): record drift, swap.
                    client_drift.append(f"  {key}: {env.parent.name}({mask(val)}) "
                                        f"overrides stale {prev_src}({mask(gathered[key])})")
                    gathered[key] = val
                    src[key] = (prio, env.parent.name)
                elif prio > prev_prio:
                    # stored (service) outranks current (client): record drift, keep.
                    client_drift.append(f"  {key}: {prev_src}({mask(gathered[key])}) "
                                        f"overrides stale {env.parent.name}({mask(val)})")
                else:
                    # same priority, different values -> genuinely per-instance
                    hard_conflicts.append(f"  {key}: {env.parent.name}={mask(val)} "
                                          f"vs {prev_src}={mask(gathered[key])}")

    # Enforce alias agreement on the gathered values.
    for alias, canonical in ALIASES.items():
        if alias in gathered and canonical in gathered and gathered[alias] != gathered[canonical]:
            hard_conflicts.append(f"  ALIAS MISMATCH: {alias}={mask(gathered[alias])} "
                                  f"!= {canonical}={mask(gathered[canonical])}")

    if hard_conflicts:
        print("[X] Bootstrap aborted -- same-priority conflicts (per-instance or "
              "misclassified key):")
        for c in hard_conflicts:
            print(c)
        print("\n    These keys have legitimately different values across peers")
        print("    (e.g. one password per instance). Remove them from SECRET_KEYS")
        print("    in render_envs.py -- they are config, not shared secrets.")
        return 2

    MASTER_ENV.parent.mkdir(parents=True, exist_ok=True)
    lines = [
        "# Centralized secrets -- SINGLE source of truth.",
        "# Edit a value HERE, then run: python scripts/secrets/render_envs.py",
        "# Never commit (gitignored). Service-specific config (incl. per-instance",
        "# passwords) stays in each service .env; only shared SECRET values are",
        "# synced from this file.",
        "",
    ]
    for key in sorted(gathered):
        lines.append(f"{key}={gathered[key]}")
    MASTER_ENV.write_text("\n".join(lines) + "\n", encoding="utf-8")

    print(f"[+] Wrote {MASTER_ENV} with {len(gathered)} secret keys:")
    for key in sorted(gathered):
        print(f"      {key} = {mask(gathered[key])}")
    if client_drift:
        print(f"\n[i] {len(client_drift)} client/notebook drift(s) resolved "
              f"(service value taken as canonical):")
        for d in client_drift:
            print(d)
        print("    Run `python scripts/secrets/render_envs.py` to propagate the "
              "canonical values into the drifted notebooks .env.")
    return 0


# --------------------------------------------------------------------------- #
# sync: propagate master.env -> every .env
# --------------------------------------------------------------------------- #
def sync(check_only: bool) -> int:
    if not MASTER_ENV.exists():
        print(f"[X] {MASTER_ENV} not found. Run with --bootstrap first.")
        return 1
    master = read_env(MASTER_ENV)
    missing_in_master = SECRET_KEYS - master.keys()
    if missing_in_master:
        print(f"[!] {len(missing_in_master)} declared SECRET keys are absent from "
              f"master.env (left untouched in services): {sorted(missing_in_master)}")

    drift: list[str] = []
    written: list[str] = []
    for env in TARGET_ENVS:
        if not env.exists():
            continue
        original = env.read_text(encoding="utf-8").splitlines()
        changed = False
        out_lines: list[str] = []
        for line in original:
            m = _LINE_RE.match(line)
            if m and m.group(1) in master:
                key, new_val = m.group(1), master[m.group(1)]
                cur = parse_kv(m.group(2))
                if cur != new_val:
                    drift.append(f"  {env.parent.name}: {key} "
                                 f"{mask(cur)} -> {mask(new_val)}")
                    out_lines.append(f"{key}={new_val}")
                    changed = True
                else:
                    out_lines.append(line)
            else:
                out_lines.append(line)
        if changed and not check_only:
            env.write_text("\n".join(out_lines) + "\n", encoding="utf-8")
            written.append(env.parent.name)

    if drift:
        if check_only:
            print(f"[X] DRIFT detected ({len(drift)} key(s) differ from master):")
            for d in drift:
                print(d)
            print("\n    Run `python scripts/secrets/render_envs.py` to resync.")
            return 1
        print(f"[+] Resynced {len(drift)} value(s) across: {', '.join(written)}")
        for d in drift:
            print(d)
        print("\n[i] Restart impacted containers (ComfyUI-Login hashes regen at restart).")
        return 0

    print(f"[OK] All {len(TARGET_ENVS)} target .env in sync with master.env "
          f"({len(master)} secret keys). No drift.")
    return 0


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__,
                                formatter_class=argparse.RawDescriptionHelpFormatter)
    mode = p.add_mutually_exclusive_group()
    mode.add_argument("--bootstrap", action="store_true",
                      help="one-shot: build master.env from existing .env values")
    mode.add_argument("--check", action="store_true",
                      help="report drift only, exit 1 on drift (CI / pre-commit)")
    args = p.parse_args()
    if args.bootstrap:
        return bootstrap()
    return sync(check_only=args.check)


if __name__ == "__main__":
    sys.exit(main())
