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
  --bootstrap-missing  close the .env blind spot (#9351): for every
              service dir with a docker-compose.yml but no .env, parse
              the compose file's ${KEY} references, and write a fresh
              .env containing every referenced SECRET_KEY whose value is
              present in master.env. Idempotent (services with an
              existing .env are left to sync()). Use after pulling this
              change to recover services that have NEVER had an .env
              provisioned -- running sync() alone would leave them
              invisible to --check.

All printed output masks secret values (only the last 4 chars shown).
Neither master.env nor any .env is committed (all gitignored).
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
MASTER_ENV = REPO_ROOT / ".secrets" / "master.env"
SERVICES_ROOT = REPO_ROOT / "docker-configurations" / "services"

# Service + notebooks .env files managed by this script.
#
# Note: TARGET_ENVS only enumerates .env files that ALREADY EXIST. A service
# directory that lacks a .env is invisible to ``--check`` and to sync until
# ``--bootstrap-missing`` has run (see ``bootstrap_missing_envs`` + the
# ``--bootstrap-missing`` CLI flag). The whisper-api drift incident (#9351)
# was undetectable by ``--check`` precisely because whisper-api/ had no .env;
# the running container's API_KEY was injected at ``docker run``-time, drifted
# from master.env, and the auditor saw ``[OK]`` because there was no file to
# compare against. ``--bootstrap-missing`` closes this blind spot by writing
# the missing .env from master.env so future ``--check`` runs SEE drift.
TARGET_ENVS = [
    *sorted(SERVICES_ROOT.glob("*/.env")),
    REPO_ROOT / "MyIA.AI.Notebooks" / "GenAI" / ".env",
    # Lean prover harness: agent_tests/prover/config.py loads this .env.
    # Centralizes MISTRAL_API_KEY (Leanstral trial, #5475) + ANTHROPIC_API_KEY
    # so rotation = edit master.env + render (cf #16 "rotation facile").
    # Only keys present in master.env are rewritten; the prover's own
    # ZAI/LOCAL/OPENROUTER config (absent from master) is left untouched.
    REPO_ROOT / "MyIA.AI.Notebooks" / "SymbolicAI" / "Lean" / ".env",
    # Trading paper harness: Portfolio-IBKR-Coinbase-Hybrid/paper_harness/config.py
    # loads this .env. Centralizes the IBKR paper login (#1199) so a re-provision =
    # edit master.env + render. The credential was lost 3x when it lived only in a
    # per-machine .env with no canonical anchor -- master.env is now that anchor.
    REPO_ROOT / "MyIA.AI.Notebooks" / "QuantConnect" / "projects" / "Portfolio-IBKR-Coinbase-Hybrid" / ".env",
    # --- Notebook-side .env targets (#9929, c.10186) -----------------------
    # Closes the structural blind-spot documented in ai-01's c.9929 finding:
    # `--check` reports `[OK] No drift` whenever a `.env` is **absent** from
    # TARGET_ENVS, even if it carries a stale shared key (e.g. a revoked
    # OpenAI token duplicated into two series, sha=4a2fac0e1714 -> HTTP 401).
    # Six escalations in a row (#6255 #8519 #8624 #9059 #9929 + the
    # GPU-1 "vLLM DOWN" phantom) evaporated to a 10-second measurement that
    # TARGET_ENVS would have surfaced. The lists below are **optional**: a
    # path that does not exist on the current machine is silently skipped
    # (see ``sync()``'s ``if not env.exists(): continue``), so adding them is
    # a no-op on machines where the series is absent and a real check on
    # machines where the series is present (e.g. ai-01 confirmed SmartContracts
    # + QuantConnect + SymbolicLearning carry real OPENAI/OPENROUTER keys).
    # Per-series rationale lives in the comments above each entry below.
    # AgenticDataScience (ML/DataScienceWithAgents series). ECE TP uses
    # OPENAI_API_KEY + OPENAI_BASE_URL; OPENROUTER is a duplicate alias.
    REPO_ROOT / "MyIA.AI.Notebooks" / "ML" / "DataScienceWithAgents" / "AgenticDataScience" / ".env",
    # SemanticKernel notebooks (.NET Interactive). 0-AI-settings.ipynb +
    # 09-SemanticKernel-Building-CLR consume this via Settings.LoadFromFile
    # (config/settings.json is gitignored and derived from this key -- see
    # render_settings_json.py).
    REPO_ROOT / "MyIA.AI.Notebooks" / "SemanticKernel" / ".env",
    # SmartContracts series (Solidity, foundry). OPENAI_API_KEY is an
    # OpenRouter-key alias used by SC-11 LLM-Assisted notebook.
    REPO_ROOT / "MyIA.AI.Notebooks" / "SymbolicAI" / "SmartContracts" / ".env",
    # QuantConnect series. May carry OPENAI_API_KEY on machines that use
    # OpenAI for QC LLM summaries (not all do -- some route via QC Cloud).
    REPO_ROOT / "MyIA.AI.Notebooks" / "QuantConnect" / ".env",
    # SymbolicLearning series. SL-* notebooks may consume OPENAI/OPENROUTER
    # for LLM-assisted proof search. Path may not exist on machines that
    # never provisioned it.
    REPO_ROOT / "MyIA.AI.Notebooks" / "SymbolicAI" / "SymbolicLearning" / ".env",
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
    "OPENAI_API_KEY", "ANTHROPIC_API_KEY", "OPENROUTER_API_KEY", "MISTRAL_API_KEY",
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
    # IBKR paper/simulated trading login (Portfolio-IBKR-Coinbase-Hybrid, #1199).
    # A single shared credential (not per-instance) -> centralized so a re-provision
    # is edit-master + render, never a scattered per-machine .env that gets lost.
    # IBKR_ACCOUNT_ID stays out (it is an identifier discovered post-login, not a
    # secret; it lives in the consumer .env as config).
    "IBKR_USERNAME", "IBKR_PASSWORD",
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


# --------------------------------------------------------------------------- #
# --bootstrap-missing: close the .env-blind-spot (#9351)
#
# When a service's docker-compose.yml references ${SOME_KEY} to interpolate a
# master.env value, the SERVICE runs fine (docker compose expands the var) but
# render_envs.py has nothing to compare against — ``--check`` reads ``[OK]``
# because the .env file is missing, while the canonical divergence is silently
# INVISIBLE. The fix: when invoked with --bootstrap-missing, scan every
# service directory for a docker-compose.yml (or -hybrid sibling), parse its
# ${KEY} references, and for each KEY that exists in master.env and that the
# service does NOT yet have in its .env, write KEY=<master_value> to a fresh
# .env. Future ``--check`` runs now have a file to compare against.
# --------------------------------------------------------------------------- #
_COMPOSE_GLOBS = ("docker-compose.yml", "docker-compose-hybrid.yml")
# Matches ${VAR} and ${VAR:-default} interpolation tokens in compose YAML.
# Intentionally naive: a token whose body is "}" or ":-" is ignored (defensive).
_COMPOSE_VAR_RE = re.compile(r"\$\{([A-Za-z_][A-Za-z0-9_]*)(?::-[^}]*)?\}")


def _compose_referenced_keys(compose_path: Path, secret_keys: frozenset[str]) -> set[str]:
    """Return the subset of ``secret_keys`` referenced by ${KEY} in compose_path.

    Pure parser: no YAML library required (the patterns we look for are
    trivial), no false positives from YAML comments (they don't contain ``${``).
    A service that references ``${UNREGISTERED_KEY}`` is ignored — only keys
    declared in ``SECRET_KEYS`` are considered, so the writer never emits a
    value the script cannot later keep in sync.
    """
    if not compose_path.exists():
        return set()
    text = compose_path.read_text(encoding="utf-8")
    found = set()
    for m in _COMPOSE_VAR_RE.finditer(text):
        key = m.group(1)
        if key in secret_keys:
            found.add(key)
    return found


def _service_compose_paths(service_dir: Path) -> list[Path]:
    """Return the compose files for a service dir, in deterministic order."""
    return [service_dir / g for g in _COMPOSE_GLOBS if (service_dir / g).exists()]


def bootstrap_missing_envs(
    services_root: Path | None = None,
    master_path: Path | None = None,
    secret_keys: frozenset[str] | None = None,
) -> list[str] | None:
    """Auto-create .env for services whose compose file references a SECRET_KEY
    but who lack a .env. Returns the list of service-dir names that were
    newly written. Hermetic test paths: (a) caller passes ``services_root`` /
    ``master_path`` / ``secret_keys`` explicitly, OR (b) caller monkeypatches
    the module globals (``render_envs.MASTER_ENV`` / ``SERVICES_ROOT``) and
    invokes via ``main()`` — the ``None`` defaults below defer to the LIVE
    module globals at call time, so such monkeypatches bite.

    Precedence: if the service already has an .env, it is left untouched
    (sync() handles updates). If the service has NO .env but has at least one
    compose file, the union of ${KEY} references across BOTH compose files
    becomes the candidate key set; only keys present in master.env get
    written. Values originate from master.env — never from the running
    container, the host shell, or an interactive prompt.

    Returns ``None`` when master.env is missing (vs ``[]`` when no gaps
    need filling), so the CLI can distinguish "no-op success" from "cannot
    run" via different exit codes.
    """
    # Resolve module globals at CALL TIME, not import time. Binding these as
    # default args (= SERVICES_ROOT / MASTER_ENV / SECRET_KEYS) would freeze
    # them to their import-time values, making a test's
    # ``monkeypatch.setattr(render_envs, "MASTER_ENV", tmp_path/...)`` INERT --
    # the #10085 hermeticity defect: the function read the REAL master.env on
    # every cluster machine (writing real service .env files with live key
    # material) while CI stayed spuriously green only because it owns no
    # master.env. The None-sentinel defers to the live module global so test
    # monkeypatches bite; explicit callers (tests passing tmp_path) override
    # exactly as before.
    if services_root is None:
        services_root = SERVICES_ROOT
    if master_path is None:
        master_path = MASTER_ENV
    if secret_keys is None:
        secret_keys = SECRET_KEYS
    if not master_path.exists():
        print(f"[X] {master_path} not found. Run with --bootstrap first.")
        return None
    master = read_env(master_path)
    available = {k: v for k, v in master.items() if k in secret_keys and v}

    written: list[str] = []
    for service_dir in sorted(p for p in services_root.iterdir() if p.is_dir()):
        env_path = service_dir / ".env"
        if env_path.exists():
            continue  # sync() handles this; we only fill gaps.
        compose_paths = _service_compose_paths(service_dir)
        if not compose_paths:
            continue  # no docker-compose* => nothing to auto-provision.
        referenced: set[str] = set()
        for cp in compose_paths:
            referenced |= _compose_referenced_keys(cp, secret_keys)
        keys_to_emit = sorted(referenced & available.keys())
        if not keys_to_emit:
            continue
        lines = [
            f"# Auto-generated by render_envs.py --bootstrap-missing (cf #9351).",
            f"# Edit values in .secrets/master.env, then re-run this script.",
            "",
        ]
        lines.extend(f"{k}={available[k]}" for k in keys_to_emit)
        lines.append("")
        env_path.write_text("\n".join(lines), encoding="utf-8")
        written.append(service_dir.name)
        print(f"[+] {service_dir.name}: created .env with {len(keys_to_emit)} "
              f"key(s) {[mask(available[k]) for k in keys_to_emit]}")
    if not written:
        print(f"[OK] No missing .env in {services_root} (all services have "
              f".env OR no compose-referenced SECRET_KEYS).")
    return written


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__,
                                formatter_class=argparse.RawDescriptionHelpFormatter)
    mode = p.add_mutually_exclusive_group()
    mode.add_argument("--bootstrap", action="store_true",
                      help="one-shot: build master.env from existing .env values")
    mode.add_argument("--check", action="store_true",
                      help="report drift only, exit 1 on drift (CI / pre-commit)")
    mode.add_argument("--bootstrap-missing", action="store_true",
                      help="auto-create .env for service dirs that have a "
                           "docker-compose.yml but no .env (closes the "
                           "--check blind spot, cf #9351)")
    args = p.parse_args()
    if args.bootstrap:
        return bootstrap()
    if args.bootstrap_missing:
        # bootstrap_missing_envs returns None on missing master.env, [] on
        # successful no-op, list on writes. Map None -> 1 (cannot run),
        # otherwise -> 0 (success regardless of whether anything was written).
        return 1 if bootstrap_missing_envs() is None else 0
    return sync(check_only=args.check)


if __name__ == "__main__":
    sys.exit(main())
