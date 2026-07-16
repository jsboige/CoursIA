#!/usr/bin/env python3
"""Audit publicly-exposed `*.myia.io` services for authentication state.

Distinguishes three categories of debt (audit c.442, 2026-07-14):

- **AUTH-OK**     : auth UI (login form or token gate) PRESENT, auth API
                    (endpoints behind same gate) also PRESENT.
- **API-LEAK**    : auth UI PRESENT (login form, 302 redirect), but API
                    endpoints (e.g. Gradio `/sdapi/*`) respond WITHOUT auth.
                    User can hit backend via API bypass.
- **ORPHELIN-START** : reverse-proxy (IIS) responds 502/504 because no
                    backend Docker container is running, BUT the
                    `docker-compose.yml` exists. Compose-no-start.
- **ORPHELIN-DNS**    : DNS resolves + reverse-proxy routes, but NO
                    `docker-compose.yml` exists for the service. DNS-only
                    ghost subdomain.

Usage:
    python audit_exposed_services.py                  # run all tiers (webui + api)
    python audit_exposed_services.py --tier api       # run only API tier
    python audit_exposed_services.py --tier webui     # run only WebUI tier (legacy default)
    python audit_exposed_services.py --json out.json  # machine-readable output
    python audit_exposed_services.py --md report.md   # markdown report

Sourced from issue #16 (sécurisation services IA exposés publiquement).
First audit run by po-2023, cycle c.442, 2026-07-14T~14:00Z (tier WebUI).
Tier API added by po-2026, cycle c.615, 2026-07-16 (12 services compose-driven
+ 5 ORPHELIN-DNS external — issue #16 §APIs nécessitant des tokens).
Pattern mirror: scripts/notebook_tools/scan_md_hierarchy.py (render-agnostic,
machine-readable summary line per finding, plus human report).
"""

import argparse
import json
import re
import socket
import subprocess
import sys
import time
import urllib.request
import urllib.error
from typing import Dict, List, Optional, Tuple, Union

# A tier entry is a 3- or 4-tuple:
#   (subdomain, compose_dir, api_endpoint[, local_port])
#   compose_dir:    relative to docker-configurations/services/, or None if no
#                  compose. When None, the service falls into ORPHELIN-DNS
#                  (DNS resolves + reverse-proxy routes, but no compose file).
#   api_endpoint:   URL path to test for API auth (localhost probe via
#                  reverse-proxy bypass), or None if not applicable.
#   local_port:     local backend port the API listens on (defaults to 1111
#                  for backward compat with forge-turbo legacy default).
TierEntry = Union[Tuple[str, Optional[str], Optional[str]],
                  Tuple[str, Optional[str], Optional[str], int]]

# Tier WebUI login natif (c.442 #6564) — full set of exposed services to probe.
# Legacy 3-tuple shape; local_port defaults to DEFAULT_LOCAL_PORT (1111).
DEFAULT_TIER: List[TierEntry] = [
    # (subdomain, expected_compose, api_endpoint_probe)
    ("stable-diffusion-webui-forge.myia.io", "forge-turbo", "/sdapi/v1/options"),
    ("sdnext.myia.io", "sdnext", None),
    ("micro.text-generation-webui.myia.io", None, None),
    ("mini.text-generation-webui.myia.io", None, None),
    ("medium.text-generation-webui.myia.io", None, None),
    ("large.text-generation-webui.myia.io", None, None),
]

# Alias for clarity (webui tier == legacy default tier). Added c.615 so that
# future callers can reference WEBUI_TIER by name rather than DEFAULT_TIER.
WEBUI_TIER: List[TierEntry] = DEFAULT_TIER

# Tier API (c.615, this commit) — services listed in issue #16 §"APIs nécessitant
# des tokens" + adjacent compose-driven services in docker-configurations/services/.
# Local ports extracted from each service's docker-compose.yml header comment
# (`# Port: NNNN`) verified firsthand 2026-07-16 (po-2026, c.615).
#
# Three sub-categories:
#   (a) compose-driven (whisper-api, tts-api, etc.) — we can audit from here.
#   (b) ORPHELIN-DNS external (mcp-tools, skagents, embeddings, qdrant, search)
#       — DNS resolves + reverse-proxy routes, but no compose file in this
#       repo. Flagged so that the runbook can route the audit to the
#       appropriate machine tier.
#
# API endpoints probed via `localhost:<port><api_endpoint>` to bypass the
# IIS reverse-proxy and hit the backend directly (same pattern as c.442).
API_TIER: List[TierEntry] = [
    # (subdomain, compose_dir, api_endpoint, local_port)
    # (a) compose-driven API services — 12 entries
    ("whisper-api.myia.io", "whisper-api", "/health", 8190),
    ("whisper-api.myia.io", "whisper-api", "/v1/models", 8190),  # OpenAI-compat probe
    ("tts-api.myia.io", "tts-api", "/health", 8191),
    ("tts-api.myia.io", "tts-api", "/v1/voices", 8191),  # service-specific probe
    ("musicgen-api.myia.io", "musicgen-api", "/health", 8192),
    ("demucs-api.myia.io", "demucs-api", "/health", 8193),
    ("funasr-api.myia.io", "funasr-api", "/health", 8194),
    ("qwen-asr-api.myia.io", "qwen-asr-api", "/health", 8195),
    ("tts-multi.myia.io", "tts-multi", "/health", 8196),
    ("tts-fishaudio.myia.io", "tts-fishaudio", "/health", 8197),
    ("vllm-zimage.myia.io", "vllm-zimage", "/v1/models", 8001),  # OpenAI-compat
    ("comfyui-qwen.myia.io", "comfyui-qwen", "/system_stats", 8188),
    ("comfyui-video.myia.io", "comfyui-video", "/system_stats", 8189),
    ("orchestrator.myia.io", "orchestrator", "/health", 8090),
    # (b) ORPHELIN-DNS external services — 5 entries, no compose in this repo
    ("mcp-tools.myia.io", None, None, 0),
    ("skagents.myia.io", None, None, 0),
    ("embeddings.myia.io", None, None, 0),
    ("qdrant.myia.io", None, None, 0),
    ("search.myia.io", None, None, 0),
]

DEFAULT_TIMEOUT = 5.0
DEFAULT_USER_AGENT = "CoursIA-AuditExposedServices/1.0 (po-2026, #16)"
DEFAULT_LOCAL_PORT = 1111  # forge-turbo legacy default (c.442)
ALL_TIERS: Dict[str, List[TierEntry]] = {
    "webui": WEBUI_TIER,
    "api": API_TIER,
}


def normalize_entry(entry: TierEntry) -> Tuple[str, Optional[str], Optional[str], int]:
    """Promote a 3-tuple entry to a 4-tuple with local_port defaulted.

    Backward compatibility for tests/callers using the legacy 3-tuple shape
    (c.442 #6564). New API_TIER entries use the 4-tuple shape explicitly.
    """
    if len(entry) == 4:
        return entry
    if len(entry) == 3:
        subdomain, compose_dir, api_endpoint = entry
        return (subdomain, compose_dir, api_endpoint, DEFAULT_LOCAL_PORT)
    raise ValueError(
        f"TierEntry must be 3- or 4-tuple, got {len(entry)}-tuple: {entry!r}"
    )


def dns_resolves(host: str) -> Tuple[bool, Optional[str]]:
    """Return (resolves, ip) for the given hostname."""
    try:
        ip = socket.gethostbyname(host)
        return True, ip
    except (socket.gaierror, socket.herror):
        return False, None


def http_probe(url: str, timeout: float = DEFAULT_TIMEOUT) -> Tuple[int, Dict[str, str]]:
    """Return (status_code, headers_dict) for the given URL (HEAD first, GET fallback)."""
    req = urllib.request.Request(url, method="GET")
    req.add_header("User-Agent", DEFAULT_USER_AGENT)
    try:
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            return resp.status, dict(resp.headers)
    except urllib.error.HTTPError as e:
        return e.code, dict(e.headers or {})
    except (urllib.error.URLError, TimeoutError, OSError) as e:
        return 0, {"error": str(e)}


def compose_exists(compose_dir: Optional[str], repo_root: str = ".") -> bool:
    """Check if docker-compose.yml exists for the given service directory."""
    if not compose_dir:
        return False
    import os
    path = os.path.join(repo_root, "docker-configurations", "services", compose_dir, "docker-compose.yml")
    return os.path.isfile(path)


def container_running(compose_dir: Optional[str]) -> bool:
    """Check if a Docker container matching the compose service name is running."""
    if not compose_dir:
        return False
    try:
        out = subprocess.run(
            ["docker", "ps", "--filter", f"name={compose_dir}", "--format", "{{.Names}}"],
            capture_output=True, text=True, timeout=10,
        )
        return compose_dir in out.stdout
    except (subprocess.TimeoutExpired, FileNotFoundError):
        return False


def probe_api_auth(api_endpoint: Optional[str], port: int = DEFAULT_LOCAL_PORT,
                   timeout: float = DEFAULT_TIMEOUT) -> str:
    """Test API auth on a known local port (proxy bypass).

    Returns one of: 'OPEN' (no auth), 'PROTECTED' (401/403), 'N/A' (no probe
    configured), 'ERR(<code>)' for other non-200/non-401/non-403 responses.

    Accepts port=0 as 'skip' (used by ORPHELIN-DNS external services — see
    issue #16 §APIs nécessitant des tokens). In that case returns 'N/A'
    unconditionally, since we cannot reach a backend that has no compose
    file in this repo.
    """
    if not api_endpoint or port == 0:
        return "N/A"
    url = f"http://localhost:{port}{api_endpoint}"
    code, _ = http_probe(url, timeout=timeout)
    if code in (401, 403):
        return "PROTECTED"
    if code == 200:
        return "OPEN"
    return f"ERR({code})"


def classify_subdomain(subdomain: str, compose_dir: Optional[str], api_endpoint: Optional[str],
                       local_port: int = DEFAULT_LOCAL_PORT) -> Dict[str, object]:
    """Run all probes and return a single finding dict."""
    resolves, ip = dns_resolves(subdomain)
    http_code, headers = http_probe(f"https://{subdomain}", timeout=DEFAULT_TIMEOUT)
    compose = compose_exists(compose_dir)
    container = container_running(compose_dir)
    api_auth = probe_api_auth(api_endpoint, port=local_port)

    if not resolves:
        category = "NO-DNS"
    elif not compose and not container:
        category = "ORPHELIN-DNS"
    elif compose and not container:
        category = "ORPHELIN-START"
    elif container and api_auth == "OPEN":
        # Substance: backend is up, but its API endpoints accept unauthenticated
        # requests. The UI may be protected (login form) but the API surface
        # is the actual attack vector. Flag API-LEAK regardless of the external
        # proxy state (502 just means the proxy is misconfigured too, but the
        # backend substance is the leak).
        category = "API-LEAK"
    elif container and api_auth == "PROTECTED":
        category = "AUTH-OK"
    else:
        category = "UNCLEAR"

    return {
        "subdomain": subdomain,
        "category": category,
        "dns_resolves": resolves,
        "dns_ip": ip,
        "http_external": http_code,
        "compose_exists": compose,
        "container_running": container,
        "api_auth": api_auth,
        "redirect": headers.get("Location", ""),
        "server": headers.get("Server", ""),
        "local_port": local_port,  # new c.615: which port was probed
        "compose_dir": compose_dir,  # new c.615: aid triage of ORPHELIN-START/DNS
    }


def run_audit(tier: Optional[List[TierEntry]] = None,
              local_port: int = DEFAULT_LOCAL_PORT) -> List[Dict[str, object]]:
    """Run the full audit and return list of findings.

    When `tier` is None, defaults to WEBUI_TIER (== legacy DEFAULT_TIER) for
    backward compatibility with c.442 callers and tests. New code should
    pass an explicit tier (WEBUI_TIER, API_TIER, or pass the union of both).
    Per-entry `local_port` from the tier tuple takes precedence over the
    function-level `local_port` argument.
    """
    if tier is None:
        tier = WEBUI_TIER
    findings = []
    for entry in tier:
        subdomain, compose_dir, api_endpoint, entry_port = normalize_entry(entry)
        # Per-entry port overrides function-level default — supports mixed-port
        # tiers where each service listens on its own port.
        effective_port = entry_port if entry_port != DEFAULT_LOCAL_PORT else local_port
        f = classify_subdomain(
            subdomain, compose_dir, api_endpoint,
            local_port=effective_port,
        )
        findings.append(f)
    return findings


def render_markdown(findings: List[Dict[str, object]], tier_name: str = "tier WebUI login natif") -> str:
    """Render a markdown audit report (mirror c.442 layout).

    Header reflects tier_name (e.g. 'tier WebUI login natif', 'tier API',
    'tous tiers (WebUI + API)'). Local port column added in c.615 so operators
    can see which port was probed for each service.
    """
    lines = [
        f"# Audit `*.myia.io` — {tier_name}",
        "",
        f"Date: {time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())}",
        f"Source: issue #16 (sécurisation services IA exposés publiquement)",
        "",
        "## Résultats",
        "",
        "| Subdomain | DNS | HTTP ext. | Backend | Auth UI | Auth API | Port | Catégorie |",
        "|-----------|-----|-----------|---------|---------|----------|------|-----------|",
    ]
    for f in findings:
        dns = "OK" if f["dns_resolves"] else "FAIL"
        compose = f["compose_exists"] and f["container_running"]
        backend = "running" if f["container_running"] else (
            "compose-only" if f["compose_exists"] else "absent"
        )
        auth_ui = (
            "OK" if f["redirect"].endswith("/login")
            else ("n/a" if not f["container_running"] else "?")
        )
        # Format the port column: 0 means "skipped" (ORPHELIN-DNS external).
        port = f.get("local_port", DEFAULT_LOCAL_PORT)
        port_str = str(port) if port else "—"
        lines.append(
            f"| `{f['subdomain']}` | {dns} | {f['http_external']} | {backend} | {auth_ui} | "
            f"{f['api_auth']} | {port_str} | **{f['category']}** |"
        )
    lines.extend([
        "",
        "## Légende catégories",
        "",
        "- **AUTH-OK** : auth UI et API présentes, service sécurisé.",
        "- **API-LEAK** : auth UI (login) présente mais endpoints API ouverts sans auth.",
        "- **ORPHELIN-START** : compose existe mais container pas démarré (502 via reverse-proxy).",
        "- **ORPHELIN-DNS** : DNS résout + reverse-proxy route, mais aucun compose file (ghost).",
        "- **NO-DNS** : subdomain ne résout pas (DNS-only ghost, pas d'IIS).",
        "",
        "## Sourced from",
        "",
        "Issue #16 — WebUI tier po-2023 c.442 2026-07-14 (#6564).",
        "API tier extension po-2026 c.615 2026-07-16.",
        "Mirror de `scripts/notebook_tools/scan_md_hierarchy.py`.",
    ])
    return "\n".join(lines) + "\n"


def main(argv: Optional[List[str]] = None) -> int:
    parser = argparse.ArgumentParser(
        description="Audit `*.myia.io` services for auth state (tier WebUI + tier API).",
    )
    parser.add_argument("--tier", choices=("webui", "api", "all"), default="all",
                        help="Which tier to audit: 'webui' (login natif, c.442), "
                             "'api' (services API compose-driven, c.615), "
                             "or 'all' (default).")
    parser.add_argument("--json", metavar="PATH", help="Write JSON findings to PATH")
    parser.add_argument("--md", metavar="PATH", help="Write markdown report to PATH")
    parser.add_argument("--local-port", type=int, default=DEFAULT_LOCAL_PORT,
                        help="Fallback local backend port (default: 1111, forge-turbo). "
                             "Per-entry ports in API_TIER override this.")
    parser.add_argument("--quiet", action="store_true", help="Suppress stdout output")
    args = parser.parse_args(argv)

    # Tier selection. 'all' concatenates WEBUI_TIER and API_TIER in that order,
    # so the audit report reads WebUI first (c.442 baseline) then API.
    if args.tier == "webui":
        tier = WEBUI_TIER
        tier_name = "tier WebUI login natif"
    elif args.tier == "api":
        tier = API_TIER
        tier_name = "tier API (compose-driven + ORPHELIN-DNS)"
    else:
        tier = WEBUI_TIER + API_TIER
        tier_name = "tous tiers (WebUI + API)"

    findings = run_audit(tier=tier, local_port=args.local_port)

    if not args.quiet:
        # Compact stdout summary
        for f in findings:
            print(f"  {f['subdomain']:45s} → {f['category']:15s} "
                  f"(HTTP={f['http_external']}, container={f['container_running']}, "
                  f"api_auth={f['api_auth']}, port={f['local_port']})")

    if args.json:
        with open(args.json, "w", encoding="utf-8") as fp:
            json.dump(findings, fp, indent=2, ensure_ascii=False)
        if not args.quiet:
            print(f"\nJSON written to {args.json}")

    if args.md:
        with open(args.md, "w", encoding="utf-8") as fp:
            fp.write(render_markdown(findings, tier_name=tier_name))
        if not args.quiet:
            print(f"Markdown written to {args.md}")

    # Exit non-zero if any API-LEAK or ORPHELIN found (P0/P1 actions required)
    critical = [f for f in findings if f["category"] in ("API-LEAK", "ORPHELIN-START", "ORPHELIN-DNS")]
    return 1 if critical else 0


if __name__ == "__main__":
    sys.exit(main())
