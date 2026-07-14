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
    python audit_exposed_services.py                  # run full probe
    python audit_exposed_services.py --json out.json  # machine-readable output
    python audit_exposed_services.py --md report.md   # markdown report

Sourced from issue #16 (sécurisation services IA exposés publiquement).
First audit run by po-2023, cycle c.442, 2026-07-14T~14:00Z.
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
from typing import Dict, List, Optional, Tuple

# Tier WebUI login natif — full set of exposed services to probe.
# Each tier entry: (subdomain, compose_dir, auth_endpoint_probe)
#   compose_dir: relative to docker-configurations/services/, or None if no compose.
#   auth_endpoint_probe: URL to test for API auth, or None if not applicable.
DEFAULT_TIER = [
    # (subdomain, expected_compose, api_endpoint_probe)
    ("stable-diffusion-webui-forge.myia.io", "forge-turbo", "/sdapi/v1/options"),
    ("sdnext.myia.io", "sdnext", None),
    ("micro.text-generation-webui.myia.io", None, None),
    ("mini.text-generation-webui.myia.io", None, None),
    ("medium.text-generation-webui.myia.io", None, None),
    ("large.text-generation-webui.myia.io", None, None),
]

DEFAULT_TIMEOUT = 5.0
DEFAULT_USER_AGENT = "CoursIA-AuditExposedServices/1.0 (po-2023, #16)"


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


def probe_api_auth(api_endpoint: Optional[str], port: int = 1111, timeout: float = DEFAULT_TIMEOUT) -> str:
    """Test API auth on a known local port (proxy bypass).

    Returns one of: 'OPEN' (no auth), 'PROTECTED' (401/403), 'N/A' (no probe configured).
    """
    if not api_endpoint:
        return "N/A"
    url = f"http://localhost:{port}{api_endpoint}"
    code, _ = http_probe(url, timeout=timeout)
    if code in (401, 403):
        return "PROTECTED"
    if code == 200:
        return "OPEN"
    return f"ERR({code})"


def classify_subdomain(subdomain: str, compose_dir: Optional[str], api_endpoint: Optional[str],
                       local_port: int = 1111) -> Dict[str, object]:
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
    }


def run_audit(tier: List[Tuple[str, Optional[str], Optional[str]]] = None,
              local_port: int = 1111) -> List[Dict[str, object]]:
    """Run the full audit and return list of findings."""
    if tier is None:
        tier = DEFAULT_TIER
    findings = []
    for subdomain, compose_dir, api_endpoint in tier:
        f = classify_subdomain(subdomain, compose_dir, api_endpoint, local_port=local_port)
        findings.append(f)
    return findings


def render_markdown(findings: List[Dict[str, object]], tier_name: str = "tier WebUI login natif") -> str:
    """Render a markdown audit report (mirror c.442 layout)."""
    lines = [
        f"# Audit `*.myia.io` — {tier_name}",
        "",
        f"Date: {time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())}",
        f"Source: issue #16 (sécurisation services IA exposés publiquement)",
        "",
        "## Résultats",
        "",
        "| Subdomain | DNS | HTTP ext. | Backend | Auth UI | Auth API | Catégorie |",
        "|-----------|-----|-----------|---------|---------|----------|-----------|",
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
        lines.append(
            f"| `{f['subdomain']}` | {dns} | {f['http_external']} | {backend} | {auth_ui} | "
            f"{f['api_auth']} | **{f['category']}** |"
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
        "Issue #16 — po-2023, cycle c.442, 2026-07-14T~14:00Z. Mirror de `scripts/notebook_tools/scan_md_hierarchy.py`.",
    ])
    return "\n".join(lines) + "\n"


def main(argv: Optional[List[str]] = None) -> int:
    parser = argparse.ArgumentParser(description="Audit `*.myia.io` services for auth state.")
    parser.add_argument("--json", metavar="PATH", help="Write JSON findings to PATH")
    parser.add_argument("--md", metavar="PATH", help="Write markdown report to PATH")
    parser.add_argument("--local-port", type=int, default=1111,
                        help="Local backend port for API auth probe (default: 1111, forge-turbo)")
    parser.add_argument("--quiet", action="store_true", help="Suppress stdout output")
    args = parser.parse_args(argv)

    findings = run_audit(local_port=args.local_port)

    if not args.quiet:
        # Compact stdout summary
        for f in findings:
            print(f"  {f['subdomain']:50s} → {f['category']:15s} (HTTP={f['http_external']}, "
                  f"container={f['container_running']}, api_auth={f['api_auth']})")

    if args.json:
        with open(args.json, "w", encoding="utf-8") as fp:
            json.dump(findings, fp, indent=2, ensure_ascii=False)
        if not args.quiet:
            print(f"\nJSON written to {args.json}")

    if args.md:
        with open(args.md, "w", encoding="utf-8") as fp:
            fp.write(render_markdown(findings))
        if not args.quiet:
            print(f"Markdown written to {args.md}")

    # Exit non-zero if any API-LEAK or ORPHELIN found (P0/P1 actions required)
    critical = [f for f in findings if f["category"] in ("API-LEAK", "ORPHELIN-START", "ORPHELIN-DNS")]
    return 1 if critical else 0


if __name__ == "__main__":
    sys.exit(main())
