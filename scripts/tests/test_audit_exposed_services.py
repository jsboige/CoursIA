#!/usr/bin/env python3
"""Tests for audit_exposed_services.py — round-trip output-content asserts (L498).

Per L498, REDACT-class tooling MUST have a round-trip OUTPUT-content test,
not just detection boolean. For audit_exposed_services.py, the analog is:
classify_subdomain must classify correctly across all 5 categories (output
content) AND helpers (dns_resolves, compose_exists, container_running,
probe_api_auth, http_probe) must return the right SHAPE (boolean-like).

Pattern mirror: scripts/notebook_tools/tests/test_strip_machine_paths.py
(detection + non-overlap + round-trip output).
"""
from __future__ import annotations

import json
import os
import socket
import sys
import tempfile
from pathlib import Path
from unittest import mock

import pytest

# Mirror the import style from test_strip_machine_paths.py
REPO_ROOT = Path(__file__).resolve().parents[2]
SCRIPTS_SECURITY = REPO_ROOT / "scripts" / "security"
sys.path.insert(0, str(REPO_ROOT / "scripts"))

from security.audit_exposed_services import (  # noqa: E402
    DEFAULT_TIER,
    WEBUI_TIER,
    API_TIER,
    DEFAULT_LOCAL_PORT,
    classify_subdomain,
    compose_exists,
    container_running,
    dns_resolves,
    http_probe,
    normalize_entry,
    probe_api_auth,
    render_markdown,
    run_audit,
)


# --- helpers: mock fixtures ---

def _no_dns(_host: str):
    return (False, None)


def _dns_ok(_host: str):
    return (True, "82.66.89.184")


def _http_ok(url, timeout=5.0):
    return (200, {"Server": "Gradio", "Location": "/login"})


def _http_502(url, timeout=5.0):
    return (502, {"Server": "Microsoft-IIS/10.0", "Location": ""})


def _http_401(url, timeout=5.0):
    return (401, {"Server": "Gradio"})


def _container_running(compose_dir):
    return True


def _compose_yes(compose_dir, repo_root="."):
    return True


def _compose_no(compose_dir, repo_root="."):
    return False


# --- DNS helper ---

def test_dns_resolves_returns_tuple_false():
    # Script catches (socket.gaierror, herror) — both inherit from OSError.
    # Use a proper gaierror to verify the handler.
    with mock.patch("socket.gethostbyname", side_effect=socket.gaierror("no DNS")):
        resolves, ip = dns_resolves("does-not-exist.invalid")
    assert resolves is False
    assert ip is None


def test_dns_resolves_returns_tuple_true():
    with mock.patch("socket.gethostbyname", return_value="10.0.0.1"):
        resolves, ip = dns_resolves("ok.example")
    assert resolves is True
    assert ip == "10.0.0.1"


# --- HTTP probe ---

def test_http_probe_200_returns_status():
    with mock.patch("urllib.request.urlopen") as m:
        m.return_value.__enter__.return_value.status = 200
        m.return_value.__enter__.return_value.headers = {"Server": "IIS"}
        code, headers = http_probe("https://example.com")
    assert code == 200
    assert headers["Server"] == "IIS"


# --- compose_exists ---

def test_compose_exists_none_returns_false(tmp_path):
    assert compose_exists(None, repo_root=str(tmp_path)) is False


def test_compose_exists_real_present(tmp_path):
    compose_dir = tmp_path / "docker-configurations" / "services" / "forge-turbo"
    compose_dir.mkdir(parents=True)
    (compose_dir / "docker-compose.yml").write_text("services: {}\n")
    assert compose_exists("forge-turbo", repo_root=str(tmp_path)) is True


def test_compose_exists_real_absent(tmp_path):
    assert compose_exists("nonexistent", repo_root=str(tmp_path)) is False


# --- container_running ---

def test_container_running_no_compose_returns_false():
    assert container_running(None) is False


def test_container_running_docker_not_found():
    with mock.patch("subprocess.run", side_effect=FileNotFoundError):
        assert container_running("forge-turbo") is False


def test_container_running_match_in_output():
    out = "forge-turbo\n" * 3
    fake_result = mock.Mock(stdout=out)
    with mock.patch("subprocess.run", return_value=fake_result):
        assert container_running("forge-turbo") is True


# --- probe_api_auth ---

def test_probe_api_auth_n_a_when_none():
    assert probe_api_auth(None) == "N/A"


def test_probe_api_auth_protected_on_401():
    with mock.patch(
        "security.audit_exposed_services.http_probe", return_value=(401, {})
    ):
        assert probe_api_auth("/sdapi/v1/options") == "PROTECTED"


def test_probe_api_auth_open_on_200():
    with mock.patch(
        "security.audit_exposed_services.http_probe", return_value=(200, {})
    ):
        assert probe_api_auth("/sdapi/v1/options") == "OPEN"


def test_probe_api_auth_err_on_unexpected():
    with mock.patch(
        "security.audit_exposed_services.http_probe", return_value=(500, {})
    ):
        assert probe_api_auth("/sdapi/v1/options") == "ERR(500)"


# --- classify_subdomain: round-trip OUTPUT-content (L498) ---
# The substance: a finding dict is the audit's "output content". Per L498,
# tests MUST assert on the output data, not just on detection booleans.

def test_classify_no_dns_when_dns_fails():
    with mock.patch("security.audit_exposed_services.dns_resolves", _no_dns):
        f = classify_subdomain("ghost.invalid", "ghost", None)
    assert f["category"] == "NO-DNS"
    assert f["dns_resolves"] is False
    assert f["dns_ip"] is None


def test_classify_orphelin_dns_dns_resolves_but_no_compose():
    with mock.patch("security.audit_exposed_services.dns_resolves", _dns_ok), \
         mock.patch("security.audit_exposed_services.http_probe", _http_ok), \
         mock.patch("security.audit_exposed_services.compose_exists", _compose_no), \
         mock.patch("security.audit_exposed_services.container_running", lambda c: False):
        f = classify_subdomain("ghost.text-gen.myia.io", "ghost-text", None)
    assert f["category"] == "ORPHELIN-DNS"
    assert f["dns_resolves"] is True
    assert f["compose_exists"] is False
    assert f["container_running"] is False


def test_classify_orphelin_start_compose_but_container_not_running():
    with mock.patch("security.audit_exposed_services.dns_resolves", _dns_ok), \
         mock.patch("security.audit_exposed_services.http_probe", _http_502), \
         mock.patch("security.audit_exposed_services.compose_exists", _compose_yes), \
         mock.patch("security.audit_exposed_services.container_running", lambda c: False):
        f = classify_subdomain("forge.myia.io", "forge-turbo", "/sdapi/v1/options")
    assert f["category"] == "ORPHELIN-START"
    assert f["compose_exists"] is True
    assert f["container_running"] is False
    assert f["http_external"] == 502  # substance: 502 reverse-proxy response


def test_classify_api_leak_when_container_up_but_api_open():
    with mock.patch("security.audit_exposed_services.dns_resolves", _dns_ok), \
         mock.patch("security.audit_exposed_services.http_probe", _http_ok), \
         mock.patch("security.audit_exposed_services.compose_exists", _compose_yes), \
         mock.patch("security.audit_exposed_services.container_running", _container_running), \
         mock.patch("security.audit_exposed_services.probe_api_auth", return_value="OPEN"):
        f = classify_subdomain("forge.myia.io", "forge-turbo", "/sdapi/v1/options")
    assert f["category"] == "API-LEAK"
    assert f["api_auth"] == "OPEN"
    assert f["container_running"] is True
    assert f["redirect"].endswith("/login")  # UI has login, but API leaks


def test_classify_auth_ok_when_container_up_and_api_protected():
    with mock.patch("security.audit_exposed_services.dns_resolves", _dns_ok), \
         mock.patch("security.audit_exposed_services.http_probe", _http_ok), \
         mock.patch("security.audit_exposed_services.compose_exists", _compose_yes), \
         mock.patch("security.audit_exposed_services.container_running", _container_running), \
         mock.patch("security.audit_exposed_services.probe_api_auth", return_value="PROTECTED"):
        f = classify_subdomain("forge.myia.io", "forge-turbo", "/sdapi/v1/options")
    assert f["category"] == "AUTH-OK"
    assert f["api_auth"] == "PROTECTED"
    assert f["container_running"] is True


# --- run_audit (integration-shaped) ---

def test_run_audit_returns_list_of_findings():
    fake_findings = [
        {"subdomain": "a", "category": "ORPHELIN-START", "dns_resolves": True, "dns_ip": "1.2.3.4",
         "http_external": 502, "compose_exists": True, "container_running": False,
         "api_auth": "N/A", "redirect": "", "server": ""},
    ]
    with mock.patch("security.audit_exposed_services.classify_subdomain", return_value=fake_findings[0]):
        out = run_audit(tier=[("a.myia.io", "a", None)])
    assert isinstance(out, list)
    assert len(out) == 1
    assert out[0]["category"] == "ORPHELIN-START"


# --- render_markdown round-trip ---

def test_render_markdown_contains_table_and_categories():
    findings = [
        {"subdomain": "a.myia.io", "category": "AUTH-OK", "dns_resolves": True, "dns_ip": "1.2.3.4",
         "http_external": 200, "compose_exists": True, "container_running": True,
         "api_auth": "PROTECTED", "redirect": "/login", "server": "Gradio"},
        {"subdomain": "b.myia.io", "category": "API-LEAK", "dns_resolves": True, "dns_ip": "1.2.3.4",
         "http_external": 200, "compose_exists": True, "container_running": True,
         "api_auth": "OPEN", "redirect": "/login", "server": "Gradio"},
    ]
    md = render_markdown(findings)
    assert "# Audit `*.myia.io`" in md
    assert "| Subdomain |" in md
    assert "`a.myia.io`" in md
    assert "**AUTH-OK**" in md
    assert "**API-LEAK**" in md
    assert "## Légende catégories" in md


# --- DEFAULT_TIER smoke check ---

def test_default_tier_covers_forge_sdnext_and_text_gen():
    """Smoke test: ensure DEFAULT_TIER covers forge-turbo + sdnext + 4x text-gen."""
    subdomains = [entry[0] for entry in DEFAULT_TIER]
    assert "stable-diffusion-webui-forge.myia.io" in subdomains
    assert "sdnext.myia.io" in subdomains
    text_gen = [s for s in subdomains if "text-generation-webui.myia.io" in s]
    assert len(text_gen) == 4  # micro/mini/medium/large


# --- API_TIER (c.615) — round-trip OUTPUT-content (L498) ---
# Each test asserts on the dict/finding shape produced by the new code path,
# not just detection booleans. Tests use mock fixtures so they don't depend
# on whether whisper-api containers are actually running on the worker machine.

def test_api_tier_covers_all_16_apis_from_issue_16():
    """API_TIER must cover the 9 services in issue #16 §APIs nécessitant tokens
    (whisper/tts/musicgen/demucs/mcp-tools/skagents/embeddings/qdrant/search)
    plus adjacent compose-driven services (comfyui-qwen/comfyui-video/orchestrator).
    """
    subdomains = [entry[0] for entry in API_TIER]
    # issue #16 §APIs (must-haves):
    for required in ("whisper-api.myia.io", "tts-api.myia.io", "musicgen-api.myia.io",
                     "demucs-api.myia.io", "mcp-tools.myia.io", "skagents.myia.io",
                     "embeddings.myia.io", "qdrant.myia.io", "search.myia.io"):
        assert required in subdomains, f"missing required service {required}"
    # Adjacent compose-driven services:
    for adjacent in ("comfyui-qwen.myia.io", "comfyui-video.myia.io",
                     "orchestrator.myia.io"):
        assert adjacent in subdomains, f"missing adjacent compose {adjacent}"


def test_api_tier_each_entry_has_local_port_int():
    """Every API_TIER entry must be a 4-tuple with explicit local_port (issue #16
    category spans many different backend ports — Whisper=8190, TTS=8191, …)."""
    for entry in API_TIER:
        assert len(entry) == 4, f"entry not 4-tuple: {entry!r}"
        subdomain, compose_dir, api_endpoint, port = entry
        assert isinstance(port, int), f"port not int in {entry!r}"
        # ORPHELIN-DNS external entries use port=0 as skip-sentinel
        if compose_dir is None:
            assert port == 0, f"ORPHELIN-DNS entry {entry!r} must use port=0"


def test_orphelin_dns_external_services_have_no_compose():
    """5 external services (mcp-tools/skagents/embeddings/qdrant/search) have
    no compose_dir — they fall into ORPHELIN-DNS when DNS resolves but no
    compose file exists in this repo. Round-trip on actual shape."""
    externals = [entry for entry in API_TIER if entry[0]
                 in ("mcp-tools.myia.io", "skagents.myia.io",
                     "embeddings.myia.io", "qdrant.myia.io", "search.myia.io")]
    assert len(externals) == 5
    for entry in externals:
        assert entry[1] is None, f"{entry[0]} must have compose_dir=None"
        assert entry[2] is None, f"{entry[0]} must have api_endpoint=None"
        assert entry[3] == 0, f"{entry[0]} must have local_port=0 (skip sentinel)"


def test_normalize_entry_3_tuple_promotes_to_4_with_default_port():
    """Backward compat: legacy 3-tuple entries (c.442) must still work — promote
    to 4-tuple with DEFAULT_LOCAL_PORT (=1111, forge-turbo)."""
    promoted = normalize_entry(("forge.myia.io", "forge-turbo", "/sdapi/v1/options"))
    assert len(promoted) == 4
    assert promoted[3] == DEFAULT_LOCAL_PORT


def test_normalize_entry_4_tuple_passes_through():
    """4-tuple entries must pass through unchanged."""
    entry = ("whisper-api.myia.io", "whisper-api", "/health", 8190)
    assert normalize_entry(entry) == entry


def test_normalize_entry_rejects_invalid_arity():
    """Anything other than 3- or 4-tuple must raise ValueError loudly."""
    import pytest
    with pytest.raises(ValueError, match="TierEntry must be 3- or 4-tuple"):
        normalize_entry(("only", "two"))
    with pytest.raises(ValueError, match="TierEntry must be 3- or 4-tuple"):
        normalize_entry(("one",))


def test_probe_api_auth_port_zero_returns_na():
    """ORPHELIN-DNS external entries use port=0 as the skip-sentinel. The
    probe must short-circuit to 'N/A' without contacting localhost."""
    assert probe_api_auth(None, port=0) == "N/A"
    assert probe_api_auth("/some/endpoint", port=0) == "N/A"


def test_run_audit_api_tier_returns_findings_with_local_port_set():
    """When run_audit is called with API_TIER, each finding must include
    local_port field (round-trip on new c.615 output key). Mocks prevent
    real network/probes."""
    fake_finding_whisper = {
        "subdomain": "whisper-api.myia.io", "category": "AUTH-OK",
        "dns_resolves": True, "dns_ip": "82.66.89.184",
        "http_external": 200, "compose_exists": True,
        "container_running": True, "api_auth": "PROTECTED",
        "redirect": "", "server": "Gradio", "local_port": 8190,
        "compose_dir": "whisper-api",
    }
    fake_finding_external = {
        "subdomain": "qdrant.myia.io", "category": "ORPHELIN-DNS",
        "dns_resolves": True, "dns_ip": "82.66.89.184",
        "http_external": 200, "compose_exists": False,
        "container_running": False, "api_auth": "N/A",
        "redirect": "", "server": "IIS", "local_port": 0,
        "compose_dir": None,
    }
    with mock.patch(
        "security.audit_exposed_services.classify_subdomain",
        side_effect=[fake_finding_whisper, fake_finding_external],
    ):
        out = run_audit(tier=[("whisper-api.myia.io", "whisper-api", "/health", 8190),
                              ("qdrant.myia.io", None, None, 0)])
    assert len(out) == 2
    assert out[0]["local_port"] == 8190  # normal service
    assert out[0]["compose_dir"] == "whisper-api"
    assert out[1]["local_port"] == 0     # ORPHELIN-DNS sentinel
    assert out[1]["compose_dir"] is None


def test_render_markdown_api_tier_includes_port_column():
    """The c.615 markdown report must include the new 'Port' column and label
    the API tier accordingly. Round-trip on output content (L498)."""
    findings = [
        {"subdomain": "whisper-api.myia.io", "category": "AUTH-OK",
         "dns_resolves": True, "dns_ip": "82.66.89.184",
         "http_external": 200, "compose_exists": True,
         "container_running": True, "api_auth": "PROTECTED",
         "redirect": "/login", "server": "Gradio",
         "local_port": 8190, "compose_dir": "whisper-api"},
        {"subdomain": "qdrant.myia.io", "category": "ORPHELIN-DNS",
         "dns_resolves": True, "dns_ip": "82.66.89.184",
         "http_external": 200, "compose_exists": False,
         "container_running": False, "api_auth": "N/A",
         "redirect": "", "server": "IIS",
         "local_port": 0, "compose_dir": None},
    ]
    md = render_markdown(findings, tier_name="tier API (compose-driven + ORPHELIN-DNS)")
    assert "# Audit `*.myia.io`" in md
    assert "tier API" in md
    assert "| Port |" in md  # new column header
    assert "8190" in md     # concrete port
    assert "—" in md        # ORPHELIN-DNS port placeholder


def test_webui_tier_alias_matches_default_tier_identity():
    """Rétro-compat: WEBUI_TIER must be the same object as DEFAULT_TIER (c.442
    callers referencing either name see the same data)."""
    assert WEBUI_TIER is DEFAULT_TIER
