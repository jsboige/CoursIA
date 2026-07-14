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
    classify_subdomain,
    compose_exists,
    container_running,
    dns_resolves,
    http_probe,
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
