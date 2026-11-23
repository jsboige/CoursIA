"""Tests for the WSL distribution detection of the Lean setup chain (#21611).

`setup_lean4_all.py` used to take the FIRST line of `wsl -l -q` as the target
distribution. On a machine with Docker Desktop installed, that first line is
`docker-desktop` -- a container without bash -- and the Lean chain then died
with an opaque `127` (`/bin/sh: bash: not found`).

These tests drive `_detect_wsl_distro()` with a faked `subprocess.run`: the
listing is provided, and the probe of each candidate is answered explicitly.
"""
from __future__ import annotations

import importlib.util
import subprocess
import sys
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
MODULE_PATH = REPO_ROOT / "scripts" / "lean" / "setup_lean4_all.py"


def _load_module():
    spec = importlib.util.spec_from_file_location("setup_lean4_all", MODULE_PATH)
    module = importlib.util.module_from_spec(spec)
    sys.modules["setup_lean4_all"] = module
    spec.loader.exec_module(module)
    return module


dl = _load_module()


class _FakeRun:
    """Stand-in for ``subprocess.run`` answering the listing and the probes."""

    def __init__(self, listing: bytes, probe_rc: dict[str, int]):
        self.listing = listing
        self.probe_rc = probe_rc
        self.calls: list[list[str]] = []

    def __call__(self, args, **kwargs):
        self.calls.append(list(args))
        if args[:3] == ["wsl", "-l", "-q"]:
            return subprocess.CompletedProcess(args, 0, self.listing, b"")
        # probe: wsl -d <name> -- bash -lc true
        name = args[2]
        rc = self.probe_rc.get(name, 0)
        return subprocess.CompletedProcess(args, rc, b"", b"")


def _detect(monkeypatch, listing: str, probe_rc: dict[str, int] | None = None):
    fake = _FakeRun(listing.encode("utf-16-le"), probe_rc or {})
    monkeypatch.setattr(dl.subprocess, "run", fake)
    chosen = dl._detect_wsl_distro()
    return chosen, fake


def test_docker_desktop_is_not_selected(monkeypatch):
    """The measured case: `docker-desktop` is listed first on a Docker Desktop
    machine (2026-10-20, poste myia-po-2028)."""
    chosen, fake = _detect(
        monkeypatch,
        listing="docker-desktop\nUbuntu\nUbuntu-24.04\n",
        probe_rc={"Ubuntu": 0, "Ubuntu-24.04": 0},
    )
    assert chosen == "Ubuntu"
    # docker-desktop is never even probed
    assert all("docker-desktop" not in call for call in fake.calls)


def test_user_distro_is_selected_when_listed_first(monkeypatch):
    """Control: without Docker Desktop, the first user distro is kept."""
    chosen, _ = _detect(
        monkeypatch,
        listing="Ubuntu\nUbuntu-24.04\n",
        probe_rc={"Ubuntu": 0},
    )
    assert chosen == "Ubuntu"


def test_distro_without_bash_is_skipped_for_the_next_one(monkeypatch):
    """A distribution that does not answer the bash probe is not installed into."""
    chosen, fake = _detect(
        monkeypatch,
        listing="Ubuntu\nDebian\n",
        probe_rc={"Ubuntu": 1, "Debian": 0},
    )
    assert chosen == "Debian"
    assert ["wsl", "-d", "Ubuntu", "--", "bash", "-lc", "true"] in fake.calls


def test_default_is_the_first_usable_candidate_when_no_probe_answers(monkeypatch):
    """No candidate answers the probe: keep the first USER distro, never
    docker-desktop (and never a name that does not exist on the machine)."""
    chosen, _ = _detect(
        monkeypatch,
        listing="docker-desktop\nDebian\n",
        probe_rc={"Debian": 1},
    )
    assert chosen == "Debian"


def test_fallback_is_ubuntu_when_no_user_distro_exists(monkeypatch):
    """Only non-user distributions: the historical fallback applies."""
    chosen, _ = _detect(
        monkeypatch,
        listing="docker-desktop\ndocker-desktop-data\n",
        probe_rc={},
    )
    assert chosen == "Ubuntu"


def test_utf16_listing_still_decodes(monkeypatch):
    """Regression: the listing is UTF-16LE with a BOM on recent Windows."""
    listing = "docker-desktop\nUbuntu\n".encode("utf-16")
    fake = _FakeRun(listing, {"Ubuntu": 0})
    monkeypatch.setattr(dl.subprocess, "run", fake)
    assert dl._detect_wsl_distro() == "Ubuntu"


def test_probe_failure_is_treated_as_not_usable(monkeypatch):
    """A probe that raises (WSL missing, timeout) must not crash detection."""

    def _boom(args, **kwargs):
        if args[:3] == ["wsl", "-l", "-q"]:
            return subprocess.CompletedProcess(args, 0, "Ubuntu\n".encode("utf-16-le"), b"")
        raise OSError("wsl exploded")

    monkeypatch.setattr(dl.subprocess, "run", _boom)
    assert dl._detect_wsl_distro() == "Ubuntu"


@pytest.mark.parametrize(
    "name,expected",
    [
        ("docker-desktop", False),
        ("docker-desktop-data", False),
        ("Docker-Desktop", False),
        ("Ubuntu", True),
        ("Ubuntu-24.04", True),
        ("Debian", True),
        ("", False),
    ],
)
def test_is_user_distro(name, expected):
    assert dl._is_user_distro(name) is expected
