#!/usr/bin/env python3
"""Pytest suite for `SymbolicAI/Argument_Analysis/install_jdk_portable.py`.

Co-located with the module under `Argument_Analysis/`. CPU-only, no network,
no real JDK download, no real JDK install. The module imports only stdlib at
top level (os, platform, pathlib, subprocess, zipfile, urllib.request, logging,
sys) and lazily imports `tarfile` inside the Linux/MacOS extraction branch, so
it loads cleanly without optional deps.

The module is the portable-JDK bootstrap for Argument Analysis (downloads Azul
Zulu JDK 17.0.11 if no system JDK is available) and had 0 dedicated Python test
coverage before this PR.

Strategy: every network/subprocess/filesystem side effect is mocked.
`urllib.request.urlretrieve` is replaced with a stub that writes a real in-memory
zip / tar.gz (so zipfile.extractall / tarfile.extractall exercise real code paths)
into a tmp_path-relative archive; `subprocess.run` is replaced with a stub that
returns a captured-result object (or raises FileNotFoundError / TimeoutExpired);
`platform.system` is pinned per test; `JDK_PORTABLE_DIR` is redirected to a
tmp_path subdir so no directory is ever created next to the module file.
"""
from __future__ import annotations

import io
import importlib.util
import logging
import os
import tarfile
import zipfile
from pathlib import Path
from types import SimpleNamespace

import pytest

# Load the module by path (lives under Argument_Analysis/, stdlib-only at import
# time -> no sys.path manipulation, no package-relative imports).
_MODULE_PATH = Path(__file__).resolve().parent / "install_jdk_portable.py"
_spec = importlib.util.spec_from_file_location("install_jdk_portable", _MODULE_PATH)
jdk = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(jdk)


def _ok_run(*args, **kwargs):
    """Fake subprocess.run that succeeds and prints version to stderr."""
    return SimpleNamespace(returncode=0, stderr="openjdk version 17.0.1\n", stdout="")


def _run_raises(exc):
    """Build a fake subprocess.run that raises `exc`."""

    def _raiser(*args, **kwargs):
        raise exc

    return _raiser


# --------------------------------------------------------------------------
# Module constants
# --------------------------------------------------------------------------


def test_jdk_urls_cover_three_platforms():
    assert set(jdk.JDK_URLS.keys()) == {"Windows", "Linux", "Darwin"}
    # All URLs point at Azul Zulu CDN with the pinned build.
    for plat, url in jdk.JDK_URLS.items():
        assert url.startswith("https://cdn.azul.com/zulu/bin/")
        assert jdk.JDK_BUILD in url


def test_jdk_portable_dir_is_sibling_of_module():
    assert isinstance(jdk.JDK_PORTABLE_DIR, Path)
    assert jdk.JDK_PORTABLE_DIR.name == "jdk-17-portable"
    assert jdk.JDK_PORTABLE_DIR.parent == _MODULE_PATH.parent


# --------------------------------------------------------------------------
# setup_logging
# --------------------------------------------------------------------------


def test_setup_logging_returns_named_logger():
    logger = jdk.setup_logging()
    assert isinstance(logger, logging.Logger)
    assert logger.name == "JDKPortable"


def test_setup_logging_is_idempotent_returns_named_logger():
    # logging.basicConfig is idempotent: it only configures root when root has
    # no handlers (it is a no-op under pytest, where root already has the caplog
    # handler). Calling setup_logging multiple times must not raise and must keep
    # returning the JDKPortable named logger.
    logger1 = jdk.setup_logging()
    logger2 = jdk.setup_logging()
    assert logger1.name == "JDKPortable"
    assert logger2.name == "JDKPortable"


# --------------------------------------------------------------------------
# detect_system_jdk
# --------------------------------------------------------------------------


def test_detect_system_jdk_true_when_java_version_ok(monkeypatch):
    monkeypatch.setattr(jdk.subprocess, "run", _ok_run)
    monkeypatch.delenv("JAVA_HOME", raising=False)
    assert jdk.detect_system_jdk() is True


def test_detect_system_jdk_false_when_java_not_found_and_no_java_home(monkeypatch):
    # `java` command missing AND no JAVA_HOME -> falls through to False.
    monkeypatch.setattr(jdk.subprocess, "run", _run_raises(FileNotFoundError))
    monkeypatch.delenv("JAVA_HOME", raising=False)
    assert jdk.detect_system_jdk() is False


def test_detect_system_jdk_false_when_java_returns_nonzero(monkeypatch):
    monkeypatch.setattr(
        jdk.subprocess,
        "run",
        lambda *a, **k: SimpleNamespace(returncode=1, stderr="error", stdout=""),
    )
    monkeypatch.delenv("JAVA_HOME", raising=False)
    assert jdk.detect_system_jdk() is False


def test_detect_system_jdk_true_via_java_home_when_java_missing(monkeypatch, tmp_path):
    # `java` command not found, but JAVA_HOME points at a real JDK layout.
    monkeypatch.setattr(jdk.subprocess, "run", _run_raises(FileNotFoundError))
    home = tmp_path / "jdk"
    (home / "bin").mkdir(parents=True)
    (home / "bin" / "java.exe").write_bytes(b"")
    monkeypatch.setenv("JAVA_HOME", str(home))
    monkeypatch.setattr(jdk.platform, "system", lambda: "Windows")
    assert jdk.detect_system_jdk() is True


# --------------------------------------------------------------------------
# detect_portable_jdk
# --------------------------------------------------------------------------


def test_detect_portable_jdk_none_when_dir_absent(monkeypatch, tmp_path):
    monkeypatch.setattr(jdk, "JDK_PORTABLE_DIR", tmp_path / "absent")
    monkeypatch.setattr(jdk.platform, "system", lambda: "Windows")
    assert jdk.detect_portable_jdk() is None


def test_detect_portable_jdk_finds_java_exe(monkeypatch, tmp_path):
    portable = tmp_path / "jdk-17-portable"
    home = portable / "zulu-jdk17"
    (home / "bin").mkdir(parents=True)
    (home / "bin" / "java.exe").write_bytes(b"")
    monkeypatch.setattr(jdk, "JDK_PORTABLE_DIR", portable)
    monkeypatch.setattr(jdk.platform, "system", lambda: "Windows")
    result = jdk.detect_portable_jdk()
    assert result == home


def test_detect_portable_jdk_none_when_dir_empty(monkeypatch, tmp_path):
    portable = tmp_path / "jdk-17-portable"
    portable.mkdir(parents=True)
    monkeypatch.setattr(jdk, "JDK_PORTABLE_DIR", portable)
    monkeypatch.setattr(jdk.platform, "system", lambda: "Windows")
    assert jdk.detect_portable_jdk() is None


# --------------------------------------------------------------------------
# download_and_install_portable_jdk
# --------------------------------------------------------------------------


def _fake_zip_urlretrieve(zip_bytes_for, tmp_path):
    """Return a urlretrieve stub writing a zip holding jdk-17/bin/java.exe."""

    def _retrieve(url, path, hook=None):
        buf = io.BytesIO()
        with zipfile.ZipFile(buf, "w") as zf:
            zf.writestr("jdk-17/bin/java.exe", b"")
        Path(path).write_bytes(buf.getvalue())

    return _retrieve


def test_download_and_install_windows(monkeypatch, tmp_path):
    portable = tmp_path / "jdk-17-portable"
    monkeypatch.setattr(jdk, "JDK_PORTABLE_DIR", portable)
    monkeypatch.setattr(jdk.platform, "system", lambda: "Windows")
    monkeypatch.setattr(jdk.urllib.request, "urlretrieve", _fake_zip_urlretrieve(None, tmp_path))
    # The archive is written relative to CWD; redirect CWD so it lands in tmp.
    monkeypatch.chdir(tmp_path)

    result = jdk.download_and_install_portable_jdk()
    assert result == portable / "jdk-17"
    assert (portable / "jdk-17" / "bin" / "java.exe").exists()
    # Archive cleaned up after extraction.
    assert not (tmp_path / "jdk-portable.zip").exists()


def test_download_and_install_linux_tar_gz(monkeypatch, tmp_path):
    portable = tmp_path / "jdk-17-portable"
    monkeypatch.setattr(jdk, "JDK_PORTABLE_DIR", portable)
    monkeypatch.setattr(jdk.platform, "system", lambda: "Linux")
    # Build a tar.gz holding jdk-17/bin/java.
    def _retrieve_tar(url, path, hook=None):
        buf = io.BytesIO()
        info = tarfile.TarInfo(name="jdk-17/bin/java")
        info.size = 0
        with tarfile.open(fileobj=buf, mode="w:gz") as tf:
            tf.addfile(info, io.BytesIO(b""))
        Path(path).write_bytes(buf.getvalue())

    monkeypatch.setattr(jdk.urllib.request, "urlretrieve", _retrieve_tar)
    monkeypatch.chdir(tmp_path)

    result = jdk.download_and_install_portable_jdk()
    assert result == portable / "jdk-17"
    assert (portable / "jdk-17" / "bin" / "java").exists()
    assert not (tmp_path / "jdk-portable.tar.gz").exists()


def test_download_and_install_unsupported_platform(monkeypatch):
    monkeypatch.setattr(jdk.platform, "system", lambda: "Solaris")
    assert jdk.download_and_install_portable_jdk() is None


def test_download_and_install_returns_none_on_urlretrieve_failure(monkeypatch, tmp_path):
    portable = tmp_path / "jdk-17-portable"
    monkeypatch.setattr(jdk, "JDK_PORTABLE_DIR", portable)
    monkeypatch.setattr(jdk.platform, "system", lambda: "Windows")
    monkeypatch.setattr(jdk.urllib.request, "urlretrieve", _run_raises(OSError("network down")))
    monkeypatch.chdir(tmp_path)

    assert jdk.download_and_install_portable_jdk() is None


# --------------------------------------------------------------------------
# setup_java_environment
# --------------------------------------------------------------------------


def test_setup_java_environment_sets_java_home(monkeypatch, tmp_path):
    jdk_home = tmp_path / "fake-jdk"
    (jdk_home / "bin").mkdir(parents=True)
    (jdk_home / "bin" / "java.exe").write_bytes(b"")
    monkeypatch.delenv("JAVA_HOME", raising=False)
    monkeypatch.setenv("PATH", "/usr/bin")
    monkeypatch.setattr(jdk.platform, "system", lambda: "Windows")
    monkeypatch.setattr(jdk.subprocess, "run", _ok_run)

    assert jdk.setup_java_environment(jdk_home) is True
    assert os.environ["JAVA_HOME"] == str(jdk_home)


def test_setup_java_environment_prepends_bin_to_path(monkeypatch, tmp_path):
    jdk_home = tmp_path / "fake-jdk"
    (jdk_home / "bin").mkdir(parents=True)
    (jdk_home / "bin" / "java.exe").write_bytes(b"")
    monkeypatch.delenv("JAVA_HOME", raising=False)
    monkeypatch.setenv("PATH", "/usr/bin")
    monkeypatch.setattr(jdk.platform, "system", lambda: "Windows")
    monkeypatch.setattr(jdk.subprocess, "run", _ok_run)

    jdk.setup_java_environment(jdk_home)
    expected_bin = str(jdk_home / "bin")
    assert os.environ["PATH"].startswith(expected_bin)


def test_setup_java_environment_false_when_version_test_fails(monkeypatch, tmp_path):
    jdk_home = tmp_path / "fake-jdk"
    (jdk_home / "bin").mkdir(parents=True)
    (jdk_home / "bin" / "java.exe").write_bytes(b"")
    monkeypatch.delenv("JAVA_HOME", raising=False)
    monkeypatch.setenv("PATH", "/usr/bin")
    monkeypatch.setattr(jdk.platform, "system", lambda: "Windows")
    monkeypatch.setattr(
        jdk.subprocess, "run",
        lambda *a, **k: SimpleNamespace(returncode=1, stderr="err", stdout=""),
    )

    assert jdk.setup_java_environment(jdk_home) is False


def test_setup_java_environment_false_on_timeout(monkeypatch, tmp_path):
    jdk_home = tmp_path / "fake-jdk"
    (jdk_home / "bin").mkdir(parents=True)
    (jdk_home / "bin" / "java.exe").write_bytes(b"")
    monkeypatch.delenv("JAVA_HOME", raising=False)
    monkeypatch.setenv("PATH", "/usr/bin")
    monkeypatch.setattr(jdk.platform, "system", lambda: "Windows")
    monkeypatch.setattr(jdk.subprocess, "run", _run_raises(jdk.subprocess.TimeoutExpired))

    assert jdk.setup_java_environment(jdk_home) is False


# --------------------------------------------------------------------------
# main
# --------------------------------------------------------------------------


def test_main_true_when_system_jdk_available(monkeypatch):
    monkeypatch.setattr(jdk, "detect_system_jdk", lambda: True)
    # The two later probes must NOT be reached; verify by raising if called.
    monkeypatch.setattr(jdk, "detect_portable_jdk", lambda: (_ for _ in ()).throw(AssertionError()))
    assert jdk.main() is True


def test_main_true_when_portable_jdk_exists(monkeypatch, tmp_path):
    monkeypatch.setattr(jdk, "detect_system_jdk", lambda: False)
    monkeypatch.setattr(jdk, "detect_portable_jdk", lambda: tmp_path)
    monkeypatch.setattr(jdk, "setup_java_environment", lambda home: True)
    assert jdk.main() is True


def test_main_false_when_install_fails(monkeypatch):
    monkeypatch.setattr(jdk, "detect_system_jdk", lambda: False)
    monkeypatch.setattr(jdk, "detect_portable_jdk", lambda: None)
    monkeypatch.setattr(jdk, "download_and_install_portable_jdk", lambda: None)
    assert jdk.main() is False


# --------------------------------------------------------------------------
# get_java_home
# --------------------------------------------------------------------------


def test_get_java_home_returns_env_when_set(monkeypatch):
    monkeypatch.setenv("JAVA_HOME", "/opt/jdk-17")
    assert jdk.get_java_home() == "/opt/jdk-17"


def test_get_java_home_none_when_unset(monkeypatch):
    monkeypatch.delenv("JAVA_HOME", raising=False)
    assert jdk.get_java_home() is None
