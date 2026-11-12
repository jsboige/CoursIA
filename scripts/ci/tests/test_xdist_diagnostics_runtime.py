"""Vérifie le diagnostic sur de vrais workers et son nettoyage."""
import os
import subprocess
import sys
from pathlib import Path

WATCHDOG = Path(__file__).resolve().parents[1] / "xdist_watchdog.py"


def _run(tmp_path, source):
    test = tmp_path / "test_sample.py"
    test.write_text(source, encoding="utf-8")
    temp = tmp_path / "temp"
    temp.mkdir()
    env = dict(os.environ, TMPDIR=str(temp))
    pytest = str(Path(sys.executable).with_name("pytest"))
    result = subprocess.run(
        [sys.executable, str(WATCHDOG), "--idle-limit", "2", "--", pytest,
         str(test), "-n", "1", "-q", "--max-worker-restart=0"],
        capture_output=True, text=True, env=env, timeout=30,
    )
    assert not list(temp.glob("coursia-xdist-*"))
    return result


def test_crash_worker(tmp_path):
    result = _run(tmp_path, "import os\ndef test_crash():\n    os._exit(7)\n")
    assert result.returncode != 0
    assert "XDIST-DIAGNOSTIC gw0:" in result.stdout
    assert "test_crash" in result.stdout


def test_timeout_worker(tmp_path):
    result = _run(tmp_path, "import time\ndef test_hang():\n    time.sleep(30)\n")
    assert result.returncode != 0
    assert "XDIST-DIAGNOSTIC gw0:" in result.stdout
    assert "test_hang" in result.stdout


def test_success_preserves_exit_and_cleans(tmp_path):
    result = _run(tmp_path, "def test_ok():\n    assert True\n")
    assert result.returncode == 0
    assert "XDIST-DIAGNOSTIC" not in result.stdout


def test_signal_cleans(tmp_path):
    import signal
    import time

    test = tmp_path / "test_signal.py"
    test.write_text("import time\ndef test_wait():\n    time.sleep(30)\n", encoding="utf-8")
    temp = tmp_path / "temp"
    temp.mkdir()
    env = dict(os.environ, TMPDIR=str(temp))
    pytest = str(Path(sys.executable).with_name("pytest"))
    proc = subprocess.Popen(
        [sys.executable, str(WATCHDOG), "--idle-limit", "20", "--", pytest,
         str(test), "-n", "1", "-q"], stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, text=True, env=env,
    )
    deadline = time.monotonic() + 15
    while time.monotonic() < deadline:
        if list(temp.glob("coursia-xdist-*/gw0")):
            break
        time.sleep(0.05)
    else:
        proc.kill()
        proc.communicate(timeout=10)
        raise AssertionError("worker non démarré")
    proc.send_signal(signal.SIGTERM)
    proc.communicate(timeout=15)
    assert proc.returncode != 0
    assert not list(temp.glob("coursia-xdist-*"))


def test_user_plugin_name_is_not_masked(tmp_path):
    plugin_dir = tmp_path / "user_plugins"
    plugin_dir.mkdir()
    (plugin_dir / "xdist_diagnostics.py").write_text(
        "import os\ndef pytest_configure(config):\n"
        "    open(os.environ['USER_PLUGIN_MARKER'], 'w').write('loaded')\n",
        encoding="utf-8",
    )
    test = tmp_path / "test_plugin.py"
    test.write_text("def test_ok():\n    assert True\n", encoding="utf-8")
    marker = tmp_path / "user-plugin-loaded"
    temp = tmp_path / "temp"
    temp.mkdir()
    env = dict(os.environ, TMPDIR=str(temp), PYTHONPATH=str(plugin_dir),
               PYTEST_PLUGINS="xdist_diagnostics", USER_PLUGIN_MARKER=str(marker))
    pytest = str(Path(sys.executable).with_name("pytest"))
    result = subprocess.run(
        [sys.executable, str(WATCHDOG), "--idle-limit", "10", "--", pytest,
         str(test), "-n", "1", "-q"], capture_output=True, text=True,
        env=env, timeout=30,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    assert marker.read_text() == "loaded"
    assert not list(temp.glob("coursia-xdist-*"))


def test_invalid_utf8_does_not_prevent_timeout(tmp_path):
    source = (
        "import os, pathlib, time\n"
        "def test_invalid():\n"
        "    p = pathlib.Path(os.environ['COURSIA_XDIST_DIAGNOSTICS']) / 'gw0'\n"
        "    p.write_bytes(b'partial-\\xff')\n"
        "    time.sleep(30)\n"
    )
    result = _run(tmp_path, source)
    assert result.returncode != 0
    assert "XDIST-WATCHDOG" in result.stdout
    assert "partial-\ufffd" in result.stdout
