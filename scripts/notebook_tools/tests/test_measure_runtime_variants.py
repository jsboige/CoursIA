"""Tests for scripts/notebook_tools/measure_runtime_variants.py.

The tool compares the wall-clock of a .NET notebook under several runtimes.
Two properties matter for the measurement to be trustworthy, and they are
pinned here without a live kernel:

* the **runtime proof** is read back from the file the probe cell wrote —
  the tool never trusts a name it did not observe;
* the **kernelspec name** follows the dotted ``.net-csharp*`` convention —
  a plain name adds ~5 s of startup per execution (measured: 17,5 s for
  ``mesure-net11`` against 12,4 s for ``.net-csharp-r11e``, identical
  content, same directory, interleaved, same proven runtime). The tool
  therefore refuses to *generate* a plain-named spec and warns when one is
  handed to it.

No live kernel, no network, no .NET runtime: the notebook execution is
mocked. Fast.
"""
import json
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import measure_runtime_variants as mrv  # noqa: E402


# --- kernelspec -------------------------------------------------------------

def test_generated_spec_is_dotted_and_carries_the_runtime_root(tmp_path):
    arm = mrv.parse_arm("net11=auto@" + str(tmp_path).replace("\\", "/"),
                        "C:/tools/dotnet-interactive.exe", tmp_path)
    assert arm["kernel"].startswith("."), "le nom doit suivre la convention pointée"
    assert arm["kernel"] == ".net-csharp-net11"
    assert arm["generated"] is True

    spec = json.loads((tmp_path / "kernels" / arm["kernel"] / "kernel.json").read_text(encoding="utf-8"))
    assert spec["env"]["DOTNET_ROOT"].endswith(str(tmp_path).replace("\\", "/"))
    assert spec["env"]["DOTNET_ROLL_FORWARD"] == "Major"
    assert spec["argv"][0] == "C:/tools/dotnet-interactive.exe"
    assert "{connection_file}" in spec["argv"]


def test_plain_kernel_name_is_reported(tmp_path, capsys):
    mrv.parse_arm("net10=.net-csharp", "C:/tools/dotnet-interactive.exe", tmp_path)
    assert "AVERTISSEMENT" not in capsys.readouterr().err

    mrv.parse_arm("net10=net-csharp-plain", "C:/tools/dotnet-interactive.exe", tmp_path)
    assert "AVERTISSEMENT" in capsys.readouterr().err


def test_malformed_arm_is_rejected(tmp_path):
    with pytest.raises(mrv.ArmError):
        mrv.parse_arm("sans-egal", "C:/tools/dotnet-interactive.exe", tmp_path)


# --- sonde runtime ---------------------------------------------------------

def test_probe_reads_the_runtime_back_from_the_file(tmp_path, monkeypatch):
    seen = tmp_path / "runtime_seen.txt"

    def fake_run(notebook, kernel, timeout, env):
        # La sonde ecrit ce que le noyau a reellement observe.
        seen.write_text("RUNTIME=.NET 11.0.0-rc.3.26522.148\nRUNTIMEVER=11.0.0\n",
                        encoding="utf-8")
        return {"cells_ok": 1, "cells_total": 1, "cells_errors": 0, "total_seconds": 1.0}

    monkeypatch.setattr(mrv, "run_notebook_tools", fake_run)
    runtime = mrv.probe_runtime(".net-csharp-r11", tmp_path, 30, {})
    assert runtime == ".NET 11.0.0-rc.3.26522.148"


def test_probe_fails_loudly_when_nothing_is_written(tmp_path, monkeypatch):
    monkeypatch.setattr(mrv, "run_notebook_tools",
                        lambda *a, **k: {"cells_ok": 0, "cells_total": 1, "cells_errors": 1})
    with pytest.raises(mrv.ArmError):
        mrv.probe_runtime(".net-csharp-r11", tmp_path, 30, {})


# --- lecture de la metrique -------------------------------------------------

def test_metrics_are_read_from_the_canonical_output():
    raw = ("\x1b[1m[08-Aspire-AsyncFFI-Dotnet.ipynb]\x1b[0m (kernel: .net-csharp)\n"
           "  [+] Executed 9 cells: 9 OK, 0 errors\n"
           "\n  Total time: 12.7s\n")
    parsed = mrv.ANSI_RE.sub("", raw)
    assert mrv.CELLS_RE.search(parsed).groups() == ("9", "9", "0")
    assert float(mrv.TOTAL_RE.search(parsed).group(1)) == 12.7


def test_probe_notebook_embeds_the_probe_path(tmp_path):
    probe_out = tmp_path / "runtime_seen.txt"
    nb_path = tmp_path / "sonde.ipynb"
    mrv.build_probe_notebook(nb_path, probe_out)
    nb = json.loads(nb_path.read_text(encoding="utf-8"))
    source = "".join(nb["cells"][0]["source"])
    assert "RuntimeInformation.FrameworkDescription" in source
    assert str(probe_out).replace("\\", "/") in source


# --- redaction --------------------------------------------------------------

def test_redact_paths_covers_both_separator_forms(monkeypatch, tmp_path):
    """Le home est masque quelle que soit l'ecriture du chemin.

    Defaut constate sur `scripts/results/net11_axis1_2026-10-30.json` : le
    `dotnet_root` d'un bras etait passe en slashes, la redaction ne comparait
    que la forme native et la valeur machine restait dans l'artefact.
    """
    home = tmp_path / "home"
    home.mkdir()
    monkeypatch.setattr(mrv.Path, "home", classmethod(lambda cls: home))
    monkeypatch.setattr(mrv.Path, "cwd", classmethod(lambda cls: tmp_path / "work"))

    slashed = str(home).replace("\\", "/") + "/.dotnet-r11"
    native = str(home) + "\\.dotnet-r11"

    assert mrv.redact_paths(slashed) == "~/.dotnet-r11"
    assert mrv.redact_paths(native) == "~/.dotnet-r11"
    assert "dotnet-r11" in mrv.redact_paths(slashed)  # le reste de la valeur survit

