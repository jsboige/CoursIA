"""Tests for scripts/notebook_tools/check_pr_dotnet_nuget_block.py

Issue #10024 Livrable 2 acceptance -- >=2 falsification tests proving silence
([gate-must-verify-detector-fp-before-wiring]) PLUS a CONTROLE POSITIF
OBLIGATOIRE: a gate that never fires is silent for the wrong reason (#8680).
These tests prove the advisory can actually fire (reference RED case: PR #10021
on App-13b) AND that it stays silent on the legitimate combinations.

Falsification cases that MUST be silent:
  1. .NET notebook WITH `#r "nuget:"` + body invoking RECOVERABLE-MACHINE -> SILENT
     (the nuget blocker genuinely can apply headless -> block may be legitimate).
  2. .NET notebook WITHOUT nuget + body NOT invoking any block -> SILENT.
  3. non-.NET notebook + body invoking a block -> SILENT (out of scope).

Pure functions on tmp_path notebooks -- no I/O on the real repo.
"""

import json
import sys
from pathlib import Path

_tools_dir = str(Path(__file__).resolve().parent.parent)
if _tools_dir not in sys.path:
    sys.path.insert(0, _tools_dir)

import check_pr_dotnet_nuget_block as mod  # noqa: E402


def _write_nb(path: Path, cells: list[dict], kernel: str = ".net-csharp") -> Path:
    nb = {
        "cells": cells,
        "metadata": {"kernelspec": {"name": kernel, "display_name": kernel}},
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    path.write_text(json.dumps(nb), encoding="utf-8")
    return path


def _code(source: str) -> dict:
    return {
        "cell_type": "code",
        "source": [source],
        "metadata": {},
        "execution_count": 1,
        "outputs": [],
    }


# Reference RED case body -- mirrors PR #10021 (the canonical anti-pattern):
# RECOVERABLE-MACHINE verdict + transplant, on App-13b which has 0 #r nuget.
BODY_10021 = (
    "## Re-exec verdict\n\n"
    "**RECOVERABLE-MACHINE (real kernel unavailable headless)**. "
    "Le notebook n'est pas executable localement (blocage nuget #r headless). "
    "Outputs produits via un projet console .NET auto-contenu (transplant), "
    "non committé dans le depot."
)


def test_reference_red_case_app13b_0_nuget_body_invokes_block(tmp_path: Path):
    """CONTROLE POSITIF: the reference case (PR #10021) MUST be flagged.
    App-13b contains 0 `#r "nuget:"`; the body invokes RECOVERABLE-MACHINE +
    headless + nuget + transplant -> the exact anti-pattern."""
    nb = tmp_path / "App-13b.ipynb"
    _write_nb(
        nb,
        [
            _code('var x = 1;'),
            _code('Console.WriteLine("hello");'),
        ],
        kernel=".net-csharp",
    )
    payload = mod.check_pr([str(nb)], BODY_10021)
    assert payload["summary"]["dotnet_block_without_nuget"] == 1
    assert payload["summary"]["dotnet_notebooks_checked"] == 1
    assert payload["summary"]["dotnet_notebooks_with_nuget"] == 0
    assert payload["summary"]["body_invokes_block"] is True
    entry = payload["notebooks"][0]
    assert entry["flagged"] is True
    assert entry["nuget_count"] == 0
    assert "recoverable-machine" in entry["body_block_keywords"]


def test_silence_dotnet_WITH_nuget_and_body_invokes_block(tmp_path: Path):
    """FALSIFICATION 1: a .NET notebook WITH `#r "nuget:"` + body invoking the
    block -> SILENT. The nuget blocker genuinely can apply headless, so the
    RECOVERABLE-MACHINE verdict may be legitimate. Flagging here = FP."""
    nb = tmp_path / "WithNuget.ipynb"
    _write_nb(
        nb,
        [
            _code('#r "nuget: GeneticSharp, 3.1.4"'),
            _code('using GeneticSharp;\nvar ga = new GeneticAlgorithm();'),
        ],
        kernel=".net-csharp",
    )
    payload = mod.check_pr([str(nb)], BODY_10021)
    assert payload["summary"]["dotnet_block_without_nuget"] == 0
    assert payload["summary"]["dotnet_notebooks_with_nuget"] == 1
    entry = payload["notebooks"][0]
    assert entry["flagged"] is False
    assert entry["nuget_count"] == 1


def test_silence_dotnet_WITHOUT_nuget_and_body_does_not_invoke_block(tmp_path: Path):
    """FALSIFICATION 2: a .NET notebook WITHOUT nuget + body that does NOT
    invoke any block -> SILENT. No dispense claimed -> nothing to flag."""
    nb = tmp_path / "PlainDotnet.ipynb"
    _write_nb(
        nb,
        [_code('Console.WriteLine("no nuget here");')],
        kernel=".net-csharp",
    )
    body = "Routine re-exec via notebook_tools.py execute --kernel .net-csharp. All cells green."
    payload = mod.check_pr([str(nb)], body)
    assert payload["summary"]["dotnet_block_without_nuget"] == 0
    assert payload["summary"]["body_invokes_block"] is False
    entry = payload["notebooks"][0]
    assert entry["flagged"] is False


def test_silence_non_dotnet_notebook_out_of_scope(tmp_path: Path):
    """FALSIFICATION 3: a non-.NET notebook (python3) + body invoking the block
    -> SILENT. The .NET blocker does not apply to python3 notebooks."""
    nb = tmp_path / "Python.ipynb"
    _write_nb(
        nb,
        [_code('print("python notebook")')],
        kernel="python3",
    )
    payload = mod.check_pr([str(nb)], BODY_10021)
    assert payload["summary"]["dotnet_block_without_nuget"] == 0
    assert payload["summary"]["dotnet_notebooks_checked"] == 0
    entry = payload["notebooks"][0]
    assert entry["flagged"] is False
    assert entry["status"] == "non-dotnet"


def test_nuget_ref_regex_matches_variants():
    """The `#r "nuget:"` regex must catch the real-world variants (versioned,
    spaced) so a notebook with a genuine nuget ref is not mis-flagged."""
    assert mod.NUGET_REF_RE.findall('#r "nuget: GeneticSharp"')
    assert mod.NUGET_REF_RE.findall('#r "nuget:GeneticSharp, 3.1.4"')
    assert mod.NUGET_REF_RE.findall('#r  "nuget: Google.OrTools"')
    # Must NOT match a plain DLL load or a comment.
    assert not mod.NUGET_REF_RE.findall('#r "System.Console"')
    assert not mod.NUGET_REF_RE.findall('// nuget is mentioned in a comment')


def test_stdio_variant_kernel_names_caught(tmp_path: Path):
    """All `.net*` kernel variants are in scope (.net-csharp, .net-fsharp,
    .net-powershell, .net-csharp-stdio). A non-.net name is not."""
    for kernel in (".net-csharp", ".net-fsharp", ".net-powershell", ".net-csharp-stdio"):
        nb = tmp_path / f"{kernel}.ipynb"
        _write_nb(nb, [_code('var x = 1;')], kernel=kernel)
        payload = mod.check_pr([str(nb)], BODY_10021)
        assert payload["summary"]["dotnet_notebooks_checked"] == 1, kernel
        assert payload["summary"]["dotnet_block_without_nuget"] == 1, kernel


def test_cli_always_exits_zero(tmp_path: Path, capsys):
    """Advisory contract (#10024 acceptance): the CLI NEVER exits non-zero,
    even when it flags. The signal is the label, not the exit code."""
    nb = tmp_path / "App.ipynb"
    _write_nb(nb, [_code('var x = 1;')], kernel=".net-csharp")
    body_file = tmp_path / "body.md"
    body_file.write_text(BODY_10021, encoding="utf-8")
    rc = mod.main(["--paths", str(nb), "--pr-body-file", str(body_file)])
    assert rc == 0
    out = capsys.readouterr().out
    assert "FLAG" in out  # flagged but still exit 0
