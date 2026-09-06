#!/usr/bin/env python3
"""
test_batch_reexecute.py — garde de vraisemblance et cwd explicite (#14356).

Couvre :
  - _output_census : recensement outputs / image/png / volume par type MIME,
    abstention si illisible
  - _degradation : ne signale qu'une CHUTE, et seulement avec une reference
    (comptes images/outputs, volume MIME -- l'axe qui voit les talons que le
    comptage glorifie en hausse)
  - execute_notebook : un papermill sortant 0 en ayant perdu les images rend
    DEGRADED et restaure la sauvegarde ; idem quand un talon HTML remplace la
    charge utile alors que le compte d'outputs MONTE
  - execute_notebook : --cwd transmis a papermill, valeur selon cwd_mode

Les reproductions sont les deux defauts mesures : 2026-09-02 sur
``01-5-Qwen-Image-Edit.ipynb`` (9 s, 0 image, ``SUCCESS`` affiche) et
2026-09-03 sur ``Infer-7-Skills-IRT.ipynb`` (``dot`` absent : six graphes de
facteurs remplaces par des talons ``Graphviz non disponible``, outputs en
HAUSSE, ``text/html`` 194 409 -> 6 856). Ce sont les deux seuls cas ou le
code de sortie ment sans qu'aucun autre signal ne bronche.

Usage :
    pytest tests/test_batch_reexecute.py -v
"""

from __future__ import annotations

import json
import sys
from pathlib import Path
from types import SimpleNamespace

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts" / "notebook_tools"))

import batch_reexecute  # noqa: E402
from batch_reexecute import _degradation, _output_census  # noqa: E402


def _nb(n_images: int = 0, n_text: int = 0, html_chars: int = 0,
        n_html: int = 1) -> dict:
    """Minimal notebook carrying the requested output census.

    ``html_chars`` spreads ``n_html`` ``text/html`` payloads of that many
    characters each (list-of-lines form, as nbformat stores it), so volume
    collapses can be reproduced without six-figure literals in the source.
    """
    outputs = [{"output_type": "display_data", "data": {"image/png": "iVBORw0KGgo="}}
               for _ in range(n_images)]
    outputs += [{"output_type": "stream", "name": "stdout", "text": ["ok\n"]}
                for _ in range(n_text)]
    for _ in range(n_html if html_chars > 0 else 0):
        outputs.append({"output_type": "display_data",
                        "data": {"text/html": ["g" * html_chars]}})
    return {
        "cells": [{"cell_type": "code", "source": ["pass"],
                   "execution_count": 1, "outputs": outputs, "metadata": {}}],
        "metadata": {"kernelspec": {"name": "python3"}},
        "nbformat": 4, "nbformat_minor": 5,
    }


def _write(path: Path, nb: dict) -> Path:
    path.write_text(json.dumps(nb, indent=1), encoding="utf-8")
    return path


# --- _output_census ---

def test_census_counts_images_and_outputs(tmp_path: Path) -> None:
    nb = _write(tmp_path / "a.ipynb", _nb(n_images=2, n_text=3))
    assert _output_census(nb) == {
        "readable": True, "outputs": 5, "images": 2,
        "mime_chars": {"image/png": 2 * len("iVBORw0KGgo=")},
    }


def test_census_totals_mime_volume_across_outputs(tmp_path: Path) -> None:
    """The volume axis: three ``text/html`` payloads sum into one per-MIME
    total, whatever their number of lines."""
    nb = _write(tmp_path / "a2.ipynb", _nb(n_text=1, html_chars=3000, n_html=3))
    census = _output_census(nb)
    assert census["outputs"] == 4
    assert census["mime_chars"]["text/html"] == 3 * 3000


def test_census_handles_null_outputs(tmp_path: Path) -> None:
    """``outputs: null`` occurs in hand-edited notebooks; it must not raise."""
    raw = _nb()
    raw["cells"][0]["outputs"] = None
    nb = _write(tmp_path / "b.ipynb", raw)
    assert _output_census(nb)["outputs"] == 0


def test_census_abstains_on_unreadable(tmp_path: Path) -> None:
    nb = tmp_path / "c.ipynb"
    nb.write_text("{not json", encoding="utf-8")
    assert _output_census(nb)["readable"] is False


# --- _degradation ---

def test_degradation_flags_images_lost() -> None:
    before = {"readable": True, "outputs": 5, "images": 2}
    after = {"readable": True, "outputs": 5, "images": 0}
    assert _degradation(before, after) == "images 2 -> 0"


def test_degradation_silent_without_image_baseline() -> None:
    """No images before means no reference: the guard catches regressions, not
    absences — which is the nominal state of the notebooks this tool targets."""
    before = {"readable": True, "outputs": 4, "images": 0}
    after = {"readable": True, "outputs": 4, "images": 0}
    assert _degradation(before, after) == ""


def test_degradation_silent_on_rise() -> None:
    """A rise is the nominal outcome: the tool exists to fill missing outputs."""
    before = {"readable": True, "outputs": 0, "images": 0}
    after = {"readable": True, "outputs": 12, "images": 3}
    assert _degradation(before, after) == ""


def test_degradation_flags_output_collapse() -> None:
    before = {"readable": True, "outputs": 20, "images": 0}
    after = {"readable": True, "outputs": 4, "images": 0}
    assert _degradation(before, after) == "outputs 20 -> 4"


def test_degradation_tolerates_minor_drop() -> None:
    """A deprecation warning that stops being emitted is not a collapse."""
    before = {"readable": True, "outputs": 20, "images": 0}
    after = {"readable": True, "outputs": 19, "images": 0}
    assert _degradation(before, after) == ""


def test_degradation_abstains_when_either_side_unreadable() -> None:
    unreadable = {"readable": False, "outputs": 0, "images": 0}
    populated = {"readable": True, "outputs": 9, "images": 2}
    assert _degradation(unreadable, populated) == ""
    assert _degradation(populated, unreadable) == ""


# --- _degradation, axe volume MIME (#14356, gap mesure sur Infer-7) ---

def test_degradation_flags_mime_volume_collapse_despite_output_rise() -> None:
    """The measured Graphviz incident: six factor graphs replaced by as many
    ``<strong>Graphviz non disponible.</strong>`` stubs -- the output count
    RISES (290 -> 314), the image count never moved, only the ``text/html``
    volume (194 409 -> 6 856) tells the story."""
    before = {"readable": True, "outputs": 290, "images": 0,
              "mime_chars": {"text/html": 194409}}
    after = {"readable": True, "outputs": 314, "images": 0,
             "mime_chars": {"text/html": 6856}}
    assert _degradation(before, after) == "text/html 194409 -> 6856"


def test_degradation_silent_on_minor_mime_shrink() -> None:
    """A re-render 10 % shorter (a shorter table, a terser repr) is variation,
    not a stub."""
    before = {"readable": True, "outputs": 5, "images": 0,
              "mime_chars": {"text/html": 100000}}
    after = {"readable": True, "outputs": 5, "images": 0,
             "mime_chars": {"text/html": 90000}}
    assert _degradation(before, after) == ""


def test_degradation_mime_silent_below_volume_floor() -> None:
    """Small payloads vary legitimately; without a floor a 1.5k -> 100 stub
    would cry wolf on every terse notebook."""
    before = {"readable": True, "outputs": 5, "images": 0,
              "mime_chars": {"text/html": 1500}}
    after = {"readable": True, "outputs": 5, "images": 0,
             "mime_chars": {"text/html": 100}}
    assert _degradation(before, after) == ""


def test_degradation_handles_censuses_without_mime_axis() -> None:
    """Censuses shaped before the volume axis (and handcrafted ones) must keep
    working: absence of the key is absence of a reference, not a collapse."""
    before = {"readable": True, "outputs": 4, "images": 0}
    after = {"readable": True, "outputs": 4, "images": 0,
             "mime_chars": {"text/html": 7000}}
    assert _degradation(before, after) == ""


# --- execute_notebook ---

@pytest.fixture
def fake_papermill(monkeypatch):
    """Replace subprocess.run with a stub that writes a chosen result."""
    captured: dict = {}

    def install(result_nb: dict | None, returncode: int = 0):
        def fake_run(cmd, **kwargs):
            captured["cmd"] = cmd
            captured["kwargs"] = kwargs
            if result_nb is not None:
                Path(cmd[4]).write_text(json.dumps(result_nb, indent=1), encoding="utf-8")
            return SimpleNamespace(returncode=returncode, stdout="", stderr="")

        monkeypatch.setattr(batch_reexecute.subprocess, "run", fake_run)
        return captured

    return install


def test_zero_exit_with_lost_images_is_degraded(tmp_path: Path, fake_papermill) -> None:
    """The measured incident: papermill exits 0, exception None, clean
    execution_count — and zero images. Only the census tells them apart."""
    nb = _write(tmp_path / "d.ipynb", _nb(n_images=2, n_text=1))
    fake_papermill(_nb(n_images=0, n_text=1))

    result = batch_reexecute.execute_notebook(nb, "python3", 60)

    assert result["status"] == "DEGRADED"
    assert "images 2 -> 0" in result["error"]
    # The backup is restored: a green-looking empty notebook is worse than none.
    assert _output_census(nb)["images"] == 2
    assert not nb.with_suffix(".ipynb.bak").exists()


def test_zero_exit_with_stubbed_html_is_degraded(tmp_path: Path, fake_papermill) -> None:
    """The 2026-09-03 reproduction: papermill exits 0, the output count RISES
    (a stub is one more output, not one fewer), images never existed -- only
    the per-MIME volume names the collapse. The backup must be restored."""
    nb = _write(tmp_path / "d2.ipynb", _nb(n_text=2, html_chars=65000, n_html=3))
    # 3 riches payloads deviennent 6 talons : outputs 5 -> 8, volume /28.
    fake_papermill(_nb(n_text=2, html_chars=65000 // 28, n_html=6))

    result = batch_reexecute.execute_notebook(nb, "python3", 60)

    assert result["status"] == "DEGRADED"
    assert "text/html" in result["error"]
    assert _output_census(nb)["mime_chars"]["text/html"] == 3 * 65000
    assert not nb.with_suffix(".ipynb.bak").exists()


def test_allow_degraded_keeps_the_result(tmp_path: Path, fake_papermill) -> None:
    nb = _write(tmp_path / "e.ipynb", _nb(n_images=2, n_text=1))
    fake_papermill(_nb(n_images=0, n_text=1))

    result = batch_reexecute.execute_notebook(nb, "python3", 60, allow_degraded=True)

    assert result["status"] == "SUCCESS"
    assert result["degraded"] == "images 2 -> 0"
    assert _output_census(nb)["images"] == 0


def test_healthy_run_reports_success_without_degradation(tmp_path: Path, fake_papermill) -> None:
    nb = _write(tmp_path / "f.ipynb", _nb(n_images=0, n_text=0))
    fake_papermill(_nb(n_images=2, n_text=4))

    result = batch_reexecute.execute_notebook(nb, "python3", 60)

    assert result["status"] == "SUCCESS"
    assert result["degraded"] is None


def test_cwd_repo_is_the_default(tmp_path: Path, fake_papermill) -> None:
    nb = _write(tmp_path / "g.ipynb", _nb(n_images=1))
    captured = fake_papermill(_nb(n_images=1))

    batch_reexecute.execute_notebook(nb, "python3", 60)

    cmd = captured["cmd"]
    assert "--cwd" in cmd, "papermill must be told the cwd explicitly (#14356)"
    assert cmd[cmd.index("--cwd") + 1] == str(batch_reexecute.REPO_ROOT)


def test_cwd_notebook_mode_passes_notebook_dir(tmp_path: Path, fake_papermill) -> None:
    nb = _write(tmp_path / "h.ipynb", _nb(n_images=1))
    captured = fake_papermill(_nb(n_images=1))

    batch_reexecute.execute_notebook(nb, "python3", 60, cwd_mode="notebook")

    cmd = captured["cmd"]
    assert cmd[cmd.index("--cwd") + 1] == str(nb.parent)
