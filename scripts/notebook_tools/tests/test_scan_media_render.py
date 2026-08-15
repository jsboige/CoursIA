"""Tests for scripts/notebook_tools/scan_media_render.py — media-render scan
(#10996) with the 5 measured predicate blind spots corrected (lecon L965:
29/30 false positives on the real corpus; the 5th blind spot measured on
mesurer-la-derive-dun-copilot).

Covers pure functions (scan_notebook verdicts) against synthetic notebooks
for each blind spot, plus a regression test over the 30 real notebooks of the
#10996 triage: the enriched predicate must flag none of them (the triage
concluded 29 FAUX POSITIFS + 1 REPARABLE, all carrying committed media or
widgets/import-only).
"""

import json
import subprocess
import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from scan_media_render import (  # noqa: E402
    discover_tracked_notebooks,
    scan_notebook,
)

REPO = Path(__file__).resolve().parent.parent.parent.parent

# Les 30 notebooks du tri #10996 (tranches A/B/C/D) — chemins exacts verifies
# sur main au tri (issuecomments 5299344909, 5299156801, 5299386143, 5299391278).
TRIAGE_30 = [
    # Tranche A — Audio/01-Foundation + 02-Advanced (10)
    "MyIA.AI.Notebooks/GenAI/Audio/01-Foundation/01-1-OpenAI-TTS-Intro.ipynb",
    "MyIA.AI.Notebooks/GenAI/Audio/01-Foundation/01-2-OpenAI-Whisper-STT.ipynb",
    "MyIA.AI.Notebooks/GenAI/Audio/01-Foundation/01-4-Whisper-Local.ipynb",
    "MyIA.AI.Notebooks/GenAI/Audio/01-Foundation/01-5-Kokoro-TTS-Local.ipynb",
    "MyIA.AI.Notebooks/GenAI/Audio/02-Advanced/02-1-Chatterbox-TTS.ipynb",
    "MyIA.AI.Notebooks/GenAI/Audio/02-Advanced/02-2-XTTS-Voice-Cloning.ipynb",
    "MyIA.AI.Notebooks/GenAI/Audio/02-Advanced/02-3-MusicGen-Generation.ipynb",
    "MyIA.AI.Notebooks/GenAI/Audio/02-Advanced/02-5-Multi-Model-TTS-Gateway.ipynb",
    "MyIA.AI.Notebooks/GenAI/Audio/02-Advanced/02-6-MIDI-Generation.ipynb",
    "MyIA.AI.Notebooks/GenAI/Audio/02-Advanced/02-8-Expressive-TTS.ipynb",
    # Tranche B — Audio/04-Applications (9)
    "MyIA.AI.Notebooks/GenAI/Audio/04-Applications/04-1-Educational-Audio-Content.ipynb",
    "MyIA.AI.Notebooks/GenAI/Audio/04-Applications/04-11-Generation-TTS.ipynb",
    "MyIA.AI.Notebooks/GenAI/Audio/04-Applications/04-12-Compilation-Audio.ipynb",
    "MyIA.AI.Notebooks/GenAI/Audio/04-Applications/04-13-Audiobook-FishAudio-S2Pro.ipynb",
    "MyIA.AI.Notebooks/GenAI/Audio/04-Applications/04-2-Transcription-Pipeline.ipynb",
    "MyIA.AI.Notebooks/GenAI/Audio/04-Applications/04-4-Audio-Video-Sync.ipynb",
    "MyIA.AI.Notebooks/GenAI/Audio/04-Applications/04-5-LiveCoding-LLM-Music.ipynb",
    "MyIA.AI.Notebooks/GenAI/Audio/04-Applications/04-6-Audiobook-Pipeline.ipynb",
    "MyIA.AI.Notebooks/GenAI/Audio/04-Applications/04-9-Voice-Casting.ipynb",
    # Tranche C — Image + Video (4)
    "MyIA.AI.Notebooks/GenAI/Image/04-Applications/04-1-Educational-Content-Generation.ipynb",
    "MyIA.AI.Notebooks/GenAI/Image/04-Applications/04-3-Production-Integration.ipynb",
    "MyIA.AI.Notebooks/GenAI/Video/02-Advanced/02-5-LTX2-Audiovisual.ipynb",
    "MyIA.AI.Notebooks/GenAI/Audio/02-Advanced/02-9-AceStep-Music-Generation.ipynb",
    # Tranche D — hors serie media (7)
    "MyIA.AI.Notebooks/GenAI/00-GenAI-Environment/00-2-Docker-Services-Management.ipynb",
    "MyIA.AI.Notebooks/GenAI/PostTraining/PT_06_eval_comparative.ipynb",
    "MyIA.AI.Notebooks/GenAI/PostTraining/PT_11_grpo_qwen35_rlvr.ipynb",
    "MyIA.AI.Notebooks/GenAI/SemanticKernel/10-SemanticKernel-NotebookMaker.ipynb",
    "MyIA.AI.Notebooks/GenAI/SemanticKernel/10a-SemanticKernel-NotebookMaker-batch.ipynb",
    "MyIA.AI.Notebooks/GenAI/SemanticKernel/10b-SemanticKernel-NotebookMaker-batch-parameterized.ipynb",
    "MyIA.AI.Notebooks/GenAI/SemanticKernel/Créateur de mail personnalisé.ipynb",
]


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _nb(code_sources, outputs_by_cell=None):
    """Notebook dict: code cells from code_sources, optional per-cell outputs."""
    outputs_by_cell = outputs_by_cell or {}
    cells = []
    for i, src in enumerate(code_sources):
        cells.append({
            "cell_type": "code",
            "execution_count": i + 1,
            "source": [src] if isinstance(src, str) else src,
            "outputs": outputs_by_cell.get(i, []),
        })
    return {"nbformat": 4, "nbformat_minor": 5, "metadata": {}, "cells": cells}


def _html_output(html):
    return {"data": {"text/html": html}, "metadata": {}, "output_type": "display_data"}


def _write_nb(tmp_path, code_sources, outputs_by_cell=None, name="nb.ipynb"):
    p = tmp_path / name
    p.write_text(json.dumps(_nb(code_sources, outputs_by_cell)), encoding="utf-8")
    return p


# ---------------------------------------------------------------------------
# Angle mort 1 : data-URI media dans text/html
# ---------------------------------------------------------------------------

def test_data_uri_in_html_counts_as_rendered(tmp_path):
    nb = _write_nb(
        tmp_path,
        ["audio = Audio(data, rate=22050)", "display(audio)"],
        outputs_by_cell={
            1: [_html_output('<audio><source src="data:audio/wav;base64,UklGRg=="></audio>')],
        },
    )
    r = scan_notebook(nb, tmp_path)
    assert r.data_uris == {"audio": 1}
    assert r.verdict() == "MEDIA_RENDERED"
    assert r.verdict(legacy=True) == "NO_MEDIA_RENDERED"  # l'ancien predicat ratait le data-URI


def test_data_uri_image_in_html(tmp_path):
    nb = _write_nb(
        tmp_path,
        ["display(Image('x.png'))"],
        outputs_by_cell={
            0: [_html_output('<img src="data:image/png;base64,iVBORw0KGgo=">')],
        },
    )
    r = scan_notebook(nb, tmp_path)
    assert r.data_uris == {"image": 1}
    assert r.verdict() == "MEDIA_RENDERED"


def test_plain_html_without_data_uri_is_not_media(tmp_path):
    nb = _write_nb(
        tmp_path,
        ["display(HTML('<b>Hello</b>'))"],
        outputs_by_cell={0: [_html_output("<b>Hello</b>")]},
    )
    r = scan_notebook(nb, tmp_path)
    assert r.data_uris == {}
    # display(HTML(...)) n'est pas une primitive media : aucun appel media.
    assert r.verdict() == "NO_MEDIA_PRIMITIVE"


# ---------------------------------------------------------------------------
# Angle mort 2 : imports comptes comme appels
# ---------------------------------------------------------------------------

def test_import_only_not_flagged(tmp_path):
    nb = _write_nb(
        tmp_path,
        ["from IPython.display import Audio, display", "transcript = model.transcribe('x.mp3')"],
    )
    r = scan_notebook(nb, tmp_path)
    assert r.primitive_calls == []          # le import ne compte pas comme appel
    assert r.legacy_primitive is True       # mais l'ancien predicat le comptait
    assert r.verdict() == "NO_MEDIA_PRIMITIVE"


def test_import_then_real_call(tmp_path):
    nb = _write_nb(
        tmp_path,
        ["from IPython.display import Audio, display", "display(Audio('x.wav'))"],
        outputs_by_cell={1: [_html_output('<audio src="data:audio/wav;base64,UklGRg==">')]},
    )
    r = scan_notebook(nb, tmp_path)
    assert r.primitive_calls == ["display(Audio/Image/Video)"]
    assert r.verdict() == "MEDIA_RENDERED"


# ---------------------------------------------------------------------------
# Angle mort 3 : widgets ipywidgets exclus
# ---------------------------------------------------------------------------

def test_widgets_html_not_a_media_primitive(tmp_path):
    nb = _write_nb(
        tmp_path,
        ["display(widgets.HTML('<h3>Interface</h3>'))"],
        outputs_by_cell={0: [_html_output("<h3>Interface</h3>")]},
    )
    r = scan_notebook(nb, tmp_path)
    assert r.primitive_calls == []
    assert r.verdict() == "NO_MEDIA_PRIMITIVE"


# ---------------------------------------------------------------------------
# Angle mort 4 : media side-car (savefig → fichier tracke)
# ---------------------------------------------------------------------------

def _git_init_repo(tmp_path):
    subprocess.run(["git", "init", "-q", str(tmp_path)], check=True)
    subprocess.run(
        ["git", "-C", str(tmp_path), "config", "user.email", "t@t"],
        check=True, capture_output=True,
    )
    subprocess.run(
        ["git", "-C", str(tmp_path), "config", "user.name", "t"],
        check=True, capture_output=True,
    )


def test_savefig_sidecar_tracked_counts_as_rendered(tmp_path):
    _git_init_repo(tmp_path)
    (tmp_path / "fig.png").write_bytes(b"\x89PNG\r\n\x1a\nfake")
    subprocess.run(["git", "-C", str(tmp_path), "add", "fig.png"], check=True)
    subprocess.run(["git", "-C", str(tmp_path), "commit", "-qm", "fig"], check=True)
    nb = _write_nb(
        tmp_path,
        ["plt.savefig('fig.png')", "plt.show()"],
    )
    r = scan_notebook(nb, tmp_path)
    assert r.sidecar_files == ["fig.png"]
    assert r.verdict() == "MEDIA_RENDERED"
    assert r.verdict(legacy=True) == "NO_MEDIA_RENDERED"  # side-car invisible a l'ancien predicat


def test_savefig_untracked_file_not_counted(tmp_path):
    _git_init_repo(tmp_path)
    (tmp_path / "fig.png").write_bytes(b"\x89PNG\r\n\x1a\nfake")  # cree mais non tracke
    nb = _write_nb(tmp_path, ["plt.savefig('fig.png')"])
    r = scan_notebook(nb, tmp_path)
    assert r.sidecar_files == []
    assert r.verdict() == "NO_MEDIA_RENDERED"


# ---------------------------------------------------------------------------
# Angle mort 5 : definition de fonction `def image(v)` n'est pas un appel
# ---------------------------------------------------------------------------

def test_function_definition_named_image_not_a_call(tmp_path):
    # `def image(v)` seul n'est pas un appel a la primitive IPython Image.
    nb = _write_nb(
        tmp_path,
        ["def image(v):", "    return v * 2"],
    )
    r = scan_notebook(nb, tmp_path)
    assert r.primitive_calls == []
    assert r.verdict() == "NO_MEDIA_PRIMITIVE"


# ---------------------------------------------------------------------------
# Vrai candidat : primitive appelee, aucun media rendu
# ---------------------------------------------------------------------------

def test_real_candidate_still_flagged(tmp_path):
    nb = _write_nb(
        tmp_path,
        ["display(Audio('missing.wav'))"],
    )
    r = scan_notebook(nb, tmp_path)
    assert r.primitive_calls == ["display(Audio/Image/Video)"]
    assert r.data_uris == {} and r.mimes_separated == {} and r.sidecar_files == []
    assert r.verdict() == "NO_MEDIA_RENDERED"


# ---------------------------------------------------------------------------
# Regression : les 30 du tri #10996 ne doivent plus etre signales
# ---------------------------------------------------------------------------

@pytest.mark.skipif(
    not (REPO / "MyIA.AI.Notebooks/GenAI").exists(),
    reason="corpus GenAI absent (hors depot racine)",
)
def test_triage_30_no_false_defect():
    missing = [p for p in TRIAGE_30 if not (REPO / p).exists()]
    assert not missing, f"chemins du tri introuvables: {missing}"
    flagged = []
    for p in TRIAGE_30:
        r = scan_notebook(REPO / p, REPO)
        if r.verdict() == "NO_MEDIA_RENDERED":
            flagged.append((p, r.primitive_calls))
    assert flagged == [], (
        f"le predicat enrichi re-signale des notebooks du tri #10996 "
        f"(30/30 classes FAUX POSITIF) : {flagged}"
    )


def test_triage_30_legacy_still_flags_them():
    """Controle positif : l'ancien predicat DOIT encore signaler les 30."""
    missing = [p for p in TRIAGE_30 if not (REPO / p).exists()]
    if missing:
        pytest.skip(f"corpus GenAI absent: {missing[:2]}")
    flagged = sum(
        1 for p in TRIAGE_30
        if scan_notebook(REPO / p, REPO).verdict(legacy=True) == "NO_MEDIA_RENDERED"
    )
    assert flagged == 30, f"le predicat legacy ne signale plus les 30 (actuel: {flagged})"



# ---------------------------------------------------------------------------
# Robustesse (ai-01 c.103, #10985) : fichier JSON invalide + discovery trackee
# ---------------------------------------------------------------------------

def test_malformed_json_returns_scan_error(tmp_path):
    """Un notebook illisible ne tue pas le run : scan_error + verdict SCAN_ERROR."""
    bad = tmp_path / "broken.ipynb"
    bad.write_text('{"cells": [', encoding="utf-8")
    r = scan_notebook(bad, tmp_path)
    assert r.scan_error, "le JSON invalide doit etre capture, pas leve"
    assert "JSONDecodeError" in r.scan_error
    assert r.verdict() == "SCAN_ERROR"
    assert r.verdict(legacy=True) == "SCAN_ERROR"
    assert r.primitive_calls == [] and r.data_uris == {}


def test_discover_tracked_excludes_untracked(tmp_path):
    """La decouverte par defaut scanne les notebooks SUIVIS, pas le disque :
    un .ipynb untracked (ex. research.ipynb invalide gitignore ESGF-2026)
    ne doit pas entrer dans le corpus."""
    _git_init_repo(tmp_path)
    tracked_dir = tmp_path / "MyIA.AI.Notebooks/GenAI/Audio/01-Foundation"
    tracked_dir.mkdir(parents=True)
    good = _write_nb(tracked_dir, ["display(Audio('a.wav'))"], name="01-1-ok.ipynb")
    subprocess.run(["git", "-C", str(tmp_path), "add", str(good)], check=True)
    subprocess.run(["git", "-C", str(tmp_path), "commit", "-qm", "nb"], check=True)

    # notebook untracked (invalide, comme ESGF research.ipynb) — hors git
    untracked = tmp_path / "MyIA.AI.Notebooks/GenAI/Audio/01-Foundation/broken.ipynb"
    untracked.write_text('{"cells": [', encoding="utf-8")

    found = discover_tracked_notebooks(tmp_path)
    assert found == [good], f"decouverte trackee doit exclure l'untracked: {found}"
    # et le fichier untracked ne produit pas d'erreur en scan direct : il n'est pas scanne
    assert all(r.scan_error is None for r in [scan_notebook(good, tmp_path)])
