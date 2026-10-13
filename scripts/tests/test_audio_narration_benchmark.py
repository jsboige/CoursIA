"""Tests pour scripts/audio_narration_benchmark.py.

Couvre :
- Structure du module (imports, ENGINES registry, NARRATION_REFERENCE)
- dry_run_benchmark : verdict produit, aucun appel réseau
- _render_verdict_md : structure markdown attendue
"""
from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

SCRIPT = Path(__file__).resolve().parent.parent / "audio_narration_benchmark.py"


def test_engine_registry_has_three_engines():
    """Le benchmark expose 3 moteurs : Kokoro, TADA, Qwen3."""
    sys.path.insert(0, str(SCRIPT.parent))
    import audio_narration_benchmark as m

    keys = tuple(e.key for e in m.ENGINES)
    assert keys == ("kokoro", "tada", "qwen3"), f"keys={keys}"
    for e in m.ENGINES:
        assert e.path.startswith("/"), f"path mal formé: {e.path}"
        assert e.expected_latency_s > 0, f"latence <= 0: {e.expected_latency_s}"
        assert e.expressivity, f"expressivité vide: {e.key}"


def test_narration_reference_is_short_enough():
    """Le texte de référence tient sous 1024 chars (latence gateway acceptable)."""
    sys.path.insert(0, str(SCRIPT.parent))
    import audio_narration_benchmark as m

    assert len(m.NARRATION_REFERENCE) < 1024, (
        f"texte trop long: {len(m.NARATION_REFERENCE)} chars")


def test_dry_run_benchmark_produces_verdict(tmp_path: Path, capsys):
    """--dry-run imprime le verdict SOTA, ne touche pas le réseau."""
    result = subprocess.run(
        [sys.executable, str(SCRIPT), "--dry-run"],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
        cwd=str(tmp_path), timeout=15,
    )
    # Exit code 0 attendu (toutes les entrées ok ou dry-run).
    assert result.returncode == 0, f"stderr={result.stderr}"
    # Verdict SOTA doit être dans stdout.
    assert "Verdict SOTA" in result.stdout, "verdict SOTA absent du stdout"
    assert "kokoro" in result.stdout.lower()
    assert "tada" in result.stdout.lower()
    assert "qwen3" in result.stdout.lower()
    # Recommandations présentes.
    assert "Latence minimale" in result.stdout
    assert "Expressivité maximale" in result.stdout
    assert "Clonage de voix" in result.stdout
    # Voie 3 B.0 explicitée.
    assert "Aucune voix clonée" in result.stdout


def test_render_verdict_md_contains_required_sections():
    """_render_verdict_md génère un markdown avec tableau + recommandations."""
    sys.path.insert(0, str(SCRIPT.parent))
    import audio_narration_benchmark as m

    fake_results = [
        m.BenchmarkResult(
            engine=e.key, label=e.label, voice=m.DEFAULT_VOICES[e.key],
            latency_s=e.expected_latency_s, wav_bytes=0, status="dry-run",
        )
        for e in m.ENGINES
    ]
    md = m._render_verdict_md(m.NARRATION_REFERENCE, fake_results)
    # Sections attendues
    assert "# Verdict SOTA" in md
    assert "| Moteur | Voix | Latence | Taille WAV | Statut |" in md
    assert "## Recommandation par cas d'usage" in md
    assert "## Notes" in md
    # Les 3 moteurs sont dans le tableau
    for e in m.ENGINES:
        assert f"`{e.key}`" in md, f"moteur {e.key} absent"


if __name__ == "__main__":
    import pytest
    sys.exit(pytest.main([__file__, "-v"]))
