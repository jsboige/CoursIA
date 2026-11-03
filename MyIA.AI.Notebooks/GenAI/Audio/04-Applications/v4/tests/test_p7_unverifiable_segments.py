"""P7 — un echantillon illisible ne peut pas produire un verdict vert.

Le controle d'omission lisait ``tts_results.json`` puis sautait en silence tout
segment dont le MP3 manque -- c'est-a-dire exactement les segments qu'un rendu
rate produit. Le rapport pouvait donc afficher « OMISSIONS: none >=3 mots » et
un verdict PASS au-dessus d'un corpus troue : la moyenne WER ne portait que
sur les segments survivants.

Le contrat verifie ici : ces segments sont comptes, nommes dans
``omission_report.json`` et dans ``quality_report.json``, et ils interdisent
le PASS.

Tests hermetiques : ni Whispher, ni Gradio, ni ffmpeg -- la transcription et la
diarisation sont remplacees, les MP3 sont des fichiers vides.

Run from the v4 directory:
    python -m pytest tests/test_p7_unverifiable_segments.py -v
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

_V4 = Path(__file__).resolve().parent.parent
if str(_V4.parent) not in sys.path:
    sys.path.insert(0, str(_V4.parent))

TEXTE = "Boule de Suif baissa la tete et ne repondit rien."


def _segment(seg_index: int, speaker: str = "figurant"):
    from v4.schemas import AnnotatedSegment

    return AnnotatedSegment(
        seg_index=seg_index,
        type="dialogue",
        speaker=speaker,
        speaker_raw="Figurant",
        text=TEXTE,
        annotated_text=TEXTE,
        prosody_tags=[],
        tags_used=[],
        fishaudio_text="",
        dramatic_ref=None,
        dramatic_prompt="",
        tts_context_prefix="",
    )


class _Resp:
    status_code = 200

    def __init__(self, text: str):
        self._text = text

    def json(self):
        return {"text": self._text}


def _prepare(monkeypatch, tmp_path, tts_entries, n_segments=3):
    """Pose un faux dossier de sorties p7 et neutralise reseau + diarisation."""
    import requests

    import v4.p7_verify as p7
    from v4.schemas import AnnotatedBatch

    monkeypatch.setattr(p7, "BASE_DIR", tmp_path)
    outputs = tmp_path / "outputs"
    outputs.mkdir(parents=True, exist_ok=True)
    (outputs / "boule_de_suif_v4.mp3").write_bytes(b"MP3")
    (outputs / "annotated_v4.json").write_text(
        AnnotatedBatch(segments=[_segment(i) for i in range(1, n_segments + 1)])
        .model_dump_json(),
        encoding="utf-8",
    )
    (outputs / "tts_results.json").write_text(json.dumps(tts_entries), encoding="utf-8")

    # La transcription rend exactement le texte source : WER 0 sur ce qui est lu.
    monkeypatch.setattr(requests, "post", lambda *a, **k: _Resp(TEXTE))

    # Diarisation : on force l'echec gracieux, sinon le test attendrait Gradio.
    def _no_diarization(*a, **k):
        raise RuntimeError("diarization indisponible en test")

    monkeypatch.setattr(p7, "login_session", _no_diarization)
    monkeypatch.setattr(p7, "transcribe_with_diarization", _no_diarization)
    return p7, outputs


def _entry(seg_index: int, tmp: Path, present: bool) -> dict:
    mp3 = tmp / f"seg{seg_index}.mp3"
    if present:
        mp3.write_bytes(b"MP3")
    return {
        "seg_index": seg_index,
        "speaker": "figurant",
        "mp3_path": str(mp3) if present else "",
        "status": "generated" if present else "failed",
        "duration_s": 1.0,
    }


def test_missing_segment_blocks_the_pass_verdict(monkeypatch, tmp_path):
    """Le defaut : 2 segments sur 3 parfaitement transcrits -> PASS malgre un trou.

    Sans le correctif, la moyenne WER porte sur les 2 segments lisibles (0.0),
    ``detected_speakers = -1`` <= 10, et le verdict serait PASS. Il ne l'est
    plus : un segment non verifiable interdit le PASS.
    """
    entries = [
        _entry(1, tmp_path, True),
        _entry(2, tmp_path, False),  # rendu P5 en echec : aucun MP3
        _entry(3, tmp_path, True),
    ]
    p7, outputs = _prepare(monkeypatch, tmp_path, entries)

    report_path = p7.run(force=True)
    report = json.loads(report_path.read_text(encoding="utf-8"))

    assert report["wer"]["mean"] == 0.0, report["wer"]
    assert report["wer"]["unverifiable_segments"] == 1.0, report["wer"]
    assert report["verdict"] == "NEEDS_REVIEW", report["verdict"]

    omission = json.loads((outputs / "omission_report.json").read_text(encoding="utf-8"))
    assert omission["segments_unverifiable_missing"] == 1
    assert [u["seg_index"] for u in omission["unverifiable_missing"]] == [2]
    assert omission["unverifiable_missing"][0]["reason"] == "no_mp3_path"
    assert omission["unverifiable_missing"][0]["status"] == "failed"


def test_declared_but_absent_file_is_named_separately(monkeypatch, tmp_path):
    """Un chemin annonce dont le fichier a disparu n'est pas 'aucun chemin'."""
    entries = [
        _entry(1, tmp_path, True),
        {
            "seg_index": 2,
            "speaker": "figurant",
            "mp3_path": str(tmp_path / "disparu.mp3"),
            "status": "generated",
            "duration_s": 1.0,
        },
    ]
    p7, outputs = _prepare(monkeypatch, tmp_path, entries, n_segments=2)

    p7.run(force=True)

    omission = json.loads((outputs / "omission_report.json").read_text(encoding="utf-8"))
    assert omission["unverifiable_missing"][0]["reason"] == "mp3_absent"


def test_complete_corpus_can_still_pass(monkeypatch, tmp_path):
    """Controle positif : sans trou, le verdict reste PASS (on ne bloque pas tout)."""
    entries = [_entry(i, tmp_path, True) for i in (1, 2, 3)]
    p7, outputs = _prepare(monkeypatch, tmp_path, entries)

    report_path = p7.run(force=True)
    report = json.loads(report_path.read_text(encoding="utf-8"))

    assert report["wer"]["unverifiable_segments"] == 0.0
    assert report["wer"]["mean"] == 0.0
    assert report["verdict"] == "PASS", report["verdict"]

    omission = json.loads((outputs / "omission_report.json").read_text(encoding="utf-8"))
    assert omission["segments_unverifiable_missing"] == 0
    assert omission["unverifiable_missing"] == []


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
