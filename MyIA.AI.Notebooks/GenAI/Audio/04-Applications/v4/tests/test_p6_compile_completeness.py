"""P6 — un audiobook troue n'est plus declare termine.

P6 ecartait un segment dont le MP3 est absent (rendu P5 en echec) ou
indecodable, exportait quand meme le fichier, et imprimait « Done ». Le seul
signal etait un « Skipped: N » noye dans les lignes de succes : l'audiobook
livre avait des trous et rien ne le disait.

Le contrat verifie ici : les artefacts sont ecrits (le rendu coute des
heures, on ne le jette pas), le compte-rendu machine nomme les segments
manquants, et la phase ECHOUE, sauf desistement explicite
(``allow_missing=True``).

Tests hermetiques : pydub est remplace par un double injecte dans
``sys.modules``, aucun MP3 reel n'est lu ni ecrit, ffmpeg est declare absent.

Run from the v4 directory:
    python -m pytest tests/test_p6_compile_completeness.py -v
"""
from __future__ import annotations

import json
import sys
import types
from pathlib import Path

import pytest

_V4 = Path(__file__).resolve().parent.parent
if str(_V4.parent) not in sys.path:
    sys.path.insert(0, str(_V4.parent))


class _FakeAudio:
    """Assez de pydub pour la boucle de concatenation (longueur, +=, export)."""

    def __init__(self, duration_ms: int = 0, payload: bytes = b"AUDIO"):
        self.duration_ms = duration_ms
        self.payload = payload

    def __len__(self):
        return self.duration_ms

    def __iadd__(self, other):
        self.duration_ms += len(other)
        return self

    def append(self, other, crossfade=0):
        return _FakeAudio(self.duration_ms + len(other) - crossfade)

    def export(self, path, format=None, bitrate=None, tags=None):
        Path(path).write_bytes(b"MP3-BYTES")
        self.exported = str(path)


def _install_fake_pydub(monkeypatch, unreadable: set[str] | None = None):
    """Injecte un pydub double ; ``unreadable`` = suffixes de chemins a refuser."""
    unreadable = unreadable or set()

    class _AudioSegment:
        @staticmethod
        def silent(duration=0):
            return _FakeAudio(duration)

        @staticmethod
        def from_mp3(path):
            if any(str(path).endswith(s) for s in unreadable):
                raise OSError("cannot decode")
            return _FakeAudio(1000)

    module = types.ModuleType("pydub")
    module.AudioSegment = _AudioSegment
    monkeypatch.setitem(sys.modules, "pydub", module)
    return module


def _write_tts(path: Path, entries: list[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(entries), encoding="utf-8")


def _prepare(monkeypatch, tmp_path, entries):
    """Pose un faux dossier de sorties et neutralise l'environnement p6."""
    import v4.p6_compile as p6

    monkeypatch.setattr(p6, "BASE_DIR", tmp_path)
    (tmp_path / "outputs").mkdir(parents=True, exist_ok=True)
    _write_tts(tmp_path / "outputs" / "tts_results.json", entries)
    monkeypatch.setattr(p6, "_detect_act_boundaries", lambda path: {})
    # Pas de ffmpeg : le bloc .m4b se contente d'un avertissement.
    monkeypatch.setattr(p6.shutil, "which", lambda name: None)
    return p6


def _seg(seg_index: int, speaker: str = "figurant", **extra) -> dict:
    entry = {"seg_index": seg_index, "speaker": speaker, "mp3_path": "", "status": "generated"}
    entry.update(extra)
    return entry


def _touch(tmp_path: Path, name: str) -> str:
    p = tmp_path / name
    p.write_bytes(b"MP3")
    return str(p)


def test_missing_segments_fail_the_compilation(monkeypatch, tmp_path):
    """Le defaut : 2 segments sur 3 sans MP3, et p6 rendait "Done".

    Desormais : le MP3 est ecrit, le rapport nomme les deux segments, et la
    phase leve -- un appelant ne peut pas prendre "exporte" pour "complet".
    """
    entries = [
        _seg(1, mp3_path=_touch(tmp_path, "seg1.mp3")),
        _seg(2, status="failed"),  # P5 n'a jamais produit de MP3
        _seg(3, mp3_path=str(tmp_path / "absent.mp3")),  # chemin annonce, fichier absent
    ]
    p6 = _prepare(monkeypatch, tmp_path, entries)
    _install_fake_pydub(monkeypatch)

    with pytest.raises(p6.IncompleteAudiobookError) as excinfo:
        p6.run(force=True)

    message = str(excinfo.value)
    assert "2 segment(s) sur 3" in message, message

    # Les artefacts sont ecrits : on ne jette pas un rendu de plusieurs heures.
    assert (tmp_path / "outputs" / "boule_de_suif_v4.mp3").exists()

    report = json.loads(
        (tmp_path / "outputs" / "compile_report.json").read_text(encoding="utf-8")
    )
    assert report["complete"] is False
    assert report["segments_expected"] == 3
    assert report["segments_compiled"] == 1
    assert report["segments_missing"] == 2
    assert report["segments_unreadable"] == 0
    assert [s["seg_index"] for s in report["missing_segments"]] == [2, 3]
    assert {s["seg_index"]: s["reason"] for s in report["missing_segments"]} == {
        2: "no_mp3_path",
        3: "mp3_absent",
    }
    # Le statut amont est conserve : c'est lui qui dit POURQUOI le MP3 manque.
    assert report["missing_segments"][0]["status"] == "failed"


def test_allow_missing_is_the_explicit_opt_out(monkeypatch, tmp_path):
    """Le run de diagnostic doit pouvoir produire le fichier sans lever."""
    entries = [
        _seg(1, mp3_path=_touch(tmp_path, "seg1.mp3")),
        _seg(2, status="failed"),
    ]
    p6 = _prepare(monkeypatch, tmp_path, entries)
    _install_fake_pydub(monkeypatch)

    out = p6.run(force=True, allow_missing=True)

    assert out.exists()
    report = json.loads(
        (tmp_path / "outputs" / "compile_report.json").read_text(encoding="utf-8")
    )
    assert report["complete"] is False
    assert report["segments_missing"] == 1


def test_complete_compilation_still_passes(monkeypatch, tmp_path):
    """Controle positif : une compilation saine ne leve pas et se declare complete."""
    entries = [
        _seg(1, mp3_path=_touch(tmp_path, "seg1.mp3")),
        _seg(2, mp3_path=_touch(tmp_path, "seg2.mp3")),
    ]
    p6 = _prepare(monkeypatch, tmp_path, entries)
    _install_fake_pydub(monkeypatch)

    out = p6.run(force=True)

    assert out.exists()
    report = json.loads(
        (tmp_path / "outputs" / "compile_report.json").read_text(encoding="utf-8")
    )
    assert report["complete"] is True
    assert report["segments_compiled"] == 2
    assert report["segments_missing"] == 0
    assert report["missing_segments"] == []


def test_unreadable_mp3_is_a_distinct_cause(monkeypatch, tmp_path):
    """Un fichier present mais indecodable n'est pas "absent" : causes separees."""
    entries = [
        _seg(1, mp3_path=_touch(tmp_path, "seg1.mp3")),
        _seg(2, mp3_path=_touch(tmp_path, "seg2.mp3")),
    ]
    p6 = _prepare(monkeypatch, tmp_path, entries)
    _install_fake_pydub(monkeypatch, unreadable={"seg2.mp3"})

    with pytest.raises(p6.IncompleteAudiobookError):
        p6.run(force=True)

    report = json.loads(
        (tmp_path / "outputs" / "compile_report.json").read_text(encoding="utf-8")
    )
    assert report["complete"] is False
    assert report["segments_missing"] == 0
    assert report["segments_unreadable"] == 1
    assert report["unreadable_segments"][0]["seg_index"] == 2
    assert "cannot decode" in report["unreadable_segments"][0]["error"]


def test_run_keeps_its_indexable_signature():
    """p6 est appele uniformement par run_pipeline : `run(force=...)` doit tenir."""
    import inspect

    import v4.p6_compile as p6

    params = inspect.signature(p6.run).parameters
    assert list(params)[:2] == ["force", "allow_missing"], list(params)
    assert params["force"].default is False
    assert params["allow_missing"].default is False


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
