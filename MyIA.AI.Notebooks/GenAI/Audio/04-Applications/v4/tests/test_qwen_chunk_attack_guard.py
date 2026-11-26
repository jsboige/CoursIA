"""Garde d'attaque par chunk sur les chemins Qwen (v4/prosody_lab/qwen_tts_client.py).

La phase 2 de #19739 demande une garde d'attaque **par chunk et en ligne** :
un chunk qui commence au milieu du texte perd son attaque, et aucune mesure
de duree ne le voit (les bandes caracteres/seconde des rendus propres et
omettants se recouvrent). L'organe de verdict est `v4.attack_guard` (#21459) ;
le chemin CV3 l'a cable dans sa boucle de rendu (PR #23476). Ces tests
couvrent les deux chemins Qwen du meme pipeline (VoiceDesign et CustomVoice),
qui sont eux aussi chunkes et n'etaient pas gardes.

Trois proprietes sont pinnees :

- **garde fermee par defaut au niveau du client** : un banc de mesure n'a pas
  de serveur ASR a cote de lui, et une garde incapable de joindre son organe
  ne doit pas pretendre avoir tourne ; c'est le pipeline qui l'active ;
- **le levier est le re-rendu** (le gateway ne prend pas de graine et
  echantillonne a temperature 0.9), et la passage est **refusee** si
  l'attaque est toujours absente : un chunk dont les premiers mots n'ont
  jamais ete prononces n'est jamais livre ;
- **le pipeline active la garde** sur les deux chemins narrateur.

Hermetique : ni reseau, ni GPU, ni pydub reel (faux module `pydub` injecte
dans `sys.modules`), comme `test_p5_customvoice_narrator`.

Run from the v4 directory:
    python -m pytest tests/test_qwen_chunk_attack_guard.py -v
"""
from __future__ import annotations

import sys
import types
from pathlib import Path

_V4 = Path(__file__).resolve().parent.parent
if str(_V4.parent) not in sys.path:
    sys.path.insert(0, str(_V4.parent))

# Une phrase unique : le chunker la rend telle quelle (une phrase par chunk).
_SENTENCE = "Il marcha longtemps dans la nuit, puis il s'arreta."
# Mots de tete perdus : le verdict d'attaque compte la perte contigue depuis
# le mot 0 (organe d'omission p7 interroge a min_words=1), seuil 3 mots.
_SENTENCE_HEAD = "Il marcha longtemps"
_SENTENCE_TAIL = "dans la nuit, puis il s'arreta."


def _install_fake_pydub(monkeypatch) -> None:
    """Faux pydub : chaque chunk lu est memorise dans son tag, la sortie est
    la concatenation des tags (le tag du chunk livre est donc observable)."""

    class _FakeAudio:
        def __init__(self, tag):
            self.tag = tag

        def __len__(self):  # milliseconds — the short-audio floor's input
            return 3000

        def __add__(self, other):
            return _FakeAudio(f"{self.tag}+{getattr(other, 'tag', 'gap')}")

        def export(self, buf, format=None, bitrate=None):
            buf.write(self.tag.encode())

        @staticmethod
        def from_file(buf, format=None):
            return _FakeAudio(buf.getvalue().decode())

        @staticmethod
        def silent(duration=None):
            return _FakeAudio("gap")

    pydub = types.ModuleType("pydub")
    pydub.AudioSegment = _FakeAudio
    monkeypatch.setitem(sys.modules, "pydub", pydub)


def test_guard_closed_by_default_never_calls_the_asr(monkeypatch):
    """Sans demande de garde, l'ASR n'est jamais appele : le banc de mesure
    ne paie aucune transcription, et la garde ne peut pas pretendre avoir
    tourne."""
    import v4.prosody_lab.qwen_tts_client as client

    _install_fake_pydub(monkeypatch)
    monkeypatch.setattr(client, "qwen_tts_voicedesign", lambda text, **kw: b"CHUNK")
    calls: list[str] = []

    def _asr(path: str) -> str:
        calls.append(path)
        return _SENTENCE

    out = client.qwen_tts_voicedesign_chunked(
        _SENTENCE, instructions="calme", attack_asr=_asr,
    )
    assert out == b"CHUNK"
    assert calls == [], "l'ASR ne doit pas etre appele sans demande de garde"


def test_guard_refuses_a_chunk_whose_attack_stays_dropped(monkeypatch):
    """Une attaque absente sur tous les rendus d'un chunk fait **refuser** la
    passage : le rendu n'est jamais livre tel quel."""
    import v4.prosody_lab.qwen_tts_client as client

    _install_fake_pydub(monkeypatch)
    renders: list[int] = []

    def _fake_render(text, **kw):
        renders.append(1)
        return b"CHUNK%d" % len(renders)

    monkeypatch.setattr(client, "qwen_tts_voicedesign", _fake_render)

    def _asr(path: str) -> str:
        return _SENTENCE_TAIL  # les 3 mots de tete ne sont pas prononces

    report: dict = {}
    out = client.qwen_tts_voicedesign_chunked(
        _SENTENCE, instructions="calme", attack_guard=True,
        attack_asr=_asr, attack_report=report,
    )
    assert out is None, "une passage dont l'attaque manque n'est pas livree"
    assert len(renders) == client.ATTACK_GUARD_ATTEMPTS, (
        "le levier de re-rendu doit etre exerce jusqu'a la limite"
    )
    assert report["aborted_chunk"] == 1
    assert report["reason"] == "leading_span"
    assert report["n_missing_leading"] == 3
    assert report["aborted"] is True


def test_guard_rerenders_and_ships_the_chunk_that_keeps_its_attack(monkeypatch):
    """Le levier fonctionne : un chunk dont l'attaque est perdue au premier
    rendu est re-rendu, et c'est le rendu qui porte l'attaque qui part."""
    import v4.prosody_lab.qwen_tts_client as client

    _install_fake_pydub(monkeypatch)
    renders: list[int] = []

    def _fake_render(text, **kw):
        renders.append(1)
        return b"CHUNK%d" % len(renders)

    monkeypatch.setattr(client, "qwen_tts_voicedesign", _fake_render)

    transcripts = [_SENTENCE_TAIL, _SENTENCE]

    def _asr(path: str) -> str:
        return transcripts.pop(0)

    out = client.qwen_tts_voicedesign_chunked(
        _SENTENCE, instructions="calme", attack_guard=True, attack_asr=_asr,
    )
    assert out == b"CHUNK2", "le chunk re-rendu (attaque presente) est livre"
    assert len(renders) == 2


def test_env_switch_disables_the_guard_even_when_the_pipeline_asks(monkeypatch):
    """`V4_ATTACK_GUARD=off` l'emporte sur la demande du pipeline : c'est le
    bras A/B que la comparaison mesuree doit pouvoir prendre."""
    import v4.prosody_lab.qwen_tts_client as client

    _install_fake_pydub(monkeypatch)
    monkeypatch.setenv("V4_ATTACK_GUARD", "off")
    monkeypatch.setattr(client, "qwen_tts_voicedesign", lambda text, **kw: b"CHUNK")
    calls: list[str] = []

    out = client.qwen_tts_voicedesign_chunked(
        _SENTENCE, instructions="calme", attack_guard=True,
        attack_asr=lambda path: calls.append(path) or _SENTENCE_TAIL,
    )
    assert out == b"CHUNK"
    assert calls == []


def _build_seg(text: str = _SENTENCE):
    from v4.schemas import AnnotatedSegment

    return AnnotatedSegment(
        seg_index=888003,  # distinctive: no cached mp3 can match
        speaker="narrateur",
        type="narration",
        text=text,
        annotated_text=text,
    )


def test_pipeline_activates_the_guard_on_both_narrator_paths(tmp_path, monkeypatch):
    """Le pipeline demande la garde sur les deux chemins narrateur Qwen :
    sans ce câblage, la garde du client resterait fermée (off par defaut)."""
    from v4 import p5_tts
    import v4.prosody_lab.qwen_tts_client as client_mod

    _install_fake_pydub(monkeypatch)
    monkeypatch.setattr("v4.p5_tts.audio_duration_mp3", lambda b: 2.9)
    monkeypatch.setenv(
        "NARRATOR_CUSTOMVOICE_GATEWAY_URL", "https://tts-api.myia.io/v1"
    )

    recorded: dict = {}

    def _fake_vd(text, **kwargs):
        recorded["voicedesign"] = kwargs
        return b"WAVBYTES"

    def _fake_cv(text, **kwargs):
        recorded["customvoice"] = kwargs
        return b"WAVBYTES"

    monkeypatch.setattr(client_mod, "qwen_tts_voicedesign_chunked", _fake_vd)
    monkeypatch.setattr(client_mod, "qwen_tts_customvoice_chunked", _fake_cv)

    seg = _build_seg()
    p5_tts._synthesize_narrator_qwen(
        seg=seg, fishaudio_text=seg.text,
        mp3_path=tmp_path / "seg_qwen.mp3", seed=42, text_hash="h1",
    )
    p5_tts._synthesize_narrator_customvoice(
        seg=seg, fishaudio_text=seg.text,
        mp3_path=tmp_path / "seg_cv.mp3", seed=42, text_hash="h2",
    )

    assert recorded["voicedesign"]["attack_guard"] is True
    assert recorded["customvoice"]["attack_guard"] is True
