"""test_p5_narrator_routing.py -- tests unitaires pour le routage narrateur
v4 (Qwen VoiceDesign, CosyVoice3, Qwen CustomVoice).

Cible : selection de route exclusive, reference_id par engine, defaut
inchange tant que le user n'a pas confirme, contrat d'echec dur
(NarratorQwenUnavailable) sans repli silencieux.

Pas de GPU, pas de gateway Qwen : tous les tests sont purs-Python, ils
verifient la logique de routage et la coherence des sentinelles de cache.

Usage (depuis la racine du worktree) :
    python MyIA.AI.Notebooks/GenAI/Audio/04-Applications/v4/prosody_lab/test_p5_narrator_routing.py

Cablage CI : la jambe `Scripts Tests (CPU)` de
`.github/workflows/scripts-tests.yml` collecte ce fichier (cf cablage
test_bake_bank.py, meme workspace prosody_lab, meme convention).
"""
from __future__ import annotations

import importlib
import os
import sys
from pathlib import Path

# Make the v4 package importable as `v4.p5_tts` from the workspace root.
THIS_DIR = Path(__file__).resolve().parent
V4_DIR = THIS_DIR.parent
V4_PARENT = V4_DIR.parent  # .../04-Applications (added to sys.path)

if str(V4_PARENT) not in sys.path:
    sys.path.insert(0, str(V4_PARENT))


def fail(msg: str) -> None:
    print(f"FAIL: {msg}", file=sys.stderr)
    sys.exit(1)


def assert_eq(label: str, got, expected) -> None:
    if got != expected:
        fail(f"{label}: got {got!r}, expected {expected!r}")


def assert_true(label: str, got: bool) -> None:
    if not got:
        fail(f"{label}: expected True, got False")


def assert_raises(label: str, exc_type: type, fn) -> None:
    try:
        fn()
    except exc_type:
        return
    except Exception as exc:  # noqa: BLE001
        fail(f"{label}: expected {exc_type.__name__}, got {type(exc).__name__}: {exc}")
    fail(f"{label}: expected {exc_type.__name__}, no exception raised")


def _load_p5_tts(monkey_env: dict[str, str] | None = None):
    """Import p5_tts with a controlled env.

    Re-importing the module reads the env flags at module load time, so we
    must drop any cached import and set os.environ before importlib.reload.
    """
    saved = dict(os.environ)
    try:
        # Wipe narrator-related env so the explicit set below is the only
        # source of truth.
        for k in (
            "NARRATOR_QWEN_ROUTING",
            "NARRATOR_COSYVOICE3_ROUTING",
            "NARRATOR_QWEN_CUSTOMVOICE_ROUTING",
            "NARRATOR_QWEN_CUSTOMVOICE_SPEAKER",
            "NARRATOR_QWEN_CUSTOMVOICE_INSTRUCTIONS",
        ):
            os.environ.pop(k, None)
        if monkey_env is not None:
            for k, v in monkey_env.items():
                os.environ[k] = v
        sys.modules.pop("v4.p5_tts", None)
        # The v4 package is a directory, not a module, so import it via
        # the parent path set up above.
        mod = importlib.import_module("v4.p5_tts")
        return mod
    finally:
        os.environ.clear()
        os.environ.update(saved)


def test_default_does_not_change() -> None:
    """Sans flag pose, defaut = Qwen VoiceDesign (legacy pivot #15002, le defaut
    inchange). Le nouveau engine CustomVoice est opt-in (flag = '0' par defaut)."""
    p5 = _load_p5_tts()
    flags = p5._narrator_engine_flags()
    assert_eq("default qwen_voicedesign", flags["qwen_voicedesign"], True)
    assert_eq("default cosyvoice3", flags["cosyvoice3"], False)
    assert_eq("default qwen_customvoice", flags["qwen_customvoice"], False)
    assert_eq(
        "default selected engine = qwen_voicedesign",
        p5._selected_narrator_engine(),
        "qwen_voicedesign",
    )


def test_customvoice_flag_alone() -> None:
    """NARRATOR_QWEN_CUSTOMVOICE_ROUTING=1 seul -> qwen_customvoice est la route."""
    p5 = _load_p5_tts(
        {
            "NARRATOR_QWEN_ROUTING": "0",
            "NARRATOR_COSYVOICE3_ROUTING": "0",
            "NARRATOR_QWEN_CUSTOMVOICE_ROUTING": "1",
        }
    )
    flags = p5._narrator_engine_flags()
    assert_eq("customvoice flag", flags["qwen_customvoice"], True)
    assert_eq("qwen_voicedesign flag", flags["qwen_voicedesign"], False)
    assert_eq("cosyvoice3 flag", flags["cosyvoice3"], False)
    assert_eq(
        "selected engine = customvoice",
        p5._selected_narrator_engine(),
        "qwen_customvoice",
    )


def test_exclusivity_two_flags_raises() -> None:
    """Deux flags actifs = configuration error (no silent precedence, #15002 #6)."""
    p5 = _load_p5_tts(
        {
            "NARRATOR_QWEN_ROUTING": "1",
            "NARRATOR_QWEN_CUSTOMVOICE_ROUTING": "1",
        }
    )
    assert_raises(
        "two engines ON",
        ValueError,
        p5._selected_narrator_engine,
    )


def test_exclusivity_all_three_raises() -> None:
    p5 = _load_p5_tts(
        {
            "NARRATOR_QWEN_ROUTING": "1",
            "NARRATOR_COSYVOICE3_ROUTING": "1",
            "NARRATOR_QWEN_CUSTOMVOICE_ROUTING": "1",
        }
    )
    assert_raises(
        "three engines ON",
        ValueError,
        p5._selected_narrator_engine,
    )


def test_routing_only_narrator_segments() -> None:
    """Une seg non-narrateur ne route JAMAIS vers un engine narrateur, quel que soit le flag."""
    p5 = _load_p5_tts(
        {
            "NARRATOR_QWEN_ROUTING": "0",
            "NARRATOR_COSYVOICE3_ROUTING": "0",
            "NARRATOR_QWEN_CUSTOMVOICE_ROUTING": "1",
        }
    )
    seg = p5.AnnotatedSegment.model_validate(
        {
            "seg_index": 1,
            "type": "narration",
            "speaker": "figurant",  # not narrateur
            "speaker_raw": "M. le Comte",
            "text": "Bonjour, madame.",
            "annotated_text": "Bonjour, madame.",
        }
    )
    assert_true(
        "non-narrator does not route to customvoice",
        not p5._should_route_narrator_to("qwen_customvoice", seg),
    )
    # And vice versa, narrateur routes when flag is on:
    seg_n = p5.AnnotatedSegment.model_validate(
        {
            "seg_index": 2,
            "type": "narration",
            "speaker": "narrateur",
            "speaker_raw": "",
            "text": "Il faisait froid ce matin-la.",
            "annotated_text": "Il faisait froid ce matin-la.",
        }
    )
    assert_true(
        "narrator routes to customvoice when flag is on",
        p5._should_route_narrator_to("qwen_customvoice", seg_n),
    )


def test_cache_sentinel_embeds_speaker() -> None:
    """reference_id customvoice encode le speaker ; re-pin du speaker casse le cache."""
    p5_a = _load_p5_tts(
        {
            "NARRATOR_QWEN_CUSTOMVOICE_ROUTING": "1",
            "NARRATOR_QWEN_CUSTOMVOICE_SPEAKER": "aiden",
        }
    )
    p5_b = _load_p5_tts(
        {
            "NARRATOR_QWEN_CUSTOMVOICE_ROUTING": "1",
            "NARRATOR_QWEN_CUSTOMVOICE_SPEAKER": "dylan",
        }
    )
    ref_a = p5_a._NARRATOR_ENGINE_REFERENCE_IDS["qwen_customvoice"]
    ref_b = p5_b._NARRATOR_ENGINE_REFERENCE_IDS["qwen_customvoice"]
    assert_true(
        "sentinel embeds speaker name (aiden)",
        "aiden" in ref_a,
    )
    assert_true(
        "sentinel embeds speaker name (dylan)",
        "dylan" in ref_b,
    )
    if ref_a == ref_b:
        fail(
            "different speakers produced the same cache sentinel: "
            f"{ref_a!r} (re-pin would silently serve a stale MP3)"
        )


def test_engine_reference_ids_keys() -> None:
    """Les 3 engines ont une sentinelle declared (defaut OFF, mais le mapping existe)."""
    p5 = _load_p5_tts()
    keys = set(p5._NARRATOR_ENGINE_REFERENCE_IDS.keys())
    expected = {"qwen_voicedesign", "cosyvoice3", "qwen_customvoice"}
    assert_eq("engine reference ids keys", keys, expected)


def test_default_speaker_is_supported() -> None:
    """Le speaker par defaut 'aiden' est dans la liste supportee (snake_case)."""
    p5 = _load_p5_tts()
    # Imported from the bakeoff client, NOT from qwen_tts_client (different
    # client, same model family). We load it via the same direct path the
    # pipeline uses elsewhere: importlib.util under the bakeoff_large path.
    import importlib.util
    cv_path = (
        Path(p5.__file__).parent
        / "prosody_lab"
        / "bakeoff_large"
        / "clients"
        / "qwen3_tts_customvoice.py"
    )
    spec = importlib.util.spec_from_file_location("cv_client", cv_path)
    cv = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(cv)
    supported = cv.get_supported_speakers()
    if p5._QWEN_CUSTOMVOICE_SPEAKER not in supported:
        fail(
            f"default speaker {p5._QWEN_CUSTOMVOICE_SPEAKER!r} not in supported "
            f"list: {supported}"
        )


def main() -> int:
    tests = [
        test_default_does_not_change,
        test_customvoice_flag_alone,
        test_exclusivity_two_flags_raises,
        test_exclusivity_all_three_raises,
        test_routing_only_narrator_segments,
        test_cache_sentinel_embeds_speaker,
        test_engine_reference_ids_keys,
        test_default_speaker_is_supported,
    ]
    for t in tests:
        t()
        print(f"OK  {t.__name__}")
    print(f"\n{len(tests)} tests passed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
