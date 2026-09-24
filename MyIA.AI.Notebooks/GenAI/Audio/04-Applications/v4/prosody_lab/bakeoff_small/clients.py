"""Client skeletons for 4 small TTS models on RTX 4060 8 GB.

Each client exposes:
    NAME  (str)  : short id used in the bake table
    SIZE  (str)  : parameter count claim (e.g. '0.5B')
    LICENSE (str): declared license
    WARM(text, lang, **kwargs) -> bytes | None
        Render the text to WAV bytes (16 kHz mono PCM). Returns None if
        the model is not yet loadable on this env. Each client is expected
        to (a) instantiate lazily, (b) cache between calls, (c) free VRAM
        on explicit close() so the bake.py orchestrator can swap models.

Lang codes: 'fr' for Chatterbox Multilingual / Kyutai / pocket-tts;
'cosyvoice' uses its own dialect tags (see client).
"""
from __future__ import annotations

import logging
from typing import Optional

log = logging.getLogger("bakeoff_small")


# ---- Chatterbox Multilingual V3 (Resemble AI, ~0.5B) -------------------------
class ChatterboxClient:
    NAME = "chatterbox_mtl_v3"
    SIZE = "0.5B"
    LICENSE = "Apache-2.0"
    HF_MODEL = "ResembleAI/chatterbox-multilingual"  # candidate id; verify on HF

    def __init__(self) -> None:
        self._model = None

    def warm(self, text: str, lang: str = "fr", **kwargs) -> Optional[bytes]:
        try:
            from chatterbox.mtl_tts import ChatterboxMultilingualTTS  # noqa: E402
        except Exception as exc:
            log.warning("chatterbox import failed: %s", exc)
            return None
        if self._model is None:
            try:
                self._model = ChatterboxMultilingualTTS.from_pretrained("cuda")
            except Exception as exc:
                log.warning("chatterbox load failed: %s", exc)
                return None
        try:
            import torchaudio as ta  # noqa: E402
            wav = self._model.generate(text, language_id=lang)
            # chatterbox returns torch.Tensor at sr=24000 by convention
            ta.save("/tmp/_bake_chatterbox.wav", wav, 24000)
            with open("/tmp/_bake_chatterbox.wav", "rb") as f:
                return f.read()
        except Exception as exc:
            log.warning("chatterbox generate failed: %s", exc)
            return None

    def close(self) -> None:
        self._model = None
        try:
            import torch  # noqa: E402
            torch.cuda.empty_cache()
        except Exception:
            pass


# ---- Kyutai tts-1.6b-en_fr (kyutai-labs, 1.6B CC-BY-4.0) ----------------------
class KyutaiTTSClient:
    NAME = "kyutai_tts_1_6b"
    SIZE = "1.6B"
    LICENSE = "CC-BY-4.0"
    # HF: kyutai/tts-1.6b-en_fr (verify on load)
    HF_MODEL = "kyutai/tts-1.6b-en_fr"

    def __init__(self) -> None:
        self._model = None

    def warm(self, text: str, lang: str = "fr", **kwargs) -> Optional[bytes]:
        # Kyutai ships a python module 'kyutai_tts' but no PyPI release as of
        # 2026-09; we install via git+https://github.com/kyutai-labs/delayed-streams-modeling
        # if needed. Until then, this client returns None to flag the missing
        # dependency without blocking the bake.
        try:
            import moshi  # noqa: F401
        except Exception:
            log.warning("kyutai_tts: 'moshi' not installed (pip install moshi-tts or git+https://github.com/kyutai-labs/delayed-streams-modeling)")
            return None
        log.warning("kyutai_tts: implementation pending; client skeleton only")
        return None

    def close(self) -> None:
        self._model = None


# ---- pocket-tts (kyutai-labs, 100M) ------------------------------------------
class PocketTTSClient:
    NAME = "pocket_tts"
    SIZE = "100M"
    LICENSE = "Apache-2.0"
    HF_MODEL = "kyutai/pocket-tts"

    def __init__(self) -> None:
        self._model = None

    def warm(self, text: str, lang: str = "fr", **kwargs) -> Optional[bytes]:
        # pocket-tts is a lightweight streaming model; check moshi / pocket-tts pkg
        try:
            import pocket_tts  # noqa: F401
        except Exception:
            log.warning("pocket_tts: package not installed (pip install pocket-tts)")
            return None
        log.warning("pocket_tts: implementation pending; client skeleton only")
        return None

    def close(self) -> None:
        self._model = None


# ---- Fun-CosyVoice 3.0 0.5B (FunAudioLLM) ------------------------------------
class FunCosyVoiceClient:
    NAME = "fun_cosyvoice_3_0_5B"
    SIZE = "0.5B"
    LICENSE = "Apache-2.0"
    HF_MODEL = "FunAudioLLM/Fun-CosyVoice-3.0-0.5B"

    def __init__(self) -> None:
        self._model = None

    def warm(self, text: str, lang: str = "fr", **kwargs) -> Optional[bytes]:
        # CosyVoice requires CosyVoice python env; no PyPI release with 3.0+
        try:
            from cosyvoice.cli.cosyvoice import AutoModel  # noqa: F401
        except Exception:
            log.warning("fun_cosyvoice: CosyVoice package not installed (git+https://github.com/FunAudioLLM/CosyVoice)")
            return None
        log.warning("fun_cosyvoice: implementation pending; client skeleton only")
        return None

    def close(self) -> None:
        self._model = None


ALL_CLIENTS = [
    ChatterboxClient,
    KyutaiTTSClient,
    PocketTTSClient,
    FunCosyVoiceClient,
]
