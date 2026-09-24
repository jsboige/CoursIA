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
            import io  # noqa: E402
            import soundfile as sf  # noqa: E402
            wav = self._model.generate(text, language_id=lang)
            # chatterbox returns torch.Tensor at sr=24000 by convention.
            # Write via soundfile (libsndfile) -- torchaudio 2.11 + torchcodec 0.16
            # require torch 2.6.x which we don't ship; soundfile is independent.
            wav_np = wav.squeeze(0).detach().cpu().numpy() if hasattr(wav, "squeeze") else wav
            buf = io.BytesIO()
            sf.write(buf, wav_np, 24000, format="WAV", subtype="PCM_16")
            return buf.getvalue()
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
        # Verdicts cycle c.805 :
        # - moshi 0.2.13 installé (downgrade torch 2.13 -> 2.9.1+cpu)
        # - moshi.models.tts.TTSModel.from_checkpoint_info(...) chargeable
        # - HF_TOKEN loadé depuis .secrets/master.env
        # - DL Kyutai tts-1.6b-en_fr : 3.6 GB safetensors sur CDN us.aws.cdn.hf.co
        #   -> HTTPSConnectionPool Read timed out a plusieurs reprises sur 20 min
        # - CDN joignable (HTTP 200 sur /) mais le flux xet-bridge-us timeout
        # - Verdict : RECOVERABLE-MACHINE (machine specifique avec env reseau
        #   different - GPU po-2023 ou po-2024 avec HF_TOKEN frais + cache
        #   pre-peuple). Pas de fallback CPU first-hand en l'etat.
        try:
            import moshi  # noqa: F401
        except Exception:
            log.warning("kyutai_tts: 'moshi' not installed (pip install moshi-tts or git+https://github.com/kyutai-labs/delayed-streams-modeling)")
            return None
        log.warning("kyutai_tts: RECOVERABLE-MACHINE -- CDN us.aws.cdn.hf.co Read timed out (xet-bridge) en local; bench differe sur po-2023/po-2024 GPU")
        return None

    def close(self) -> None:
        self._model = None


# ---- pocket-tts (kyutai-labs, 100M) ------------------------------------------
class PocketTTSClient:
    NAME = "pocket_tts"
    SIZE = "100M"
    LICENSE = "Apache-2.0"
    HF_MODEL = "kyutai/pocket-tts-without-voice-cloning"

    def __init__(self) -> None:
        self._model = None
        self._state = None

    def warm(self, text: str, lang: str = "fr", **kwargs) -> Optional[bytes]:
        try:
            from pocket_tts import TTSModel  # noqa: E402
            from pocket_tts.modules.stateful_module import init_states  # noqa: E402
            import soundfile as sf  # noqa: E402
            import io  # noqa: E402
            import numpy as np  # noqa: E402
            import torch  # noqa: E402
        except Exception as exc:
            log.warning("pocket_tts: import failed: %s", exc)
            return None
        if self._model is None:
            try:
                # 'french_24l' is the official French language pack
                self._model = TTSModel.load_model(language="french_24l")
                self._state = init_states(self._model.flow_lm,
                                          batch_size=1, sequence_length=64)
            except Exception as exc:
                log.warning("pocket_tts: model load failed: %s", exc)
                return None
        try:
            pcm = self._model.generate_audio(self._state, text)
            arr = pcm.cpu().numpy() if hasattr(pcm, "cpu") else np.asarray(pcm)
            if arr.ndim > 1:
                arr = arr.squeeze()
            pcm16 = (arr * 32767).clip(-32768, 32767).astype(np.int16)
            buf = io.BytesIO()
            sr = self._model.sample_rate if hasattr(self._model, "sample_rate") else 24000
            sf.write(buf, pcm16, sr, format="WAV", subtype="PCM_16")
            return buf.getvalue()
        except Exception as exc:
            log.warning("pocket_tts: generate_audio failed: %s", exc)
            return None

    def close(self) -> None:
        self._model = None
        self._state = None
        try:
            import torch  # noqa: E402
            torch.cuda.empty_cache()
        except Exception:
            pass


# ---- Fun-CosyVoice 3.0 0.5B (FunAudioLLM) ------------------------------------
class FunCosyVoiceClient:
    NAME = "fun_cosyvoice_3_0_5B"
    SIZE = "0.5B"
    LICENSE = "Apache-2.0"
    HF_MODEL = "FunAudioLLM/Fun-CosyVoice3-0.5B-2512"

    def __init__(self) -> None:
        self._model = None

    def warm(self, text: str, lang: str = "fr", **kwargs) -> Optional[bytes]:
        # Verdict cycle c.805 :
        # - CosyVoice 3.0 = FunAudioLLM/Fun-CosyVoice3-0.5B-2512
        # - llm.pt 2 GB + flow.pt 1.3 GB + speech_tokenizer_v3.onnx 970 MB
        # - cosyvoice PyPI 0.0.8 = CosyVoice 1.x, pas 3.0
        # - CosyVoice 3.0 necessite git clone + install manuel depuis
        #   https://github.com/FunAudioLLM/CosyVoice + checkout branche 3.0
        # - Total ~4.5 GB modeles + install = > 1 cycle (mesure first-hand differee)
        # - Verdict : RECOVERABLE-MACHINE (env specifique a monter)
        try:
            from cosyvoice.cli.cosyvoice import AutoModel  # noqa: F401
        except Exception:
            log.warning("fun_cosyvoice: CosyVoice 3.0 package absent (PyPI n'expose que 0.0.8=CosyVoice 1.x; CosyVoice 3.0 = git clone FunAudioLLM/CosyVoice + branche 3.0 + 4.5 GB modeles)")
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
