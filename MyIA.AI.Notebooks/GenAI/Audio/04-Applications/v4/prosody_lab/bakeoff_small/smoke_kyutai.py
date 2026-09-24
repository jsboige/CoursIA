"""Smoke test Kyutai tts-1.6b-en_fr via moshi.models.tts.

Mesure first-hand : DL + load + 1 generation courte.
Si OK, lancera le banc complet sur A et B.
Tell c.804 : soundfile.write (libsndfile torch-independent) au lieu de torchaudio.save (torchcodec 0.16 requis).
"""
import sys
import time
import os
import numpy as np
import torch
import soundfile as sf
from moshi.models.loaders import CheckpointInfo
from moshi.models.tts import DEFAULT_DSM_TTS_REPO, DEFAULT_DSM_TTS_VOICE_REPO, TTSModel

DEVICE = "cpu"  # Tell c.1493bis : venv test moshi downgradé torch 2.9.1+cpu, CUDA OFF
HF_REPO = DEFAULT_DSM_TTS_REPO  # kyutai/tts-1.6b-en_fr

print(f"[INFO] Loading Kyutai tts model from {HF_REPO} on {DEVICE}")
print(f"[INFO] torch={torch.__version__} cuda={torch.cuda.is_available()}")
t0 = time.time()
checkpoint_info = CheckpointInfo.from_hf_repo(HF_REPO)
tts_model = TTSModel.from_checkpoint_info(
    checkpoint_info, n_q=32, temp=0.6, device=DEVICE
)
print(f"[OK] model loaded in {time.time()-t0:.1f}s")

# Micro-test : 1 phrase courte
micro_text = "Bonjour, ceci est un test."
print(f"[INFO] preparing script for: {micro_text!r}")
entries = tts_model.prepare_script([micro_text], padding_between=1)
voice_path = tts_model.get_voice_path("expresso/ex03-ex01_happy_001_channel1_334s.wav")
condition_attributes = tts_model.make_condition_attributes([voice_path], cfg_coef=2.0)

print("[INFO] generating (CPU, may take a while)...")
t0 = time.time()
pcms = tts_model.generate(entries, condition_attributes)
dt = time.time() - t0
print(f"[OK] generation done in {dt:.1f}s")
# pcms is a dict {key: tensor}
for k, v in pcms.items():
    if hasattr(v, "cpu"):
        v_np = v.cpu().numpy()
        print(f"  {k}: shape={v_np.shape} dtype={v_np.dtype} duration={v_np.shape[-1]/24000:.2f}s")

# Save as WAV 24kHz mono PCM_16 via soundfile (Tell c.804 : libsndfile torch-independent)
out_path = r"D:/dev/CoursIA-17586/MyIA.AI.Notebooks/GenAI/Audio/04-Applications/v4/prosody_lab/bakeoff_small/results/kyutai_tts_1_6b/smoke.wav"
os.makedirs(os.path.dirname(out_path), exist_ok=True)
for k, v in pcms.items():
    arr = v.cpu().numpy() if hasattr(v, "cpu") else v
    if arr.ndim > 1:
        arr = arr.squeeze()
    pcm16 = (arr * 32767).clip(-32768, 32767).astype(np.int16)
    sf.write(out_path, pcm16, 24000, subtype='PCM_16')
    print(f"[OK] smoke.wav written to {out_path} ({pcm16.shape[-1]/24000:.2f}s)")
    break  # only first entry
