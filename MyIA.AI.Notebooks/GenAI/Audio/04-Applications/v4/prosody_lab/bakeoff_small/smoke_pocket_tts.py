"""Smoke test pocket-tts 3.2.0 (french_24l).

Mesure first-hand : DL + load + 1 generation courte.
Si OK, lancera le banc complet sur A et B.
Tell c.804 : soundfile.write (libsndfile torch-independent) au lieu de torchaudio.save.
"""
import sys
import time
import os
import numpy as np
import torch
import soundfile as sf

DEVICE = "cuda" if torch.cuda.is_available() else "cpu"
print(f"[INFO] torch={torch.__version__} cuda={torch.cuda.is_available()} device={DEVICE}")

import pocket_tts
from pocket_tts import TTSModel
from pocket_tts.modules.stateful_module import init_states

micro_text = "Bonjour, ceci est un test."
print(f"[INFO] Loading pocket-tts french_24l on {DEVICE}")
t0 = time.time()
tts = TTSModel.load_model(language="french_24l")
print(f"[OK] model loaded in {time.time()-t0:.1f}s")
print(f"[INFO] sample_rate={tts.sample_rate}")

# Init state (batch_size=1, sequence_length=64 frames)
# Need to stamp state names first (already done by load_model)
print("[INFO] init_states on flow_lm (batch_size=1, sequence_length=64)")
model_state = init_states(tts.flow_lm, batch_size=1, sequence_length=64)
print(f"[OK] model_state keys: {list(model_state.keys())[:5]} ...")

print(f"[INFO] generating: {micro_text!r}")
t0 = time.time()
pcm = tts.generate_audio(model_state, micro_text)
dt = time.time() - t0
print(f"[OK] generation done in {dt:.1f}s")
print(f"     type={type(pcm)}")

if hasattr(pcm, 'cpu'):
    arr = pcm.cpu().numpy()
else:
    arr = np.asarray(pcm)
print(f"     arr shape={arr.shape} dtype={arr.dtype}")

out_path = r"D:/dev/CoursIA-17586/MyIA.AI.Notebooks/GenAI/Audio/04-Applications/v4/prosody_lab/bakeoff_small/results/pocket_tts/smoke.wav"
os.makedirs(os.path.dirname(out_path), exist_ok=True)
if arr.ndim > 1:
    arr = arr.squeeze()
# Pocket-tts generates float in [-1, 1]
if arr.dtype in (np.float32, np.float64):
    pcm16 = (arr * 32767).clip(-32768, 32767).astype(np.int16)
else:
    pcm16 = arr.astype(np.int16)
sr = tts.sample_rate if hasattr(tts, 'sample_rate') else 24000
sf.write(out_path, pcm16, sr, subtype='PCM_16')
print(f"[OK] smoke.wav written to {out_path} ({pcm16.shape[-1]/sr:.2f}s, sr={sr})")
