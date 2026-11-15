#!/usr/bin/env python3
"""zonos3_measure.py — banc #19695, rendu ZONOS3-Mini sur l'extract C.

Pilote le runtime natif ZONOS3 (ggml, CUDA) : decoupe par phrase comme le
rendu A0C de reference (ZONOS v0.1), synthetise chaque morceau avec la CLI,
recolle avec les memes pauses, et ecrit les metriques du banc.

Sortie : un JSON de metriques (meme forme que A0C-zonos-chunked-metrics.json)
cote a cote du WAV rendu. Les WAV restent hors depot (GDrive) ; le depot ne
porte que le JSON de mesure.

Usage :
    python zonos3_measure.py --binary <zonos3-server|zonos3> --model <backbone.gguf>
        --embedding <spk.embedding.npy> --text <extract.txt> --out-dir <dir>
        --seed 42 --max-frames 449 [--device 2] [--json-out <path>]
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import threading
import time
import wave
from datetime import datetime, timezone
from pathlib import Path

# --- decoupe : meme regle que le rendu A0C de reference ------------------------
SENT_RE = re.compile(r"(?<=[.!?])\s+")
CLAUSE_RE = re.compile(r"(?<=[,;:])\s+")
PAUSE_S = 0.25
MAX_CHARS = 280


def chunk_text(text: str, max_chars: int = MAX_CHARS) -> tuple[list[str], int]:
    """Decoupe en phrases, scinde les phrases trop longues a une frontiere de
    proposition, puis regroupe glouton des unites entieres jusqu'a max_chars.
    Une phrase n'est jamais tronquee."""
    sentences = [s for s in SENT_RE.split(text.strip()) if s.strip()]
    groups: list[list[str]] = []
    pending: list[str] = []
    for sentence in sentences:
        if len(sentence) <= max_chars:
            pending.append(sentence)
            continue
        # Une phrase trop longue est scindee a une frontiere de proposition et
        # forme son propre groupe : ses propositions ne rejoignent jamais le
        # groupe en cours (regle du rendu A0C de reference).
        if pending:
            groups.append(pending)
            pending = []
        groups.append([c for c in CLAUSE_RE.split(sentence) if c.strip()])
    if pending:
        groups.append(pending)
    chunks: list[str] = []
    for group in groups:
        current = ""
        for unit in group:
            candidate = f"{current} {unit}".strip() if current else unit
            if current and len(candidate) > max_chars:
                chunks.append(current)
                current = unit
            else:
                current = candidate
        if current:
            chunks.append(current)
    return chunks, len(sentences)


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as fh:
        for block in iter(lambda: fh.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()


class VramSampler:
    """Pic de VRAM du device designate, echantillonne pendant le run."""

    def __init__(self, device: int | None) -> None:
        self.device = device
        self.peak_mb = 0
        self._stop = threading.Event()
        self._thread: threading.Thread | None = None

    def _sample(self) -> None:
        while not self._stop.is_set():
            cmd = ["nvidia-smi", "--query-gpu=memory.used", "--format=csv,noheader,nounits"]
            if self.device is not None:
                cmd += ["-i", str(self.device)]
            try:
                out = subprocess.run(cmd, capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=10)
                for line in out.stdout.strip().splitlines():
                    value = int(line.strip())
                    self.peak_mb = max(self.peak_mb, value)
            except Exception:  # pragma: no cover - la mesure ne doit pas tuer le run
                pass
            time.sleep(0.5)

    def __enter__(self) -> "VramSampler":
        if shutil.which("nvidia-smi"):
            self._thread = threading.Thread(target=self._sample, daemon=True)
            self._thread.start()
        return self

    def __exit__(self, *exc) -> None:
        self._stop.set()
        if self._thread is not None:
            self._thread.join(timeout=5)


def wav_duration(path: Path) -> float:
    with wave.open(str(path), "rb") as wf:
        return wf.getnframes() / float(wf.getframerate())


def silence_wav(path: Path, seconds: float, sample_rate: int = 44100) -> None:
    with wave.open(str(path), "wb") as wf:
        wf.setnchannels(1)
        wf.setsampwidth(2)
        wf.setframerate(sample_rate)
        wf.writeframes(b"\x00\x00" * int(seconds * sample_rate))


def concat_wavs(parts: list[Path], out: Path, pause_s: float, sample_rate: int = 44100) -> float:
    """Recolle les morceaux avec un silence de pause_s entre eux."""
    total_frames = 0
    with wave.open(str(out), "wb") as out_wf:
        out_wf.setnchannels(1)
        out_wf.setsampwidth(2)
        out_wf.setframerate(sample_rate)
        for index, part in enumerate(parts):
            if index > 0:
                out_wf.writeframes(b"\x00\x00" * int(pause_s * sample_rate))
                total_frames += int(pause_s * sample_rate)
            with wave.open(str(part), "rb") as wf:
                out_wf.writeframes(wf.readframes(wf.getnframes()))
                total_frames += wf.getnframes()
    return total_frames / float(sample_rate)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--binary", required=True)
    parser.add_argument("--model", required=True)
    parser.add_argument("--embedding", required=True)
    parser.add_argument("--text", required=True)
    parser.add_argument("--out-dir", required=True)
    parser.add_argument("--json-out", required=True)
    parser.add_argument("--seed", type=int, default=42)
    parser.add_argument("--max-frames", type=int, default=449)
    parser.add_argument("--device", type=int, default=None)
    parser.add_argument("--model-dir", default=None, help="dossier des poids (provenance)")
    args = parser.parse_args()

    text = Path(args.text).read_text(encoding="utf-8")
    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    chunks, n_sentences = chunk_text(text)

    env = dict(os.environ)
    if args.device is not None:
        env["CUDA_DEVICE_ORDER"] = "PCI_BUS_ID"
        env["CUDA_VISIBLE_DEVICES"] = str(args.device)

    per_chunk = []
    parts: list[Path] = []
    wallclock_total = 0.0
    audio_total = 0.0

    with VramSampler(args.device) as sampler:
        for index, chunk in enumerate(chunks, start=1):
            out_wav = out_dir / f"zonos3-mini-chunk-{index:02d}.wav"
            cmd = [
                args.binary,
                args.model,
                "--gpu",
                "--tts",
                chunk,
                str(out_wav),
                "--seed",
                str(args.seed),
                "--max",
                str(args.max_frames),
                "--speaker-embedding",
                args.embedding,
            ]
            started = time.perf_counter()
            proc = subprocess.run(cmd, env=env, capture_output=True, text=True, encoding="utf-8", errors="replace")
            elapsed = time.perf_counter() - started
            if proc.returncode != 0 or not out_wav.exists():
                sys.stderr.write(f"chunk {index} rc={proc.returncode}\n{proc.stderr[-4000:]}\n")
                return 2
            duration = wav_duration(out_wav)
            parts.append(out_wav)
            audio_total += duration
            wallclock_total += elapsed
            per_chunk.append(
                {
                    "index": index,
                    "chars": len(chunk),
                    "duration_s": round(duration, 3),
                    "wallclock_s": round(elapsed, 3),
                    "rtf": round(elapsed / duration, 3) if duration else None,
                    "text": chunk,
                }
            )
            print(f"chunk {index}/{len(chunks)} {len(chunk)} car. -> {duration:.2f} s (rtf {elapsed / duration:.3f})", flush=True)

    final_wav = out_dir / "A0C-zonos3-mini-chunked.wav"
    duration_out = concat_wavs(parts, final_wav, PAUSE_S)
    pause_total = PAUSE_S * (len(parts) - 1)

    model_dir = Path(args.model_dir) if args.model_dir else Path(args.model).parent
    provenance = {
        "runtime": "Zyphra/ZONOS3-Mini (ggml natif, CUDA)",
        "runtime_commit": None,
        "binary_sha256": sha256(Path(args.binary)) if Path(args.binary).exists() else None,
        "model_files": {},
    }
    for candidate in sorted(model_dir.glob("*.gguf")):
        provenance["model_files"][candidate.name] = {"sha256": sha256(candidate), "bytes": candidate.stat().st_size}

    src_norm = " ".join(text.split())
    rebuilt_norm = " ".join(" ".join(chunks).split())
    metrics = {
        "ts": datetime.now(timezone.utc).isoformat(timespec="seconds").replace("+00:00", "Z"),
        "suite": "Banc #19695 -- ZONOS3-Mini, rendu chunked sur extract_C",
        "model": "Zyphra/ZONOS3-Mini",
        "backend": "ggml natif (runtime C++/CUDA), pas le serveur SGLang",
        "language": "fr (voix par defaut du checkpoint : Gaspard)",
        "speaker": "Gaspard (voix francaise livree, embedding 192-d du checkpoint)",
        "seed": args.seed,
        "max_frames": args.max_frames,
        "text_path": str(args.text),
        "text_chars": len(text),
        "text_chars_normalized": len(src_norm),
        "text_sha256": sha256(Path(args.text)),
        "cut_rule": {
            "boundary": "fin de phrase (! ? .) suivie d'un espace",
            "split_regex": "(?<=[.!?])\\s+",
            "fallback_long_sentence": "si une phrase depasse max_chars, scission a une frontiere de proposition (, ; :) -- jamais au milieu d'un mot",
            "clause_regex": "(?<=[,;:])\\s+",
            "grouping": "glouton, unites entieres, jusqu'a max_chars",
            "grouping_oversized_sentence": "une phrase trop longue forme un groupe autonome : ses propositions ne rejoignent jamais le groupe precedent",
            "max_chars": MAX_CHARS,
            "sentence_never_truncated": True,
            "pause_between_chunks_s": PAUSE_S,
        },
        "n_sentences": n_sentences,
        "n_chunks": len(chunks),
        "chunk_identity": {
            "chunk_chars_total": sum(len(c) for c in chunks),
            "separators_reinstated": len(chunks) - 1,
            "lost_chars": 0 if rebuilt_norm == src_norm else len(src_norm) - len(rebuilt_norm),
            "reassembled_equals_source": rebuilt_norm == src_norm,
            "comparison": "espaces normalises (collapse) : le separateur de jointure entre deux morceaux est reinstalle avant comparaison",
            "src_norm_chars": len(src_norm),
            "rebuilt_norm_chars": len(rebuilt_norm),
        },
        "per_chunk": per_chunk,
        "sum_chunk_audio_s": round(audio_total, 3),
        "pause_total_s": round(pause_total, 3),
        "duration_out_s": round(duration_out, 3),
        "sample_rate": 44100,
        "wallclock_total_s": round(wallclock_total, 3),
        "rtf_global": round(wallclock_total / duration_out, 3) if duration_out else None,
        "vram_peak_gb": round(sampler.peak_mb / 1024.0, 3),
        "vram_peak_mb": sampler.peak_mb,
        "out_wav": str(final_wav),
        "provenance": provenance,
    }
    Path(args.json_out).write_text(json.dumps(metrics, ensure_ascii=False, indent=1), encoding="utf-8")
    print(json.dumps({k: metrics[k] for k in ("n_chunks", "duration_out_s", "rtf_global", "vram_peak_mb")}, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
