"""Banc de mesure de la garde d'attaque (#19739) — corpus reel, chunk par chunk.

Le harnais rend une portion du corpus **du depot**
(`MyIA.AI.Notebooks/GenAI/Audio/04-Applications/boule_de_suif_full.txt`, texte
de Maupassant, domaine public), la decoupe avec le chunker mesure de p5
(<= 280 caracteres, frontieres de phrases), rend chaque chunk avec un moteur
TTS reel, puis transcrit chaque rendu pour que la garde d'attaque
(`v4.attack_guard`) puisse statuer chunk par chunk.

Trois phases, volontairement separees parce qu'elles ne tournent pas dans le
meme env :

| Phase | Env | GPU | Sortie |
|---|---|---|---|
| `chunk` | env du depot (pydantic, dotenv) | non | `chunks_plan.json` |
| `render` | env du moteur TTS (chatterbox) | oui (GPU 2) | les wavs + `chunks.json` |
| `asr` | env ASR (transformers) | oui ou non | `transcripts.json` |

La garde elle-meme n'est pas reimplementee ici : c'est `v4.attack_guard` qui
statue, en CLI (`--manifest ... --transcripts ... --out ...`). Ce harnais
produit les entrees ; l'organe produit le verdict.

Controle positif d'injection
----------------------------
Chaque rendu est aussi ecrit en version **tronquee** (les `tronque_s`
premieres secondes coupees) : c'est un onset-drop real, sur de l'audio reel,
produit par un moyen connu. La garde doit le signaler — c'est la mesure de
sensibilite du detecteur, et la preuve que le verdict ne repose pas sur une
convention de texte mais sur ce qui a ete dit.

Le `tronque_s` par defaut (1,5 s) retire l'attaque d'un chunk de narration
francaise (les 3-4 premiers mots), ce qui franchit le seuil de la garde
(3 mots consecutifs absents, meme seuil que l'organe d'omission p7).

Usage
-----
    python render_corpus_attack_guard.py --phase chunk --out-dir out \\
        --paragraphs 6
    python render_corpus_attack_guard.py --phase render --out-dir out \\
        --engine chatterbox
    python render_corpus_attack_guard.py --phase asr --out-dir out
    python -m v4.attack_guard --manifest out/chunks.json \\
        --transcripts out/transcripts.json --out out/attack_report.json
"""
from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

_V4 = Path(__file__).resolve().parent.parent
_APPS = _V4.parent
for _p in (str(_APPS),):
    if _p not in sys.path:
        sys.path.insert(0, _p)

CORPUS = _APPS / "boule_de_suif_full.txt"

# Graine de base du segment 0 — meme convention que p5 (`42 + seg_index`).
BASE_SEED = 42

# Duree de la coupe du controle positif.
TRONQUE_S = 1.5


def _paragraphs(text: str, count: int) -> list[str]:
    blocks = [b.strip() for b in text.split("\n\n") if b.strip()]
    return blocks[:count]


def phase_chunk(args) -> int:
    """Decoupe le corpus avec le chunker de p5 (l'organe mesure)."""
    from v4.p5_tts import _chunk_narration

    if not CORPUS.exists():
        print(f"corpus introuvable : {CORPUS}", file=sys.stderr)
        return 2

    paragraphs = _paragraphs(CORPUS.read_text(encoding="utf-8"), args.paragraphs)
    narration = " ".join(paragraphs)
    chunks = _chunk_narration(narration)

    plan = {
        "corpus": str(CORPUS),
        "engine": args.engine,
        "base_seed": BASE_SEED,
        "n_paragraphs": len(paragraphs),
        "chunks": [
            {"chunk_index": i, "text": c, "seed": BASE_SEED + i} for i, c in enumerate(chunks)
        ],
    }
    out = Path(args.out_dir) / "chunks_plan.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(plan, ensure_ascii=False, indent=2), encoding="utf-8")
    print(f"[chunk] {len(chunks)} chunk(s) depuis {len(paragraphs)} paragraphe(s) -> {out}")
    return 0


def phase_render(args) -> int:
    """Rend chaque chunk avec le moteur TTS, et ecrit sa version tronquee."""
    import torch

    plan = json.loads((Path(args.out_dir) / "chunks_plan.json").read_text(encoding="utf-8"))
    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)

    if args.engine != "chatterbox":
        print(f"moteur non implemente : {args.engine}", file=sys.stderr)
        return 2

    from chatterbox.tts import ChatterboxTTS
    import soundfile as sf

    t0 = time.time()
    model = ChatterboxTTS.from_pretrained(device=args.device)
    print(f"[render] modele charge en {time.time() - t0:.1f}s (device={args.device})")
    sr = int(model.sr)

    chunks = []
    for chunk in plan["chunks"]:
        seed = int(chunk["seed"])
        torch.manual_seed(seed)
        t1 = time.time()
        wav = model.generate(
            text=chunk["text"],
            exaggeration=args.exaggeration,
            cfg_weight=args.cfg_weight,
        )
        audio = wav.detach().cpu().numpy() if hasattr(wav, "detach") else wav
        audio = audio.reshape(-1)
        dur = len(audio) / sr

        audio_path = out_dir / f"chunk_{chunk['chunk_index']:02d}.wav"
        sf.write(str(audio_path), audio, sr)

        # Controle positif : le meme rendu, sans son attaque.
        cut = int(TRONQUE_S * sr)
        cut = min(cut, max(0, len(audio) // 2))
        tronque_path = out_dir / f"chunk_{chunk['chunk_index']:02d}_tronque.wav"
        sf.write(str(tronque_path), audio[cut:], sr)

        chunks.append(
            {
                "chunk_index": chunk["chunk_index"],
                "text": chunk["text"],
                "seed": seed,
                "engine": "chatterbox",
                "audio": str(audio_path),
                "audio_tronque": str(tronque_path),
                "duration_s": round(dur, 2),
            }
        )
        print(
            f"[render] chunk {chunk['chunk_index']:02d} | {dur:5.2f}s | "
            f"{len(chunk['text']):4d} car. | graine {seed}"
        )

    manifest = {
        "engine": "chatterbox",
        "base_seed": BASE_SEED,
        "corpus": str(CORPUS),
        "sample_rate": sr,
        "chunks": chunks,
    }
    out = out_dir / "chunks.json"
    out.write_text(json.dumps(manifest, ensure_ascii=False, indent=2), encoding="utf-8")
    print(f"[render] manifeste -> {out}")
    return 0


def phase_asr(args) -> int:
    """Transcrit chaque rendu (naturel puis tronque) avec l'ASR local."""
    import torch
    from transformers import pipeline

    manifest = json.loads((Path(args.out_dir) / "chunks.json").read_text(encoding="utf-8"))
    device = args.device if torch.cuda.is_available() else "cpu"
    asr = pipeline(
        "automatic-speech-recognition",
        model=args.model,
        device=device,
    )
    print(f"[asr] {args.model} sur {device}")

    def transcribe(path: str) -> str:
        out = asr(path, language="fr", generate_kwargs={"task": "transcribe"})
        return out["text"] if isinstance(out, dict) else str(out)

    natural: dict[str, str] = {}
    tronques: dict[str, str] = {}
    for chunk in manifest["chunks"]:
        idx = str(chunk["chunk_index"])
        t1 = time.time()
        natural[idx] = transcribe(chunk["audio"])
        tronques[idx] = transcribe(chunk["audio_tronque"])
        print(
            f"[asr] chunk {idx} | {time.time() - t1:5.1f}s | "
            f"naturel: {natural[idx][:60]!r}"
        )

    out_dir = Path(args.out_dir)
    (out_dir / "transcripts.json").write_text(
        json.dumps(natural, ensure_ascii=False, indent=2), encoding="utf-8"
    )
    (out_dir / "transcripts_tronques.json").write_text(
        json.dumps(tronques, ensure_ascii=False, indent=2), encoding="utf-8"
    )
    print(f"[asr] transcriptions -> {out_dir / 'transcripts.json'}")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--phase", choices=("chunk", "render", "asr"), required=True)
    parser.add_argument("--out-dir", required=True, type=Path)
    parser.add_argument("--paragraphs", type=int, default=6)
    parser.add_argument("--engine", default="chatterbox")
    parser.add_argument("--device", default="cuda")
    parser.add_argument("--exaggeration", type=float, default=0.5)
    parser.add_argument("--cfg-weight", type=float, default=0.5)
    parser.add_argument("--model", default="openai/whisper-large-v3-turbo")
    args = parser.parse_args(argv)

    if args.phase == "chunk":
        return phase_chunk(args)
    if args.phase == "render":
        return phase_render(args)
    return phase_asr(args)


if __name__ == "__main__":
    raise SystemExit(main())
