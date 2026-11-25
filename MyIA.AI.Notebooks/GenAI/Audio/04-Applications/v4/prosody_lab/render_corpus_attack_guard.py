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
| `render` | env du moteur TTS (chatterbox / cosyvoice3) | oui | les wavs + `chunks.json` |
| `asr` | env ASR (transformers ou faster-whisper) | oui ou non | `transcripts.json` |

La garde elle-meme n'est pas reimplementee ici : c'est `v4.attack_guard` qui
statue, en CLI (`--manifest ... --transcripts ... --out ...`). Ce harnais
produit les entrees ; l'organe produit le verdict.

Moteurs de rendu
----------------

`--engine chatterbox` : le moteur du banc d'origine.

`--engine cosyvoice3` : le client **canonique du depot**
(`v4/prosody_lab/bakeoff_large/clients/cosyvoice3.py`) — chargement du modele
et synthese passent par ce client, jamais par une reimplementation locale
(organe d'abord). C'est le moteur qui porte le **defaut d'attaque** qu'on
cherche a mesurer (onset-drop : les premiers mots de la narration ne sont
pas prononces) ; chatterbox, qui ne presente pas ce defect, sert de temoin.

Re-roll
-------

`--attempt N` re-seme le rendu avec la **graine espacee de l'organe**
(`v4.attack_guard.spaced_seed` : `base + index + attempt * 104729`) — la
meme formule que le re-roll inline de p5. Un chunk qui echoue au rendu
d attempt 0 peut donc etre rejoue (attempt 1) et l'on mesure si la graine
espacee **recupere** le chunk. Le manifeste de la tentative N est ecrit dans
`chunks_attempt<N>.json` : la tentative 0 (`chunks.json`) n'est jamais
ecrasee.

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
    python render_corpus_attack_guard.py --phase render --out-dir out \\
        --engine cosyvoice3
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

# Moteurs de rendu supportes par la phase `render`.
ENGINES = ("chatterbox", "cosyvoice3")


def _paragraphs(text: str, count: int) -> list[str]:
    blocks = [b.strip() for b in text.split("\n\n") if b.strip()]
    return blocks[:count]


def _seed_of(chunk_index: int, attempt: int) -> int:
    """Graine du rendu d'un chunk — l'organe (`attack_guard.spaced_seed`).

    On n'ecrit pas la formule ici : la graine espacee du re-roll est celle
    de `v4.attack_guard`, qui est aussi celle du re-roll inline de p5.
    """
    from v4.attack_guard import spaced_seed

    return spaced_seed(BASE_SEED, int(chunk_index), int(attempt))


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


def _tronquer(src: Path, dst: Path, secondes: float) -> float:
    """Ecrit la version tronquee du rendu (controle positif) et rend sa duree."""
    import torch
    import torchaudio

    wav, sr = torchaudio.load(str(src))
    cut = int(secondes * sr)
    cut = min(cut, max(0, wav.shape[-1] // 2))
    torchaudio.save(str(dst), wav[..., cut:], sr)
    return wav.shape[-1] / sr


def _render_chatterbox(args, plan, out_dir):
    """Rendu chatterbox (moteur du banc d'origine)."""
    import torch
    from chatterbox.tts import ChatterboxTTS
    import soundfile as sf

    t0 = time.time()
    model = ChatterboxTTS.from_pretrained(device=args.device)
    print(f"[render] modele charge en {time.time() - t0:.1f}s (device={args.device})")
    sr = int(model.sr)

    chunks = []
    for chunk in plan["chunks"]:
        idx = int(chunk["chunk_index"])
        seed = _seed_of(idx, args.attempt)
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

        suffix = "" if args.attempt == 0 else f"_a{args.attempt}"
        audio_path = out_dir / f"chunk_{idx:02d}{suffix}.wav"
        sf.write(str(audio_path), audio, sr)

        # Controle positif : le meme rendu, sans son attaque.
        cut = int(TRONQUE_S * sr)
        cut = min(cut, max(0, len(audio) // 2))
        tronque_path = out_dir / f"chunk_{idx:02d}{suffix}_tronque.wav"
        sf.write(str(tronque_path), audio[cut:], sr)

        chunks.append(
            {
                "chunk_index": idx,
                "text": chunk["text"],
                "seed": seed,
                "engine": "chatterbox",
                "audio": str(audio_path),
                "audio_tronque": str(tronque_path),
                "duration_s": round(dur, 2),
            }
        )
        print(
            f"[render] chunk {idx:02d} | {dur:5.2f}s | "
            f"{len(chunk['text']):4d} car. | graine {seed}"
        )

    return chunks, sr


def _render_cosyvoice3(args, plan, out_dir):
    """Rendu CosyVoice3 via le client canonique du depot.

    Aucun rechargement de modele ni reimplementation de la synthese ici : le
    client `v4/prosody_lab/bakeoff_large/clients/cosyvoice3.py` fait les deux
    (organe d'abord — la regle `organ-first-implementation`).

    La graine est posee avant chaque synthese : l'echantillonnage du LLM de
    CosyVoice3 est alors reproductible, et le re-roll (`--attempt`) est
    mesure sur le meme moteur que le rendu d'origine.
    """
    import torch
    from v4.prosody_lab.bakeoff_large.clients import cosyvoice3 as cv3

    t0 = time.time()
    model = cv3.load_model(device=args.device, dtype=args.dtype)
    print(f"[render] modele CV3 charge en {time.time() - t0:.1f}s (device={args.device})")
    sr = int(model.sample_rate)

    chunks = []
    for chunk in plan["chunks"]:
        idx = int(chunk["chunk_index"])
        seed = _seed_of(idx, args.attempt)
        torch.manual_seed(seed)
        suffix = "" if args.attempt == 0 else f"_a{args.attempt}"
        audio_path = out_dir / f"chunk_{idx:02d}{suffix}.wav"
        t1 = time.time()
        res = cv3.synth(
            text=chunk["text"],
            out_wav=str(audio_path),
            model=model,
            language=args.language,
        )
        dur = float(res["duration_s"])

        tronque_path = out_dir / f"chunk_{idx:02d}{suffix}_tronque.wav"
        _tronquer(audio_path, tronque_path, TRONQUE_S)

        chunks.append(
            {
                "chunk_index": idx,
                "text": chunk["text"],
                "seed": seed,
                "engine": "cosyvoice3",
                "audio": str(audio_path),
                "audio_tronque": str(tronque_path),
                "duration_s": round(dur, 2),
                "render_mode": res.get("mode"),
                "wallclock_s": round(float(res.get("wallclock_s", 0.0)), 2),
                "rtf": round(float(res.get("rtf", 0.0)), 3),
            }
        )
        print(
            f"[render] chunk {idx:02d} | {dur:5.2f}s | "
            f"{len(chunk['text']):4d} car. | graine {seed} | "
            f"{time.time() - t1:5.1f}s"
        )

    return chunks, sr


def phase_render(args) -> int:
    """Rend chaque chunk avec le moteur TTS, et ecrit sa version tronquee."""
    plan = json.loads((Path(args.out_dir) / "chunks_plan.json").read_text(encoding="utf-8"))
    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)

    if args.engine == "chatterbox":
        chunks, sr = _render_chatterbox(args, plan, out_dir)
    elif args.engine == "cosyvoice3":
        chunks, sr = _render_cosyvoice3(args, plan, out_dir)
    else:
        print(f"moteur non implemente : {args.engine}", file=sys.stderr)
        return 2

    manifest = {
        "engine": args.engine,
        "base_seed": BASE_SEED,
        "attempt": args.attempt,
        "corpus": str(CORPUS),
        "sample_rate": sr,
        "chunks": chunks,
    }
    name = "chunks.json" if args.attempt == 0 else f"chunks_attempt{args.attempt}.json"
    out = out_dir / name
    out.write_text(json.dumps(manifest, ensure_ascii=False, indent=2), encoding="utf-8")
    print(f"[render] manifeste -> {out}")
    return 0


def _asr_transformers(args):
    """ASR transformers (pipeline) — chemin historique du banc."""
    import torch
    from transformers import pipeline

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

    return transcribe


def _asr_faster_whisper(args):
    """ASR faster-whisper (ctranslate2) — chemin de l'env CosyVoice3.

    Meme famille de modele que l'ASR de reference (`large-v3-turbo`), mais
    sans dependre de `transformers` : l'env du moteur CV3 n'a que
    `faster-whisper`.
    """
    from faster_whisper import WhisperModel

    device = "cuda" if args.faster_whisper_device != "cpu" else "cpu"
    compute_type = "float16" if device == "cuda" else "int8"
    model = WhisperModel(args.model, device=device, compute_type=compute_type)
    print(f"[asr] faster-whisper {args.model} sur {device} ({compute_type})")

    def transcribe(path: str) -> str:
        segments, _info = model.transcribe(
            path, language="fr", beam_size=5, vad_filter=False
        )
        return "".join(seg.text for seg in segments)

    return transcribe


def phase_asr(args) -> int:
    """Transcrit chaque rendu (naturel puis tronque) avec l'ASR local."""
    out_dir = Path(args.out_dir)
    manifest_name = args.manifest or (
        "chunks.json" if args.attempt == 0 else f"chunks_attempt{args.attempt}.json"
    )
    manifest = json.loads((out_dir / manifest_name).read_text(encoding="utf-8"))

    transcribe = (
        _asr_faster_whisper(args)
        if args.asr_backend == "faster-whisper"
        else _asr_transformers(args)
    )

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

    suffix = "" if args.attempt == 0 else f"_attempt{args.attempt}"
    (out_dir / f"transcripts{suffix}.json").write_text(
        json.dumps(natural, ensure_ascii=False, indent=2), encoding="utf-8"
    )
    (out_dir / f"transcripts_tronques{suffix}.json").write_text(
        json.dumps(tronques, ensure_ascii=False, indent=2), encoding="utf-8"
    )
    print(f"[asr] transcriptions -> {out_dir / f'transcripts{suffix}.json'}")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--phase", choices=("chunk", "render", "asr"), required=True)
    parser.add_argument("--out-dir", required=True, type=Path)
    parser.add_argument("--paragraphs", type=int, default=6)
    parser.add_argument("--engine", default="chatterbox", choices=ENGINES)
    parser.add_argument("--device", default="cuda")
    parser.add_argument("--exaggeration", type=float, default=0.5)
    parser.add_argument("--cfg-weight", type=float, default=0.5)
    parser.add_argument("--model", default="openai/whisper-large-v3-turbo")
    parser.add_argument(
        "--attempt",
        type=int,
        default=0,
        help="numero de tentative de rendu (0 = rendu d'origine) ; "
        "la graine est la graine espacee de l'organe (attempt > 0).",
    )
    parser.add_argument(
        "--asr-backend",
        choices=("transformers", "faster-whisper"),
        default="transformers",
    )
    parser.add_argument(
        "--faster-whisper-device",
        default="cuda",
        help="device du backend faster-whisper ('cpu' force le CPU).",
    )
    parser.add_argument(
        "--manifest",
        default=None,
        help="nom du manifeste lu par la phase asr (defaut : chunks.json, "
        "ou chunks_attempt<N>.json si --attempt > 0).",
    )
    parser.add_argument(
        "--language",
        default="French",
        help="langue du rendu cosyvoice3 (client canonique).",
    )
    parser.add_argument(
        "--dtype",
        default="bf16",
        choices=("bf16", "fp16", "fp32"),
        help="dtype du modele cosyvoice3.",
    )
    args = parser.parse_args(argv)

    if args.phase == "chunk":
        return phase_chunk(args)
    if args.phase == "render":
        return phase_render(args)
    return phase_asr(args)


if __name__ == "__main__":
    raise SystemExit(main())
