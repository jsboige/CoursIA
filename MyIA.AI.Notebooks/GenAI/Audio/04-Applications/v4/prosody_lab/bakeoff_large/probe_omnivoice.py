"""Sonde des criteres #21568 pour un client TTS (OmniVoice) — hors banc A0.

Le banc (`banc_phase_a0.py`) mesure un moteur sur UN extrait en voix auto. Cette
sonde couvre ce que le banc ne fait pas, pour l'analyse d'un candidat :

  1. clone  — clonage a partir d'une reference courte (3-10 s) + son texte ;
  2. design — voice design par `instruct` (aucune reference) ;
  3. tags   — les tags non-verbaux (`[laughter]`, `[sigh]`) sortent-ils
              reellement, ou sont-ils lus comme des mots ?
  4. long   — texte long (> seuil de chunking du moteur), avec reutilisation
              d'un `VoiceClonePrompt` deja encode, pour observer la derive.

Chaque sonde ecrit son .wav et son dict de mesures dans `--out-dir` (hors
depot), et la sonde entiere un `probe_summary.json`. Le WER est mesure par
l'organe du banc (`banc_phase_a0.measure_wer`, faster-whisper-tiny) : meme
instrument que la ligne de banc, donc comparable a la baseline publiee.

Usage :
    _runtime/venv-omnivoice/Scripts/python.exe bakeoff_large/probe_omnivoice.py \
        --ref-audio _runtime/refs/voixB_s1.wav \
        --ref-text-file "G:/.../Chapitre1-voixB-20261019-162458/texte-lu.txt" \
        --out-dir "G:/.../run-20261020-omnivoice/probes" \
        [--extract bench_extracts/extract_A_narration.txt]

Rejouer la seule sonde « long » avec une reference auto-generee par le moteur
(mesure isolee : la degradation vient-elle de la longueur ou de la reference ?) :

    ... probe_omnivoice.py --ref-audio probes/selfref_input.wav \
        --ref-text "<la phrase exacte lue par cette reference>" \
        --extract bench_extracts/extract_A_narration.txt \
        --out-dir "G:/.../run-20261020-omnivoice/probes-selfref"

Sans `--ref-text-file`, le texte de reference vient de `--extract` : la sonde
reste utilisable quand on n'a pas le tapuscrit complet de la reference.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
import time
from pathlib import Path

BAKEOFF_ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(BAKEOFF_ROOT))

import banc_phase_a0 as banc  # noqa: E402  — organe WER, meme instrument

TAG_TEXT = (
    "[sigh] Le froid tombait sur la route, et personne ne parlait plus. "
    "[laughter] Mais quand la diligence s'arreta, tout le monde eclata de rire."
)
TAG_CONTROL = (
    "Le froid tombait sur la route, et personne ne parlait plus. "
    "Mais quand la diligence s'arreta, tout le monde eclata de rire."
)


def _first_sentence(text: str) -> str:
    """Premiere phrase : sert de ref_text pour une reference coupee au premier
    silence long (aucun alignement force n'est necessaire)."""
    m = re.search(r"(.+?[.!?])(\s|$)", text.strip(), flags=re.S)
    return (m.group(1) if m else text.strip())[:400]


def _long_excerpt(text: str, max_chars: int = 1400) -> str:
    """Extrait long coupe sur une frontiere de phrase (chunking du moteur)."""
    text = re.sub(r"\s+", " ", text).strip()
    if len(text) <= max_chars:
        return text
    cut = text[:max_chars]
    end = cut.rfind(". ")
    return cut[: end + 1] if end > 0 else cut


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--client", default="omnivoice")
    p.add_argument("--extract", default=str(BAKEOFF_ROOT.parent / "bench_extracts" / "extract_A_narration.txt"))
    p.add_argument("--ref-audio", required=True)
    p.add_argument("--ref-text-file", default=None,
                   help="texte lu par la reference : sa 1re phrase sert de ref_text, "
                        "et son extrait long alimente la sonde « long ». "
                        "A defaut, --ref-text fournit le ref_text.")
    p.add_argument("--ref-text", default=None,
                   help="ref_text explicite, apparie a un --ref-audio quelconque. "
                        "Sert a isoler une mesure : rejouer « long » avec une reference "
                        "auto-generee par le moteur lui-meme dit si la degradation vient "
                        "de la longueur ou de la reference.")
    p.add_argument("--out-dir", required=True)
    p.add_argument("--device", default="cuda")
    p.add_argument("--dtype", default="fp16")
    p.add_argument("--seed", type=int, default=0)
    p.add_argument("--skip-long", action="store_true")
    args = p.parse_args()

    import importlib

    client = importlib.import_module(f"clients.{args.client}")
    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)

    extract_text = Path(args.extract).read_text(encoding="utf-8").strip()
    source = (Path(args.ref_text_file).read_text(encoding="utf-8")
              if args.ref_text_file else extract_text)
    ref_text = args.ref_text or _first_sentence(source)
    long_text = _long_excerpt(source)

    print(f"[probe] extract {len(extract_text)} c | ref_text {len(ref_text)} c | long {len(long_text)} c")
    model = client.load_model(device=args.device, dtype=args.dtype)
    summary: dict = {
        "client": args.client,
        "model": getattr(client, "DEFAULT_MODEL_ID", None),
        "ref_audio": str(args.ref_audio),
        "ref_text": ref_text,
        "seed": args.seed,
        "probes": {},
    }

    def run(name: str, text: str, **kw) -> dict:
        wav = out_dir / f"{name}.wav"
        t0 = time.time()
        res = client.synth(text=text, out_wav=str(wav), model=model,
                           language="French", seed=args.seed, **kw)
        res["wer"] = banc.measure_wer(str(wav), text)
        res["probe_wallclock_s"] = round(time.time() - t0, 2)
        summary["probes"][name] = res
        w = res["wer"]
        print(f"[{name}] mode={res['mode']} dur={res['duration_s']:.1f}s rtf={res['rtf']:.3f} "
              f"vram={res['vram_peak_gb']:.2f}GB wer={w.get('wer')} err={w.get('error')}")
        return res

    # 1. clonage : reference courte, meme extrait que la ligne de banc.
    run("clone", extract_text, ref_audio=str(args.ref_audio), ref_text=ref_text)
    # 2. voice design : aucun audio de reference, attributs en anglais.
    run("design", extract_text, instruct="male, low pitch")
    # 3. tags non-verbaux + controle sans tags.
    tag = run("tags", TAG_TEXT)
    ctrl = run("tags_control", TAG_CONTROL)
    hyp = (tag["wer"].get("hyp") or "").lower()
    ctrl_hyp = (ctrl["wer"].get("hyp") or "").lower()
    # Le discriminant est le TAG lui-meme, jamais un mot du texte : les deux
    # hypotheses contiennent "rire" parce que la phrase porte "eclata de rire"
    # — un test sur cette famille de mots rendrait vrai des deux cotes et ne
    # mesurerait rien. On cherche donc la fuite des tokens anglais du tag.
    summary["tags_verdict"] = {
        "tag_tokens_leaked": any(t in hyp for t in ("laughter", "sigh", "[", "]")),
        "tag_tokens_leaked_control": any(t in ctrl_hyp for t in ("laughter", "sigh", "[", "]")),
        "duration_delta_s": round(tag["duration_s"] - ctrl["duration_s"], 3),
        "wer_delta": round((tag["wer"].get("wer") or 0) - (ctrl["wer"].get("wer") or 0), 4),
        "hyp_tags": hyp[:200],
        "hyp_control": ctrl_hyp[:200],
        "perceptual_check": "requise — la sonde mesure la fuite des tags et un delta de duree, pas la presence audible du non-verbal",
    }
    # 4. texte long : prompt de clonage encode une fois puis reutilise.
    if not args.skip_long:
        prompt = model.create_voice_clone_prompt(ref_audio=str(args.ref_audio), ref_text=ref_text)
        prompt_path = out_dir / "voice_clone_prompt.pt"
        prompt.save(str(prompt_path))
        summary["voice_prompt_path"] = str(prompt_path)
        run("long", long_text, voice_clone_prompt=prompt)

    (out_dir / "probe_summary.json").write_text(
        json.dumps(summary, indent=2, ensure_ascii=False), encoding="utf-8")
    print(f"[probe] resume: {out_dir / 'probe_summary.json'}")
    return 0


if __name__ == "__main__":
    sys.exit(main())