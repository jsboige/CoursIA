"""c291 — leve le doute sur le clonage : la reference est-elle en cause ?

La sonde `probe_omnivoice.py` clone depuis un rendu TTS de la voix-B du projet
(24 kHz, 5,2 s). Si le clonage echoue, deux causes restent melangees :
(i) la reference est un rendu synthetique ; (ii) le chemin de clonage est
casse en francais.

Cette sonde refait le meme test avec une reference produite par OmniVoice
lui-meme (voix auto sur la phrase 1, meme texte connu), sans autre changement.
Si l'hallucination persiste, la cause (i) est ecartee.

Sortie : `clone_selfref.wav` + `selfref_summary.json` dans --out-dir.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

BAKEOFF_ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(BAKEOFF_ROOT))

import banc_phase_a0 as banc  # noqa: E402
import clients.omnivoice as cl  # noqa: E402


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--extract", default=str(BAKEOFF_ROOT.parent / "bench_extracts" / "extract_A_narration.txt"))
    p.add_argument("--out-dir", required=True)
    p.add_argument("--seed", type=int, default=0)
    args = p.parse_args()

    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    extract_text = Path(args.extract).read_text(encoding="utf-8").strip()
    sentence = re.search(r"(.+?[.!?])(\s|$)", extract_text, flags=re.S).group(1)

    model = cl.load_model(device="cuda", dtype="fp16")
    summary: dict = {"sentence": sentence}

    # Reference auto-generee, meme moteur, meme langue.
    ref_wav = out_dir / "selfref_input.wav"
    r0 = cl.synth(text=sentence, out_wav=str(ref_wav), model=model, language="French", seed=args.seed)
    summary["selfref_synth"] = r0
    print(f"[selfref] reference auto: dur={r0['duration_s']:.2f}s")

    out_wav = out_dir / "clone_selfref.wav"
    res = cl.synth(text=extract_text, out_wav=str(out_wav), model=model, language="French",
                   ref_audio=str(ref_wav), ref_text=sentence, seed=args.seed)
    res["wer"] = banc.measure_wer(str(out_wav), extract_text)
    summary["clone_selfref"] = res
    print(f"[selfref] clone dur={res['duration_s']:.2f}s rtf={res['rtf']:.3f} "
          f"wer={(res['wer'].get('wer') or -1):.4f}")
    print("HYP:", (res["wer"].get("hyp") or "")[:200])

    (out_dir / "selfref_summary.json").write_text(
        json.dumps(summary, indent=2, ensure_ascii=False), encoding="utf-8")
    return 0


if __name__ == "__main__":
    sys.exit(main())