"""#11346 — Voice-casting remediation for the 3 REJECT-MONOTONE review segments.

Diagnosis (gate_results_2026-07-17.json, #1028 DoR):
  - comtesse  seg107 : 4 syllables / 1.3 s — segment far too short for any
    melodic movement; the character's longest line (seg214) was never tried.
  - cornudet  seg118 : longest line, but read flat by the "mocking" cloned
    voice with neutral tags ([emphasis][firm][pause]).
  - loiseau   seg230 : quoted-worry text with [chuckling] — mismatched and flat.

Remediation levers (all S2-Pro native, no workaround):
  L1 longer/richer text  — a question (rising intonation) for comtesse, an
     emphatic repetition for loiseau; more syllables = more melodic room.
  L2 free-form bracket tags placed mid-text where tone changes (F1 #1600:
     S2-Pro accepts free-form natural language; cap ~4 prefix tags #p5).
  L3 seed/temperature variation — the v4 review set was generated at seed 42
     only; re-sampling is the cheapest expressivity lever.

Candidates are written to a scratch dir; gate them with
  python scripts/tts_verification/verify_prosody.py --audio-dir <dir> --json
and surface only PASS/WARN winners (DoR condition 3).
"""
from __future__ import annotations

import sys
import json
import time
from pathlib import Path

V4 = Path(__file__).parent
sys.path.insert(0, str(V4.parent))  # 04-Applications/ so `v4.` resolves
from v4.fishaudio_client import fishaudio_tts  # noqa: E402

OUT = Path(sys.argv[1]) if len(sys.argv) > 1 else Path("remediation_candidates")
OUT.mkdir(exist_ok=True, parents=True)

# speaker -> cloned reference (manifest 2026-07, outputs/fishaudio_references)
REF = {
    "comtesse": "v4_comtesse_cold",
    "cornudet": "v4_cornudet_mocking",
    "loiseau": "v4_loiseau_vulgar",
}

# (candidate_id, reference, fishaudio_text, seed, temperature)
CANDIDATES = [
    # comtesse — L1: her longest line (109 ch), a genuine question => rising
    # intonation is the natural melodic engine. v1 = original P4 annotation
    # (never generated for review; only the 4-word seg107 was).
    ("comtesse_214_v1_orig-tags", "comtesse",
     "[soft voice]--Alors, ma soeur,[short pause] vous pensez que Dieu accepte toutes les voies,[short pause] et pardonne le fait quand le motif est pur?",
     42, 0.7),
    # v2 — L2+L3: emphasis on the final clause + re-sample.
    ("comtesse_214_v2_emphasis-resample", "comtesse",
     "[soft voice]--Alors, ma soeur,[short pause] vous pensez que Dieu accepte toutes les voies,[emphasis] et pardonne le fait quand le motif est pur?",
     7, 0.8),
    # cornudet — L2: the antithesis (barbarie / devoir sacré) read as a
    # contrast arc instead of the flat [firm] declamation.
    ("cornudet_118_v1_contrast-arc", "cornudet",
     "[serious]--La guerre est une barbarie quand on attaque un voisin paisible;[pause] [emphasis]c'est un devoir sacré quand on défend la patrie.",
     7, 0.8),
    # v2 — L1: lean into the mocking register the voice was cloned for.
    ("cornudet_127_v2_mocking-short", "cornudet",
     "[chuckling]--Voyons, vous êtes bête,[short pause] qu'est-ce que ça vous fait?",
     7, 0.8),
    # loiseau — L1+L2: "mais pas du tout" is a built-in emphatic peak.
    ("loiseau_245_v1_emphatic-peak", "loiseau",
     "[excited]--Et, vous comprenez, ce soir, il ne la trouve pas drôle,[emphasis] mais pas du tout.",
     7, 0.8),
    # v2 — the piano line: self-satisfied remark, natural lift on "quadrille".
    ("loiseau_235_v2_excited-lift", "loiseau",
     "[excited]--C'est malheureux de ne pas avoir de piano[short pause] parce qu'on pourrait pincer un quadrille.",
     7, 0.8),
    # L5 — seed/temperature sweep on the best text per stubborn character.
    # Observed 2026-08-17: loiseau_245 at seed 11/temp 0.9 => PASS-TO-EAR
    # (same text at seed 99 stays FLAT — the seed is decisive); cornudet_118
    # REJECT at every seed tried (3/7/11/99, temp 0.7-1.0) — the cloned
    # reference itself flattens declarative text, re-clone is the residual fix.
    ("cornudet_118_s3_t09", "cornudet",
     "--La guerre est une barbarie quand on attaque un voisin paisible; c'est un devoir sacré quand on défend la patrie.",
     3, 0.9),
    ("cornudet_118_s11_t09", "cornudet",
     "--La guerre est une barbarie quand on attaque un voisin paisible; c'est un devoir sacré quand on défend la patrie.",
     11, 0.9),
    ("cornudet_118_s99_t10", "cornudet",
     "--La guerre est une barbarie quand on attaque un voisin paisible; c'est un devoir sacré quand on défend la patrie.",
     99, 1.0),
    ("loiseau_245_s3_t09", "loiseau",
     "--Et, vous comprenez, ce soir, il ne la trouve pas drôle, mais pas du tout.",
     3, 0.9),
    ("loiseau_245_s11_t09", "loiseau",
     "--Et, vous comprenez, ce soir, il ne la trouve pas drôle, mais pas du tout.",
     11, 0.9),
    ("loiseau_245_s99_t10", "loiseau",
     "--Et, vous comprenez, ce soir, il ne la trouve pas drôle, mais pas du tout.",
     99, 1.0),
]

meta = []
for cid, spk, text, seed, temp in CANDIDATES:
    dest = OUT / f"{cid}.mp3"
    if dest.exists() and dest.stat().st_size > 10_000:
        print(f"[skip] {cid} already generated")
    else:
        t0 = time.time()
        audio = fishaudio_tts(text, reference_id=REF[spk], seed=seed, temperature=temp)
        if not audio:
            print(f"[FAIL] {cid}: no audio returned")
            continue
        dest.write_bytes(audio)
        print(f"[ok] {cid}: {len(audio)} bytes in {time.time()-t0:.1f}s")
    meta.append({"candidate": cid, "speaker": spk, "reference_id": REF[spk],
                 "text": text, "seed": seed, "temperature": temp})

(OUT / "candidates_manifest.json").write_text(
    json.dumps(meta, ensure_ascii=False, indent=1), encoding="utf-8")
print(f"\n{len(meta)} candidates in {OUT.resolve()}")
print("Next: python scripts/tts_verification/verify_prosody.py "
      f"--audio-dir {OUT} --json {OUT / 'gate.json'}")
