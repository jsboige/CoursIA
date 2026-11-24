#!/usr/bin/env python3
"""build_bank_entry.py -- entree de banc #19695 derivee du JSON de mesure.

Lit `zonos3-mini-a0c-metrics.json` (rendu + WER + prosodie) et produit
l'entree `bake_bank.json` conforme a `bank_schema_v1.json`, validee par
`jsonschema` quand la bibliotheque est disponible.

Le champ `wer` retient le WER de `large-v3` : c'est le modele de reference
du banc (#14059, WER 0,097) et le votant principal des omissions de la
suite A0C. Les autres ASR mesures restent dans le JSON de mesure.

Usage :
    python build_bank_entry.py --metrics zonos3-mini-a0c-metrics.json \
        --out bank_entry.json [--schema <bank_schema_v1.json>]
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

MOTOR = "zonos3_mini"
EXTRACT = "C"
SEED = 42
WER_MODEL = "large-v3"
# Les ASR retenus dans l'entree de banc sont ceux de l'enumeration du schema
# (v1) : le trio de la suite A0C de reference -- tiny / small / large-v3.
# Le JSON de mesure porte en plus large-v3-turbo (votant de la suite A0C
# de reference), hors enum du schema v1 : il n'entre donc pas dans l'entree.
BANK_ASR_MODELS = ["tiny", "small", "large-v3"]


def build(metrics: dict, prosody: dict, schema_path: Path | None) -> dict:
    wer_block = metrics.get("wer", {}).get("by_model", {})
    omissions = metrics.get("omissions") or {}
    per_model = wer_block.get(WER_MODEL, {})
    wer = per_model.get("wer")
    hyp_words = per_model.get("hyp_words")

    entry = {
        "schema_version": "v1",
        "ts": metrics["ts"],
        "machine": "myia-ai-01",
        "motor": MOTOR,
        "motor_size_b": 0.8,
        "motor_license": "Apache-2.0",
        "extract": EXTRACT,
        "extract_text_sha256_prefix": metrics["text_sha256"][:16],
        "extract_text_chars": metrics["text_chars_normalized"],
        "seed": SEED,
        "speaker": metrics.get("speaker"),
        "language": "fr",
        "wer": wer,
        "wer_model": f"faster-whisper-{WER_MODEL}",
        "rtf": metrics.get("rtf_global"),
        "vram_mb": metrics.get("vram_peak_mb"),
        "duration_s": metrics.get("duration_out_s"),
        "wallclock_total_s": metrics.get("wallclock_total_s"),
        "asr_models": BANK_ASR_MODELS,
        "omitted_segments": omissions.get("n_omitted_3asr"),
        "fidelity_omitted_segments_3plus": omissions.get("n_omitted_3asr"),
        "fidelity_added_words": None,
        "inserted_words": None,
        "voice_stable": None if not prosody else prosody.get("voice_verdict") == "CONSISTENT",
        "voice_consistent": None if not prosody else prosody.get("voice_verdict") == "CONSISTENT",
        "prosody_st_range": prosody.get("melodic_span_st"),
        "prosody_cv": prosody.get("pct_flat_transitions"),
        "prosody_velocity": prosody.get("mean_abs_interval_st"),
        # Le schema v1 fige l'enumeration du verdict de melodie a
        # EXPRESSIVE / INSUFFICIENT / FLAT : le verdict DRONE (ajoute plus tard
        # par l'instrument) n'y entre pas. On ne l'y force pas -- on le
        # laisse dans prosody_gate, prosody_reasons et notes.
        "prosody_verdict": (
            prosody.get("melody_verdict")
            if prosody.get("melody_verdict") in ("EXPRESSIVE", "INSUFFICIENT", "FLAT")
            else None
        ),
        "prosody_gate": prosody.get("gate"),
        "prosody_reasons": prosody.get("reasons"),
        "notes": (
            "Rendu natif ggml CUDA sur GPU 2 ; partition identique au rendu de "
            "reference Zonos v0.1 (8 morceaux) ; rejeu bit-identique a graine 42 ; "
            f"WER {WER_MODEL} = {wer} ({hyp_words} mots reconnus) ; "
            f"prosodie {prosody.get('gate')} ({', '.join(prosody.get('reasons') or [])}) : "
            f"melodie {prosody.get('melody_verdict')}, "
            f"mouvement {prosody.get('mean_abs_interval_st')} st/syll, "
            f"voix {prosody.get('voice_verdict')}."
        )[:2000],
        "source_path": "MyIA.AI.Notebooks/GenAI/Audio/04-Applications/v4/mesures/zonos3/zonos3-mini-a0c-metrics.json",
        "prosody_source_path": "MyIA.AI.Notebooks/GenAI/Audio/04-Applications/v4/mesures/zonos3/prosody-verdict.json",
    }
    return entry


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--metrics", required=True, type=Path)
    ap.add_argument("--prosody", required=True, type=Path,
                    help="rapport complet de verify_prosody (le metrics.json n'en garde que la queue).")
    ap.add_argument("--out", required=True, type=Path)
    ap.add_argument("--schema", type=Path, default=None)
    args = ap.parse_args()

    metrics = json.loads(args.metrics.read_text(encoding="utf-8"))
    prosody = json.loads(args.prosody.read_text(encoding="utf-8"))
    entry = build(metrics, prosody, args.schema)
    args.out.write_text(json.dumps([entry], indent=2, ensure_ascii=False) + "\n",
                        encoding="utf-8")
    print(f"entree de banc ecrite : {args.out}")

    if args.schema and args.schema.exists():
        try:
            import jsonschema
        except ImportError:
            print("jsonschema absent : validation non executee")
            return 0
        schema = json.loads(args.schema.read_text(encoding="utf-8"))
        try:
            jsonschema.validate([entry], schema)
        except jsonschema.ValidationError as exc:
            print(f"ENTREE NON CONFORME : {exc.message} (chemin {list(exc.absolute_path)})")
            return 1
        print("entree conforme a bank_schema_v1.json")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
