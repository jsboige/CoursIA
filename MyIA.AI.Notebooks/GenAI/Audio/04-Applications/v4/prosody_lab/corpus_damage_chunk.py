"""corpus_damage_chunk.py -- classification onset/mid/end des spans d'omission.

Cadrage issue #19739 phase 2 : la phase 1 (PR #19699) a livré l'organe p7
(`MyIA.AI.Notebooks/GenAI/Audio/04-Applications/v4/p7_verify.py`) qui détecte
les spans >=3 mots omis sous >=2 ASR sur 3 (vote 2/3) sur les segments
audio complets de l'audiobook Boule de Suif v4. Sur la passe 3, 24 spans
d'omission sur 145 mots sont mesurés -- dont plusieurs debutent au mot 0
du segment source, signature d'un onset-drop CosyVoice3 (cf. corps de PR
#19699, "Le residuel : onset-drop intrinseque au moteur").

Ce module **classifie** chaque span d'omission par **position dans le
segment source normalise** :
- `onset_drop` : span debute au mot 0 du segment -- la premiere proposition
  est omise.
- `end_drop` : span finit au dernier mot du segment -- la queue du segment
  est tombee.
- `mid_omission` : span entre les deux.
- `spread` : span couvre >= 80 % du segment -- la totalite du segment est
  tombee (catastrophe).
- `none` : ne classifie pas (seg trop court, span trop court).

L'instrument est CPU pur, deterministe, sans appel ASR. Il prend en entree
l'artefact `omission_report.json` produit par p7_verify.py et un mapping
des longueurs normalisees par segment (depuis `annotated_v4.json` ou un
mapping equivalent). La sortie est un rapport JSON + resume stdout,
structure compatible avec les outils du banc de reference (#19695).

Note : ce module **detecte** l'onset-drop dans les artefacts deja mesures.
Le **re-roll cible par chunk** (graine espacee, garde d'attaque) est une
extension GPU ulterieure (lane po-2023 ou po-2024 RTX 3090) ; ce module
fournit le diagnostic sans le remede.

Usage :
    python corpus_damage_chunk.py \\
        --omission-report outputs/omission_report.json \\
        --annotated outputs/annotated_v4.json \\
        --out outputs/onset_chunk_report.json

Sortie :
    {
        "method": "...",
        "n_records": int,
        "n_classified": int,
        "counts": {"onset_drop": int, "mid_omission": int, ...},
        "onset_segments": [{"seg_index": int, "speaker": str,
                             "first_span_words": str, "n_spans": int}],
        ...
    }
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

# Categories de position. Constantes exportees pour les tests.
ONSET_DROP = "onset_drop"
MID_OMISSION = "mid_omission"
END_DROP = "end_drop"
SPREAD = "spread"
NONE = "none"

# Seuil : un span qui couvre >= 80 % du segment est "spread" (catastrophe).
SPREAD_RATIO = 0.8

# Taille minimale d'un segment pour etre classifie. Les segments plus
# courts que 3 mots ne peuvent pas produire de span >=3 mots (invariant
# p7) ; on les ignore.
MIN_SEG_WORDS = 3


def _normalize_for_length(text: str) -> int:
    """Compte de mots normalises (meme convention que p7._normalize_words)."""
    import re
    import unicodedata

    text = unicodedata.normalize("NFC", text).lower()
    text = "".join(c if c.isalnum() else " " for c in text)
    return len(re.sub(r"\s+", " ", text).strip().split())


def classify_span_position(
    span_start: int, span_end: int, seg_word_count: int
) -> str:
    """Classifie un span d'omission par position dans le segment source.

    Conventions :
    - span_start / span_end sont en indices de mots **normalises** (cf.
      p7._normalize_words), inclusifs a gauche, exclusifs a droite.
    - seg_word_count : nombre total de mots normalises du segment source.

    Retourne l'une des categories : onset_drop | mid_omission | end_drop |
    spread | none.
    """
    if seg_word_count < MIN_SEG_WORDS:
        return NONE
    if span_end <= span_start:
        return NONE
    if span_end - span_start < 3:
        return NONE  # span trop court pour etre un signal

    span_len = span_end - span_start
    if span_len / seg_word_count >= SPREAD_RATIO:
        return SPREAD

    if span_start == 0:
        return ONSET_DROP
    if span_end >= seg_word_count:
        return END_DROP
    return MID_OMISSION


def build_seg_word_count_map(
    annotated_path: Path,
) -> dict[str, int]:
    """Construit le mapping seg_index -> nombre de mots normalises.

    Le fichier annotated_v4.json contient une liste de segments avec un
    champ `seg_index` et un champ `text` (cf. schemas.AnnotatedBatch).
    Cette fonction extrait juste le mapping necessaire au calcul de
    position.

    Retourne un dict vide si le fichier est introuvable (cas degenere :
    on ne peut pas classer ; l'appelant doit le signaler).
    """
    if not annotated_path.exists():
        return {}
    try:
        batch = json.loads(annotated_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}

    segments = batch.get("segments", [])
    out: dict[str, int] = {}
    for seg in segments:
        idx = seg.get("seg_index")
        text = seg.get("text", "")
        if idx is None:
            continue
        out[str(idx)] = _normalize_for_length(text)
    return out


def classify_records(
    records: list[dict],
    seg_len_map: dict[str, int],
) -> dict:
    """Classifie chaque record par position du span principal.

    Un record est un dict avec au moins :
    - `seg_index` (int)
    - `spans` (list[{start, end, words}]) -- produit par p7_verify.py
    - `speaker` (str, optionnel, transmis tel quel)

    Le span principal est le **premier** span du record (les spans sont
    tries par ordre d'apparition dans la source). Si le premier span est
    onset_drop, on considere que le segment a un onset-drop. Si tous les
    spans sont end_drop, on rapporte end_drop. Si mixes, on rapporte
    spread (le segment a une perte etendue).

    Retourne un dict compatible avec le banc de reference (cf. schema).
    """
    counts = {ONSET_DROP: 0, MID_OMISSION: 0, END_DROP: 0, SPREAD: 0, NONE: 0}
    onset_segments: list[dict] = []
    end_drop_segments: list[dict] = []
    spread_segments: list[dict] = []
    unclassified: list[dict] = []
    n_classified = 0

    for rec in records:
        idx = rec.get("seg_index")
        spans = rec.get("spans", [])
        if idx is None or not spans:
            unclassified.append({"seg_index": idx, "reason": "no_spans"})
            continue
        seg_len = seg_len_map.get(str(idx))
        if seg_len is None or seg_len < MIN_SEG_WORDS:
            unclassified.append(
                {"seg_index": idx, "reason": "seg_len_unknown_or_too_short"}
            )
            continue

        # Classification par record : on prend le verdict majoritaire parmi
        # les spans, avec la regle "spread > onset_drop > end_drop >
        # mid_omission" pour le cas mixte (un spread domine un onset, etc.).
        per_span: list[str] = []
        for sp in spans:
            cat = classify_span_position(
                int(sp["start"]), int(sp["end"]), seg_len
            )
            per_span.append(cat)
            counts[cat] += 1
            n_classified += 1

        if SPREAD in per_span:
            verdict = SPREAD
        elif ONSET_DROP in per_span:
            verdict = ONSET_DROP
        elif END_DROP in per_span:
            verdict = END_DROP
        elif per_span:
            verdict = per_span[0]
        else:
            verdict = NONE

        rec_summary = {
            "seg_index": idx,
            "speaker": rec.get("speaker", ""),
            "first_span_words": spans[0].get("words", ""),
            "n_spans": len(spans),
            "verdict": verdict,
        }
        if verdict == ONSET_DROP:
            onset_segments.append(rec_summary)
        elif verdict == END_DROP:
            end_drop_segments.append(rec_summary)
        elif verdict == SPREAD:
            spread_segments.append(rec_summary)

    return {
        "method": (
            "classification onset/mid/end/spread par position de span "
            "d'omission (>=3 mots, vote 2/3 ASR) dans le segment source "
            "normalise. Convention : ONSET_DROP si span_start == 0, "
            "END_DROP si span_end >= seg_len, MID_OMISSION entre les "
            "deux, SPREAD si span couvre >= 80% du segment, NONE "
            "sinon (seg trop court ou span trop court)."
        ),
        "n_records": len(records),
        "n_classified": n_classified,
        "counts": counts,
        "onset_segments": onset_segments,
        "end_drop_segments": end_drop_segments,
        "spread_segments": spread_segments,
        "unclassified": unclassified,
    }


def main() -> int:
    p = argparse.ArgumentParser(
        description=__doc__.splitlines()[0] if __doc__ else ""
    )
    p.add_argument(
        "--omission-report",
        required=True,
        type=Path,
        help="Artefact omission_report.json de p7_verify.py.",
    )
    p.add_argument(
        "--annotated",
        required=True,
        type=Path,
        help="Artefact annotated_v4.json (source des longueurs).",
    )
    p.add_argument(
        "--out",
        type=Path,
        default=None,
        help="Sortie JSON (defaut : stdout).",
    )
    args = p.parse_args()

    if not args.omission_report.exists():
        print(
            f"ERREUR : omission-report introuvable : {args.omission_report}",
            file=sys.stderr,
        )
        return 2

    payload = json.loads(args.omission_report.read_text(encoding="utf-8"))
    records = payload.get("records", [])

    seg_len_map = build_seg_word_count_map(args.annotated)
    if not seg_len_map:
        print(
            f"AVERTISSEMENT : annotated {args.annotated} absent ou vide ; "
            f"classification sans longueur de segment -- tous les spans "
            f"seront 'none'.",
            file=sys.stderr,
        )

    report = classify_records(records, seg_len_map)

    # Resume stdout compact
    print(f"=== ONSET CHUNK CLASSIFICATION (#19739 phase 2) ===")
    print(f"  Records : {report['n_records']}")
    print(f"  Spans classifiables : {report['n_classified']}")
    print(f"  Counts : {json.dumps(report['counts'], ensure_ascii=False)}")
    print(f"  Onset-drop segments : {len(report['onset_segments'])}")
    print(f"  End-drop segments   : {len(report['end_drop_segments'])}")
    print(f"  Spread segments     : {len(report['spread_segments'])}")
    if report["onset_segments"]:
        print(f"  -- onset-drops --")
        for rec in report["onset_segments"][:5]:
            print(
                f"    seg {rec['seg_index']:3d} "
                f"({rec.get('speaker', '?'):>5s}): "
                f"{rec['first_span_words'][:70]}"
            )

    out_text = json.dumps(report, indent=2, ensure_ascii=False)
    if args.out is not None:
        args.out.write_text(out_text, encoding="utf-8")
        print(f"\n  Ecrit : {args.out}")
    else:
        print()
        print(out_text)
    return 0


if __name__ == "__main__":
    sys.exit(main())