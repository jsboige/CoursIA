"""bake_report.py — génère un tableau Markdown du banc de référence TTS.

Usage (depuis la racine du dépôt ou un worktree) :
    python prosody_lab/bake_report.py --bank prosody_lab/bake_bank.jsonl \\
        [--out prosody_lab/bake_report.md]

Tri principal : par extract (A→E), secondaire par WER croissant, tertiaire par
motor. Les colonnes affichées :

| extract | motor | seed | wer | rtf | vram_mb | duration_s | fidelity | consistent | ts |

Le rapport **n'est pas commité** (décision ai-01 sur #19695, 2026-10-07) :
ce script sert à la lecture et à la pré-UAT gate, pas à l'archivage git.
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

PROSODY_LAB_ROOT = Path(__file__).resolve().parent


def _load_bank(bank_path: Path) -> list[dict]:
    if not bank_path.exists():
        return []
    records = []
    with open(bank_path, encoding="utf-8") as f:
        for ln in f:
            ln = ln.strip()
            if not ln:
                continue
            try:
                records.append(json.loads(ln))
            except json.JSONDecodeError as e:
                print(f"Ligne invalide ignorée : {e}", file=sys.stderr)
    return records


def _fidelity(rec: dict) -> str:
    """Synthèse des champs de fidélité (gate #17586)."""
    add = rec.get("fidelity_added_words")
    om = rec.get("fidelity_omitted_segments_3plus")
    if add is None and om is None:
        return "n/a"
    bits = []
    if add is not None:
        bits.append(f"+{add}" if add > 0 else "0")
    if om is not None:
        bits.append(f"-{om}" if om > 0 else "0")
    return "/".join(bits)


def _fmt_num(v, prec: int = 3) -> str:
    if v is None:
        return "—"
    if isinstance(v, float):
        return f"{v:.{prec}f}"
    return str(v)


def _fmt_wer(v) -> str:
    if v is None:
        return "—"
    return f"{v * 100:.1f}%"


def render_markdown(records: list[dict]) -> str:
    records = sorted(records, key=lambda r: (
        r.get("extract", ""),
        r.get("wer") if r.get("wer") is not None else 1.0,
        r.get("motor", ""),
    ))
    out = ["# Bake Bank — tableau de lecture",
           "",
           f"_Lignes : {len(records)}_",
           "",
           "| extract | motor | seed | wer | rtf | vram_mb | duration_s | fidelity | consistent | ts |",
           "|---|---|---|---|---|---|---|---|---|---|"]
    for r in records:
        out.append(
            f"| {r.get('extract','—')} "
            f"| {r.get('motor','—')} "
            f"| {r.get('seed') if r.get('seed') is not None else '—'} "
            f"| {_fmt_wer(r.get('wer'))} "
            f"| {_fmt_num(r.get('rtf'), 3)} "
            f"| {_fmt_num(r.get('vram_mb'), 0) if r.get('vram_mb') is not None else '—'} "
            f"| {_fmt_num(r.get('duration_s'), 1)} "
            f"| {_fidelity(r)} "
            f"| {r.get('voice_consistent') if r.get('voice_consistent') is not None else '—'} "
            f"| {r.get('ts','—')} |"
        )
    return "\n".join(out) + "\n"


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--bank", required=True, help="Banc JSONL.")
    p.add_argument("--out", default=None,
                   help="Sortie (stdout par défaut).")
    args = p.parse_args()

    bank_path = Path(args.bank)
    records = _load_bank(bank_path)
    md = render_markdown(records)

    if args.out:
        out_path = Path(args.out)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        with open(out_path, "w", encoding="utf-8") as f:
            f.write(md)
        print(f"Rapport écrit : {out_path} ({len(records)} lignes)")
    else:
        sys.stdout.write(md)
    return 0


if __name__ == "__main__":
    sys.exit(main())