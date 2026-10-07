"""bake_report.py -- genere un rapport markdown triee par WER du banc TTS.

Sortie : stdout OU --out <path>. Le rapport n'est PAS commite : il est poste sur
l'issue de coordination (cadrage coordinateur #19695 07/10 09:08Z, point 3 :
"Le rapport markdown se genere a la demande et se poste sur l'issue. Il n'est
pas commite : les rapports ne vivent pas dans l'arbre").

Usage :
    # Vers stdout :
    python bake_report.py --bank runs/bake_bank.json

    # Vers un fichier :
    python bake_report.py --bank runs/bake_bank.json --out runs/bake-report.md

    # Avec tri par RTF au lieu de WER :
    python bake_report.py --bank runs/bake_bank.json --sort rtf

    # Filtre par moteur :
    python bake_report.py --bank runs/bake_bank.json --motor chatterbox_mtl_v3
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

THIS_DIR = Path(__file__).resolve().parent
SCHEMA_VERSION = "v1"


def load_bank(path: Path) -> list[dict]:
    if not path.exists():
        return []
    data = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(data, list):
        raise ValueError(f"bank root doit etre une liste JSON, got {type(data).__name__}")
    return data


def fmt_wer(v: Any) -> str:
    if v is None:
        return "—"
    return f"{v * 100:.2f} %"


def fmt_num(v: Any, unit: str = "") -> str:
    if v is None:
        return "—"
    return f"{v}{unit}"


def render(bank: list[dict], sort_key: str = "wer", motor_filter: str | None = None) -> str:
    rows = list(bank)
    if motor_filter:
        rows = [r for r in rows if r.get("motor") == motor_filter]

    # Tri : nulls en fin
    def sortkey(r: dict) -> tuple[int, float]:
        v = r.get(sort_key)
        if v is None:
            return (1, 0.0)
        return (0, float(v))

    rows.sort(key=sortkey)

    if not rows:
        return f"# Banc TTS -- vide\n\nAucun run dans le banc (filtre motor={motor_filter!r}).\n"

    lines: list[str] = []
    n = len(rows)
    n_with_wer = sum(1 for r in rows if r.get("wer") is not None)
    n_moteurs = len({r.get("motor") for r in rows if r.get("motor")})
    n_extracts = len({(r.get("motor"), r.get("extract")) for r in rows if r.get("motor") and r.get("extract")})

    lines.append("# Banc de référence TTS -- rapport")
    lines.append("")
    lines.append(f"- **{n}** run(s) cumulé(s), **{n_with_wer}** avec WER mesuré")
    lines.append(f"- **{n_moteurs}** moteur(s), **{n_extracts}** couple(s) (moteur, extract)")
    lines.append(f"- Tri : `{sort_key}` (null en fin)")
    if motor_filter:
        lines.append(f"- Filtre moteur : `{motor_filter}`")
    lines.append("")

    # Tableau principal
    header_cols = [
        "Moteur", "Extract", "Seed", "Date",
        "WER", "RTF", "VRAM (MB)", "Durée (s)",
        "Voice stable", "Hallu/100syl", "Omissions", "ASR",
    ]
    lines.append("| " + " | ".join(header_cols) + " |")
    lines.append("| " + " | ".join(["---"] * len(header_cols)) + " |")

    for r in rows:
        motor = r.get("motor", "—")
        extract = r.get("extract", "—")
        seed = r.get("seed", "—")
        ts = (r.get("ts") or "—")[:10]
        wer = fmt_wer(r.get("wer"))
        rtf = fmt_num(r.get("rtf"))
        vram = fmt_num(r.get("vram_mb"))
        dur = fmt_num(r.get("duration_s"), "s")
        voice = r.get("voice_stable")
        voice_s = "✓" if voice is True else ("✗" if voice is False else "—")
        hallu = fmt_num(r.get("hallu_per_100_syl"))
        omis = fmt_num(r.get("omitted_segments"))
        asr_models = r.get("asr_models") or []
        asr_s = ", ".join(asr_models) if asr_models else "—"
        lines.append(
            f"| {motor} | {extract} | {seed} | {ts} "
            f"| {wer} | {rtf} | {vram} | {dur} "
            f"| {voice_s} | {hallu} | {omis} | {asr_s} |"
        )

    lines.append("")
    # Notes
    notes_presentes = [r for r in rows if r.get("notes")]
    if notes_presentes:
        lines.append("## Notes par run")
        lines.append("")
        for r in notes_presentes:
            label = f"{r.get('motor', '?')}/{r.get('extract', '?')}/seed={r.get('seed', '?')}"
            lines.append(f"- **{label}** : {r['notes']}")
        lines.append("")

    return "\n".join(lines)


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    p.add_argument("--bank", type=Path, required=True, help="Chemin du fichier banc JSON")
    p.add_argument("--out", type=Path, default=None, help="Fichier de sortie (default: stdout)")
    p.add_argument("--sort", default="wer", choices=["wer", "rtf", "duration_s", "ts"],
                   help="Cle de tri (default: wer)")
    p.add_argument("--motor", default=None, help="Filtre moteur (snake_case)")
    args = p.parse_args()

    bank = load_bank(args.bank)
    md = render(bank, sort_key=args.sort, motor_filter=args.motor)
    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(md, encoding="utf-8")
        print(f"Rapport ecrit: {args.out}", file=sys.stderr)
    else:
        sys.stdout.write(md)
    return 0


if __name__ == "__main__":
    sys.exit(main())