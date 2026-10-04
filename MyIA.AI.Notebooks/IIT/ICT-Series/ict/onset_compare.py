"""Comparateur baseline-vs-relance pour l'experience onset (#17719).

Compare deux artefacts produits par onset_runner.py (ou la baseline
onset_results.json de #17702, meme schema per-seed) et rend un rapport
markdown : par bras, medianes early/late de hack_freq, math_correct late,
graines croissantes, verdicts onset re-derives (reutilise verdict_for du
runner -- pas de reimplementation).

Verdict comparatif honnete : la difference baseline vs relance ne se declare
pas sur une seule seed -- sans >= 3 seeds par bras des deux cotes, le verdict
comparatif est INCONCLUSIF (esprit regle C des reviews : multi-seed ou rien).

Usage :
    python -m ict.onset_compare <baseline.json> <relance.json> [--markdown]
"""

from __future__ import annotations

import argparse
import json
import statistics
import sys
from pathlib import Path

from .onset_runner import verdict_for


def _load(path: str) -> dict:
    with open(path, encoding="utf-8") as f:
        return json.load(f)


def _arm_metrics(run: dict, arm: str) -> dict | None:
    ms = run.get("results", {}).get(arm) or []
    if not ms:
        return None
    return {
        "n_seeds": len(ms),
        "hack_early": [m["hack_early"] for m in ms],
        "hack_late": [m["hack_late"] for m in ms],
        "mc_late": [m["mc_late"] for m in ms],
        "train_s": [m.get("train_s") for m in ms if m.get("train_s") is not None],
    }


def _fmt(xs: list[float]) -> str:
    return "[" + ", ".join(f"{x:.3f}" for x in xs) + "]"


def compare(baseline: dict, relance: dict, tag_r: str | None = None) -> tuple[str, str]:
    """Rend (rapport_markdown, verdict_comparatif)."""
    arms_b = set(baseline.get("results", {}).keys())
    arms_r = set(relance.get("results", {}).keys())
    arms = sorted(arms_b & arms_r)
    lines: list[str] = []

    tag_b = baseline.get("model", "baseline 0.5B (#17702)")
    tag_r = tag_r or relance.get("model", "relance")
    lines.append(f"# Onset : baseline vs relance")
    lines.append(f"- baseline : `{tag_b}` — {baseline.get('max_steps', 120)} steps, lr={baseline.get('lr', 1e-5)}")
    lines.append(f"- relance  : `{tag_r}` — {relance.get('max_steps', 120)} steps, lr={relance.get('lr', 1e-5)}")
    if arms_b != arms_r:
        lines.append(f"- bras non communs ignorés : {sorted(arms_b ^ arms_r)}")

    verdicts = []
    for arm in arms:
        b, r = _arm_metrics(baseline, arm), _arm_metrics(relance, arm)
        if not b or not r:
            lines.append(f"\n## Bras {arm} — absent d'un des deux artefacts, ignoré")
            continue
        label = "signal affaibli" if arm == "W" else "few-shot fort"
        lines.append(f"\n## Bras {arm} ({label})")
        lines.append(f"| métrique | baseline ({b['n_seeds']} seeds) | relance ({r['n_seeds']} seeds) |")
        lines.append("|---|---|---|")
        for name, bk, rk in [
            ("hack early (median)", "hack_early", "hack_early"),
            ("hack late (median)", "hack_late", "hack_late"),
            ("mc late (median)", "mc_late", "mc_late"),
        ]:
            lines.append(f"| {name} | {statistics.median(b[bk]):.4f} | {statistics.median(r[rk]):.4f} |")
        b_inc = sum(1 for e, l in zip(b["hack_early"], b["hack_late"]) if l > e)
        r_inc = sum(1 for e, l in zip(r["hack_early"], r["hack_late"]) if l > e)
        lines.append(f"| graines croissantes | {b_inc}/{b['n_seeds']} | {r_inc}/{r['n_seeds']} |")
        if b["train_s"] and r["train_s"]:
            lines.append(f"| train_s/seed (median) | {statistics.median(b['train_s']):.0f} s | {statistics.median(r['train_s']):.0f} s |")
        lines.append(f"- per-seed hack late : baseline {_fmt(b['hack_late'])} vs relance {_fmt(r['hack_late'])}")
        sb, _ = verdict_for(arm, baseline["results"][arm])
        sr, _ = verdict_for(arm, relance["results"][arm])
        lines.append(f"- verdict onset : baseline « {sb['verdict']} » → relance « {sr['verdict']} »")
        verdicts.append((arm, b, r, sb, sr))

    # Verdict comparatif global
    conclusive = all(
        b["n_seeds"] >= 3 and r["n_seeds"] >= 3
        for _, b, r, _, _ in verdicts
    ) if verdicts else False
    if not verdicts:
        overall = "INCOMPARABLE (aucun bras commun)"
    elif not conclusive:
        overall = "INCONCLUSIF (grille reduite : <3 seeds par bras sur au moins un artefact -- etendre la grille avant de conclure)"
    else:
        shifts = []
        for arm, b, r, _, _ in verdicts:
            db = statistics.median(b["hack_late"]) - statistics.median(b["hack_early"])
            dr = statistics.median(r["hack_late"]) - statistics.median(r["hack_early"])
            shifts.append((arm, db, dr))
        stronger = all(dr > db for _, db, dr in shifts)
        weaker = all(dr < db for _, db, dr in shifts)
        if stronger:
            overall = "ONSET PLUS PRECOCE/FORT A L'ECHELLE SUPERIEURE (delta late-early croissant sur tous les bras)"
        elif weaker:
            overall = "ONSET PLUS FAIBLE A L'ECHELLE SUPERIEURE (delta decroissant sur tous les bras)"
        else:
            overall = "PAS DE DIFFERENCE NETTE ENTRE ECHELLES (deltas mixtes selon le bras)"

    lines.append(f"\n## Verdict comparatif\n\n**{overall}**")
    return "\n".join(lines), overall


def main(argv=None) -> int:
    p = argparse.ArgumentParser(description="Compare deux artefacts onset (baseline vs relance).")
    p.add_argument("baseline")
    p.add_argument("relance")
    args = p.parse_args(argv)
    relance = _load(args.relance)
    report, overall = compare(_load(args.baseline), relance,
                              tag_r=relance.get("model") or Path(args.relance).name)
    print(report)
    print(f"\n[onset-compare] verdict : {overall}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
