#!/usr/bin/env python3
"""Mesure le taux de tir schedule observé du workflow pr-gate-stale-sweep.

L'acceptance #12728 mesurait les annulations (cancellation count), pas le
taux de tir (combien de crons produisent un run). Issue #15197 a montré
que le sweep tire à ~28,8 % de sa cadence déclarée (mesure 53 runs / 184
attendus sur 184,3 h, médiane 3,35 h, max 6,24 h).

Ce script mesure le même phénomène pour le run courant : il compte les
runs `event=schedule` sur une fenêtre glissante (par défaut 7 jours) et
calcule le ratio observé/déclaré. Écrit un summary CI `tir_observed_pct`
+ `last_fired_at` + `interval_median_s`.

Le script est **advisory** : il ne rougit jamais le job (un sweep qui
rougit parce que lui-même est sous-cadencé ne fait qu'aggraver la
famine). Sa fonction est de rendre l'angle mort mesurable, pas de le
corriger : la correction est ailleurs (voie (i) doctrine du body de
#15197, voies (ii) cron externe / (iii) événementielle écartée par le
même body).
"""
from __future__ import annotations

import argparse
import json
import os
import statistics
import sys
from datetime import datetime, timedelta, timezone
from urllib.parse import urlparse

# Cadence déclarée du cron `pr-gate-stale-sweep.yml` : `7 * * * *` (chaque
# heure, à la minute 07). Une fenêtre 7 jours = 7 * 24 = 168 tics attendus.
DEFAULT_WINDOW_HOURS = 7 * 24
DECLARED_CADENCE_PER_HOUR = 1.0  # hourly
GITHUB_API = "https://api.github.com"


def _parse_iso(ts: str) -> datetime:
    text = ts[:-1] + "+00:00" if ts.endswith("Z") else ts
    return datetime.fromisoformat(text).astimezone(timezone.utc)


def fetch_runs(repo: str, workflow_file: str, window_hours: int) -> list[dict]:
    """Liste les runs `event=schedule` de `pr-gate-stale-sweep.yml` sur la fenêtre.

    `gh api` pagine automatiquement. Filtre event=schedule + status != in_progress
    pour ne mesurer que des tirs terminés.
    """
    import subprocess
    cutoff = datetime.now(timezone.utc) - timedelta(hours=window_hours)
    cmd = [
        "gh", "api", "--paginate",
        f"{GITHUB_API}/repos/{repo}/actions/workflows/{workflow_file}/runs"
        f"?event=schedule&per_page=100",
        "--jq", ".workflow_runs[] | {created_at, conclusion, status}",
    ]
    out = subprocess.run(cmd, capture_output=True, text=True, check=False, encoding="utf-8", errors="replace")
    if out.returncode != 0:
        print(f"::warning::tir measurement failed: gh api returned {out.returncode}: {out.stderr[:200]}", file=sys.stderr)
        return []
    runs: list[dict] = []
    for line in out.stdout.splitlines():
        line = line.strip()
        if not line:
            continue
        try:
            r = json.loads(line)
        except json.JSONDecodeError:
            continue
        try:
            created = _parse_iso(r["created_at"])
        except (KeyError, ValueError):
            continue
        if created < cutoff:
            continue
        runs.append(r)
    return runs


def compute_metrics(runs: list[dict], window_hours: int) -> dict:
    """Calcule tir_observed_pct + last_fired_at + interval_median_s."""
    declared = int(window_hours * DECLARED_CADENCE_PER_HOUR)
    fired = len(runs)
    tir_pct = (fired / declared * 100.0) if declared > 0 else 0.0
    if not runs:
        return {
            "fired": 0,
            "declared": declared,
            "tir_observed_pct": 0.0,
            "last_fired_at": None,
            "interval_median_s": None,
            "interval_max_s": None,
        }
    fired_times = sorted(_parse_iso(r["created_at"]) for r in runs)
    last_fired_at = fired_times[-1]
    intervals_s = [
        (fired_times[i] - fired_times[i - 1]).total_seconds()
        for i in range(1, len(fired_times))
    ]
    return {
        "fired": fired,
        "declared": declared,
        "tir_observed_pct": tir_pct,
        "last_fired_at": last_fired_at.isoformat().replace("+00:00", "Z"),
        "interval_median_s": statistics.median(intervals_s) if intervals_s else None,
        "interval_max_s": max(intervals_s) if intervals_s else None,
    }


def format_summary(metrics: dict, window_hours: int) -> str:
    lines = [
        "## pr-gate-stale-sweep tir (#15197)",
        "",
        f"Fenêtre mesurée : **{window_hours} h** (cron déclaré : `7 * * * *`)",
        "",
        f"- Runs `schedule` observés : **{metrics['fired']}**",
        f"- Tics déclarés attendus : **{metrics['declared']}**",
        f"- Taux de tir observé : **{metrics['tir_observed_pct']:.1f} %**",
        f"- Dernier tir : `{metrics['last_fired_at'] or 'aucun'}`",
        f"- Intervalle médian : **{metrics['interval_median_s']:.0f} s**" if metrics['interval_median_s'] is not None else "- Intervalle médian : n/a",
        f"- Intervalle max : **{metrics['interval_max_s']:.0f} s**" if metrics['interval_max_s'] is not None else "- Intervalle max : n/a",
        "",
        "**Doctrine** (#15197 voie (i)) : ce sweep est un **filet de rattrapage**, "
        "jamais le chemin de déblocage d'une PR nommée. Quand une PR précise "
        "attend, dispatcher explicitement : `gh workflow run pr-gate-stale-sweep.yml`.",
    ]
    return "\n".join(lines) + "\n"


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--repo", default=os.environ.get("GITHUB_REPOSITORY", "jsboige/CoursIA"))
    p.add_argument("--workflow-file", default="pr-gate-stale-sweep.yml")
    p.add_argument("--window-hours", type=int, default=DEFAULT_WINDOW_HOURS)
    p.add_argument("--write-summary", action="store_true",
                   help="Append metrics to GITHUB_STEP_SUMMARY if set")
    args = p.parse_args()

    runs = fetch_runs(args.repo, args.workflow_file, args.window_hours)
    metrics = compute_metrics(runs, args.window_hours)
    summary = format_summary(metrics, args.window_hours)

    print(f"[pr-sweep-tir] fired={metrics['fired']}/{metrics['declared']} "
          f"({metrics['tir_observed_pct']:.1f}%), "
          f"last_fired_at={metrics['last_fired_at'] or 'none'}, "
          f"interval_median_s={metrics['interval_median_s']}")

    if args.write_summary:
        summary_path = os.environ.get("GITHUB_STEP_SUMMARY")
        if summary_path:
            with open(summary_path, "a", encoding="utf-8") as f:
                f.write(summary)
        else:
            print("::warning::GITHUB_STEP_SUMMARY not set, summary not written", file=sys.stderr)

    # Advisory: exit 0 regardless. The angle this measures is the
    # cadence the job itself depends on, so making the job fail under
    # famine makes the famine worse.
    return 0


if __name__ == "__main__":
    sys.exit(main())
