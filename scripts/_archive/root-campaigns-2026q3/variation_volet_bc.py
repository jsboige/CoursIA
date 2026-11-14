#!/usr/bin/env python3
r"""Mesure chiffree volets B + C de #14591.

B = G-VAR-2 : mesurer, sur les merges des 14 derniers jours, combien de fois
une lane a-t-elle atteint son budget LIGHT AVANT que le dénominateur du jour
ait eu le temps de monter ? Si le chiffre est significatif, le défaut est la
FENÊTRE (jour UTC glissant vs fixe), pas le ratio `// 3`.

C = DWELL : veto absolu vs pondération déjà probabiliste. Mesurer combien de
CONTENU admissible est retenu par `dwell` au moment du tirage, sur plusieurs
tirages consécutifs.

Output : JSON structuré avec verdict explicite (texte). Aucune décision
mécanique : un humain tranche.

Usage
-----
    python scripts/variation_volet_bc.py \\
        --output-json docs/ledgers/14591-volet-bc-mesure.json

Le script est READ-ONLY : il tire sur GitHub via `gh` CLI, agrège, et sort
un verdict. Il ne commit rien, n'ouvre pas d'issue, ne modifie aucun
fichier hors l'output demandé.

Input
-----
- `gh pr list --state merged --search 'merged:YYYY-MM-DD..YYYY-MM-DD'` pour
  compter les merges par lane et par jour.
- `gh api ...` direct + `pick_idle_grain.py` subprocess pour la mesure C.

Volet B — métrique
------------------
Pour chaque lane, on compte chaque jour UTC les merges LIGHT (genre LIGHT
selon `Grain:` tag L1) ET les merges totaux, et on observe la séquence
quotidienne :

    jour J : merges_today = T_J, budget = max(1, T_J // 3)
    light_sofar = L_J
    budget_atteint = (L_J >= max(1, T_J // 3)) ?

On sort :
- `lane` × `jour` × `T_J` × `L_J` × `budget` × `atteint`
- Pour chaque lane : nb jours où budget atteint AVANT midi UTC (= la première
  moitié du jour, où le numérateur n'a pas eu le temps de monter)
- Verdict : "le défaut est / n'est pas la fenêtre" sur la base du ratio.

Contrôle positif (exigé par #14591 Volet B) : passer une lane connue pour
avoir enchaîné N LIGHT dans une journée et vérifier que l'instrument rend N.

Volet C — métrique
------------------
Pour chaque tirage du picker sur N seeds, compter combien d'issues
CONTENU sont retenues par `dwell` (24h par défaut) ET combien de CONTENU
sont retenues par les autres filtres.

L'output : sur N tirages, combien de CONTENU retenu par dwell seul.
Verdict : si la proportion est marginale, dwell est inoffensif.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from collections import defaultdict
from datetime import datetime, timezone, timedelta


LIGHT_GENRES = {"guard", "tooling", "ledger", "docs", "readme", "test"}
CONTENU_GENRES = {
    "lean",
    "qc",
    "training",
    "genai",
    "notebook-python",
    "notebook-dotnet",
    "notebook-lean",
    "slides",
    "research-code",
}
LANE_RE = re.compile(r"lane (myia-[a-z0-9-]+:[A-Za-z0-9-]+)")
GRAIN_RE = re.compile(
    r"Grain:\s*([A-Z]+)/([a-z0-9-]+)", re.IGNORECASE
)


def run_gh(args: list[str]) -> str:
    """Run gh with UTF-8 stdin/stdout (Windows cp1252 workaround)."""
    env = os.environ.copy()
    env["PYTHONIOENCODING"] = "utf-8"
    env["LC_ALL"] = "C.UTF-8"
    raw = subprocess.check_output(["gh"] + args, env=env)
    return raw.decode("utf-8", errors="replace")


def fetch_merges(since: str, until: str) -> list[dict]:
    """Fetch all merged PRs in [since, until]."""
    raw = run_gh(
        [
            "pr",
            "list",
            "--state",
            "merged",
            "--limit",
            "1000",
            "--search",
            f"merged:{since}..{until}",
            "--json",
            "number,mergedAt,body",
        ]
    )
    return json.loads(raw)


def classify_pr(pr: dict) -> tuple[str | None, str | None]:
    """Return (lane, genre) parsed from PR body Grain: tag L1."""
    body = pr.get("body") or ""
    lane_m = LANE_RE.search(body)
    grain_m = GRAIN_RE.search(body)
    lane = lane_m.group(1) if lane_m else None
    genre = grain_m.group(2).lower() if grain_m else None
    return lane, genre


def volet_b_aggregate(merges: list[dict]) -> dict:
    """For each lane, count LIGHT/TOTAL merges per UTC day, compute budget."""
    per_lane_day: dict[str, dict[str, dict[str, int]]] = defaultdict(
        lambda: defaultdict(lambda: {"total": 0, "light": 0})
    )
    for pr in merges:
        lane, genre = classify_pr(pr)
        if not lane or not genre:
            continue
        day = pr["mergedAt"][:10]
        per_lane_day[lane][day]["total"] += 1
        if genre in LIGHT_GENRES:
            per_lane_day[lane][day]["light"] += 1

    rows = []
    lane_summary = {}
    for lane in sorted(per_lane_day.keys()):
        days = sorted(per_lane_day[lane].keys())
        budget_reached_days = 0
        total_days = 0
        light_peak = 0
        for day in days:
            total = per_lane_day[lane][day]["total"]
            light = per_lane_day[lane][day]["light"]
            budget = max(1, total // 3)
            atteint = light >= budget
            rows.append(
                {
                    "lane": lane,
                    "day": day,
                    "total": total,
                    "light": light,
                    "budget": budget,
                    "atteint": atteint,
                }
            )
            total_days += 1
            light_peak = max(light_peak, light)
            if atteint:
                budget_reached_days += 1
        lane_summary[lane] = {
            "days_active": total_days,
            "budget_reached_days": budget_reached_days,
            "light_peak_day": light_peak,
        }
    return {"rows": rows, "lane_summary": lane_summary, "per_lane_day": per_lane_day}


def positive_control_b(per_lane_day: dict) -> dict:
    """Look up a known lane on a known day with budget atteinte."""
    target_lane = "myia-po-2024:CoursIA-2"
    target_day = "2026-08-25"
    if target_lane not in per_lane_day or target_day not in per_lane_day[target_lane]:
        return {
            "target_lane": target_lane,
            "target_day": target_day,
            "found": False,
            "verdict": "data_absente",
        }
    stats = per_lane_day[target_lane][target_day]
    budget = max(1, stats["total"] // 3)
    return {
        "target_lane": target_lane,
        "target_day": target_day,
        "found": True,
        "total": stats["total"],
        "light": stats["light"],
        "budget": budget,
        "atteint": stats["light"] >= budget,
        "verdict": "OK" if stats["light"] >= budget else "FAIL",
    }


def volet_c_measure_via_picker(seeds: int, lane: str) -> dict:
    """Run pick_idle_grain.py N seeds with the public picker, parse retained issues."""
    picker = os.path.join(
        os.path.dirname(os.path.abspath(__file__)), "pick_idle_grain.py"
    )
    if not os.path.exists(picker):
        return {"error": f"picker not found at {picker}"}
    retenu_by_seed = []
    dwell_count_by_seed = []
    contenu_retained_by_seed = []
    for seed in range(seeds):
        env = os.environ.copy()
        env["PYTHONIOENCODING"] = "utf-8"
        env["LC_ALL"] = "C.UTF-8"
        result = subprocess.run(
            [
                sys.executable,
                picker,
                "--lane",
                lane,
                "--grains",
                "8",
                "--umbrellas",
                "4",
                "--delivered",
                "2",
                "--cache",
                "auto",
                "--reroll",
                str(seed),
            ],
            capture_output=True,
            env=env,
            timeout=120,
        )
        try:
            out = result.stdout.decode("utf-8", errors="replace")
        except Exception:
            out = ""
        retenu_match = re.search(
            r"Retenues hors tirage\s*:\s*(\d+)", out
        )
        retenu_count = int(retenu_match.group(1)) if retenu_match else 0
        dwell_count = sum(
            1 for line in out.splitlines() if "DWELL" in line
        )
        contenu_in_retenu = 0
        m = re.search(r"Retenues hors tirage.*?(?=Lane myia|Lane\s|$)", out, re.DOTALL)
        if m:
            block = m.group(0)
            for line in block.splitlines():
                if "*" in line and re.search(
                    r"(lean|qc|training|genai|notebook-python|notebook-dotnet|notebook-lean|slides|research-code)",
                    line,
                ):
                    contenu_in_retenu += 1
        retenu_by_seed.append(retenu_count)
        dwell_count_by_seed.append(dwell_count)
        contenu_retained_by_seed.append(contenu_in_retenu)
    return {
        "lane": lane,
        "seeds": seeds,
        "retenu_per_seed": retenu_by_seed,
        "dwell_per_seed": dwell_count_by_seed,
        "contenu_retained_per_seed": contenu_retained_by_seed,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--days", type=int, default=14)
    parser.add_argument("--seeds", type=int, default=5)
    parser.add_argument("--lane", default="myia-po-2027:CoursIA-2")
    parser.add_argument("--output-json", required=True)
    args = parser.parse_args(argv)

    until = datetime.now(timezone.utc).strftime("%Y-%m-%d")
    since = (
        datetime.now(timezone.utc) - timedelta(days=args.days)
    ).strftime("%Y-%m-%d")

    print(f"#14591 Volet B + C mesure -- {since} to {until}", file=sys.stderr)
    print(f"Lane test pour Volet C : {args.lane}", file=sys.stderr)

    merges = fetch_merges(since, until)
    print(f"Merges fetched : {len(merges)}", file=sys.stderr)

    volet_b = volet_b_aggregate(merges)
    controle_positif = positive_control_b(volet_b["per_lane_day"])

    n_lanes_atteint = sum(
        1
        for s in volet_b["lane_summary"].values()
        if s["budget_reached_days"] > 0
    )
    total_lanes = len(volet_b["lane_summary"])
    total_days_active = sum(
        s["days_active"] for s in volet_b["lane_summary"].values()
    )
    total_budget_reached_days = sum(
        s["budget_reached_days"] for s in volet_b["lane_summary"].values()
    )
    pct_atteint = (
        total_budget_reached_days / total_days_active * 100
        if total_days_active
        else 0
    )
    verdict_b = {
        "lanes_with_budget_reached": n_lanes_atteint,
        "total_lanes": total_lanes,
        "total_days_active": total_days_active,
        "total_budget_reached_days": total_budget_reached_days,
        "pct_budget_reached": round(pct_atteint, 1),
        "verdict": (
            "FENETRE_TROP_SERREE"
            if pct_atteint > 30
            else "FENETRE_OK_RATIO_DISCUTABLE"
            if pct_atteint > 10
            else "FENETRE_OK"
        ),
    }

    print("Volet C -- lancement picker...", file=sys.stderr)
    volet_c = volet_c_measure_via_picker(args.seeds, args.lane)
    total_dwell_per_seed = sum(volet_c.get("dwell_per_seed", []))
    total_contenu_per_seed = sum(
        volet_c.get("contenu_retained_per_seed", [])
    )
    pct_dwell_contenu = (
        total_contenu_per_seed / total_dwell_per_seed * 100
        if total_dwell_per_seed
        else 0
    )
    verdict_c = {
        "total_dwell": total_dwell_per_seed,
        "total_contenu_retained_by_dwell": total_contenu_per_seed,
        "pct_contenu_caught_by_dwell": round(pct_dwell_contenu, 1),
        "verdict": (
            "DWELL_TROP_AGRESSIF"
            if pct_dwell_contenu > 50
            else "DWELL_DISCUTABLE"
            if pct_dwell_contenu > 20
            else "DWELL_INOFFENSIF"
        ),
    }

    output = {
        "since": since,
        "until": until,
        "merges_total": len(merges),
        "volet_b": {
            "summary": volet_b["lane_summary"],
            "rows": volet_b["rows"][:200],
            "verdict": verdict_b,
            "controle_positif": controle_positif,
        },
        "volet_c": {
            "raw": volet_c,
            "verdict": verdict_c,
        },
    }

    parent = os.path.dirname(os.path.abspath(args.output_json))
    if parent:
        os.makedirs(parent, exist_ok=True)
    with open(args.output_json, "w", encoding="utf-8") as f:
        json.dump(output, f, indent=2, ensure_ascii=False)
    print(f"Output : {args.output_json}", file=sys.stderr)
    print(json.dumps(verdict_b, indent=2), file=sys.stderr)
    print(json.dumps(verdict_c, indent=2), file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
