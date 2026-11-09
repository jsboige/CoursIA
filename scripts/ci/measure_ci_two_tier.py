#!/usr/bin/env python3
"""Mesure P0 du plan « CI a deux etages » (issue #25510).

Produit, en un seul passage :

1. le **census** des workflows du depot : declencheurs lus dans le bloc `on:`,
   nombre de jobs, signaux declares (Lean, papermill, reseau) ;
2. la **mesure de cout** des runs `pull_request` : duree (`updated_at -
   run_started_at`), mediane, p90, max et repartition des conclusions, par
   workflow ;
3. la liste des **constituants du PR gate** : les jobs declenches sur
   `pull_request`, classes bloquant ou advisory avec la fonction du gate
   lui-meme (`pr_gate.is_advisory`) -- jamais avec une liste recopiee a la main.

Le gate exige un seul nom de check (``PR gate``) mais agrege tout check-run non
advisory de la tete : l'ensemble des jobs bloquants est donc exactement ce qu'un
deuxieme etage devrait deplacer vers le lot quotidien.

Usage :

    python scripts/ci/measure_ci_two_tier.py --out .tmp/ci_two_tier_inventory.json

Limite connue et **annoncee** : l'API Actions plafonne la pagination a 1000
resultats filtres -- la page suivante revient vide et `total_count` affiche 0.
La fenetre mesuree est donc la plus recente, et l'intervalle reellement couvert
est ecrit dans le JSON (`window_covered`) -- il n'est jamais suppose : le champ
`total_count` de l'API n'est pas fiable et n'est pas utilise.

Lecture seule : aucune ecriture dans le depot, aucun secret (le jeton est lu
par ``gh auth token`` au moment de l'appel).
"""
from __future__ import annotations

import argparse
import json
import re
import statistics
import subprocess
import sys
import time
import urllib.error
import urllib.request
from datetime import datetime, timedelta, timezone
from pathlib import Path

REPO = "jsboige/CoursIA"
REPO_ROOT = Path(__file__).resolve().parents[2]
WF_DIR = REPO_ROOT / ".github" / "workflows"

sys.path.insert(0, str(REPO_ROOT / "scripts"))
import pr_gate as gate  # noqa: E402

# Signaux qui rendent un workflow « lourd » sans passer par la mesure : les
# phases P1/P2/P3 du plan s'appuient dessus.
HEAVY_SIGNALS = {
    "lean": re.compile(r"\blake\s+build\b|\belan\b|lean-axiom|proof-integrity|lean4", re.I),
    "papermill": re.compile(r"papermill|nbconvert", re.I),
    "reseau": re.compile(
        r"pip\s+install|npm\s+(ci|install)|dotnet\s+restore|nuget\s+restore|"
        r"curl\s+-|wget\s+|docker\s+(pull|build)|playwright\s+install|download",
        re.I,
    ),
}

# Plafond de pagination de l'API Actions **avec un filtre** : au-dela de 1000
# resultats filtres, la page suivante revient vide et `total_count` affiche 0.
# Mesure du 2026-11-09 : page 11 vide, 1000 runs collectes sur 10 pages.
MAX_RUNS = 1000
PAGE = 100


def token() -> str:
    out = subprocess.run(
        ["gh", "auth", "token", "--user", "jsboige"],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
        check=True,
    )
    return out.stdout.strip()


TOK = token()


def api(path: str, tries: int = 4):
    req = urllib.request.Request(
        f"https://api.github.com{path}",
        headers={
            "Authorization": f"Bearer {TOK}",
            "Accept": "application/vnd.github+json",
            "X-GitHub-Api-Version": "2022-11-28",
            # GitHub rejette les requetes sans User-Agent (403 "forbidden by
            # administrative rules") : sans cet en-tete, chaque appel echoue
            # puis part en backoff, et la mesure prend une demi-heure au lieu
            # de deux minutes.
            "User-Agent": "coursia-ci-two-tier-measure",
        },
    )
    delay = 3
    for attempt in range(tries):
        try:
            with urllib.request.urlopen(req, timeout=90) as resp:
                return json.loads(resp.read().decode("utf-8"))
        except urllib.error.HTTPError as exc:
            if exc.code in (403, 429) and attempt < tries - 1:
                time.sleep(delay)
                delay *= 2
                continue
            raise
    raise RuntimeError(path)


def top_level_on(text: str) -> list[str]:
    """Declencheurs de premier niveau du bloc ``on:``.

    La lecture est structurelle, pas textuelle : plusieurs workflows mentionnent
    ``pull_request`` dans un commentaire, pour dire qu'ils en sont sortis.
    """
    keys: list[str] = []
    in_on = False
    base_indent: int | None = None
    for raw in text.splitlines():
        line = raw.rstrip()
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        if not in_on:
            if re.match(r"^on:\s*$", line) or re.match(r"^['\"]?on['\"]?:\s*$", line):
                in_on = True
            continue
        indent = len(line) - len(line.lstrip())
        if base_indent is None:
            # le niveau des enfants de `on:` est releve sur le premier enfant :
            # l'indentation n'est pas toujours de deux espaces dans ce depot.
            base_indent = indent
        elif indent < base_indent:
            break
        if indent != base_indent:
            continue
        m = re.match(r"^\s+['\"]?([A-Za-z0-9_-]+)['\"]?:", line)
        if m:
            keys.append(m.group(1))
    return keys


def workflow_name(text: str) -> str:
    m = re.search(r"^name:\s*(.+)$", text, re.M)
    return m.group(1).strip().strip("'\"") if m else ""


def jobs_of(text: str) -> list[tuple[str, str]]:
    """(id de job, nom affiche) pour chaque job du workflow."""
    m = re.search(r"^jobs:\s*$", text, re.M)
    if not m:
        return []
    out: list[tuple[str, str]] = []
    cur_id = None
    for line in text[m.end():].splitlines():
        jm = re.match(r"^  ([A-Za-z0-9_-]+):\s*$", line)
        if jm:
            cur_id = jm.group(1)
            out.append((cur_id, cur_id))
            continue
        nm = re.match(r"^    name:\s*(.+)$", line)
        if nm and cur_id:
            out[-1] = (cur_id, nm.group(1).strip().strip("'\""))
    return out


def code_lines(text: str) -> str:
    """Le texte du workflow prive de ses lignes de commentaire.

    Un signal declare (Lean, reseau) qui n'apparait que dans un commentaire ne
    dit rien du cout du workflow : le matcher sur le texte entier produit des
    faux positifs, dont un workflow de garde qui evoque Lean dans une note.
    """
    kept = [
        ln for ln in text.splitlines()
        if not ln.lstrip().startswith("#")
    ]
    return "\n".join(kept)


def parse_ts(s: str) -> datetime:
    return datetime.strptime(s, "%Y-%m-%dT%H:%M:%SZ").replace(tzinfo=timezone.utc)


def pct(values: list[float], p: float) -> float:
    if not values:
        return 0.0
    vs = sorted(values)
    if len(vs) == 1:
        return vs[0]
    k = (len(vs) - 1) * p
    lo = int(k)
    hi = min(lo + 1, len(vs) - 1)
    return vs[lo] + (vs[hi] - vs[lo]) * (k - lo)


def sweep_runs(created_since: str, max_pages: int) -> tuple[list[dict], dict]:
    """Balaye les runs `pull_request` de la fenetre, page par page."""
    runs: list[dict] = []
    pages = 0
    truncated = False
    for page in range(1, max_pages + 1):
        data = api(
            f"/repos/{REPO}/actions/runs?per_page={PAGE}&event=pull_request"
            f"&page={page}&created%3E={created_since}"
        )
        batch = data.get("workflow_runs", [])
        pages = page
        runs.extend(batch)
        if len(batch) < PAGE:
            break
        if len(runs) >= MAX_RUNS:
            truncated = True
            break
    created = [r["created_at"] for r in runs if r.get("created_at")]
    covered = {
        "runs": len(runs),
        "pages": pages,
        "truncated_at_cap": truncated,
        "from": min(created) if created else None,
        "to": max(created) if created else None,
    }
    return runs, covered


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default="")
    ap.add_argument("--hours", type=int, default=24,
                    help="fenetre demandee en heures (la fenetre reellement "
                         "couverte est plus courte : l'API plafonne a 1000 runs "
                         "filtres)")
    ap.add_argument("--max-pages", type=int, default=MAX_RUNS // PAGE)
    args = ap.parse_args()

    since = datetime.now(timezone.utc) - timedelta(hours=args.hours)
    created_since = since.strftime("%Y-%m-%dT%H:%M:%SZ")

    print(f"[1/3] balayage des runs pull_request depuis {created_since}",
          file=sys.stderr, flush=True)
    runs, covered = sweep_runs(created_since, args.max_pages)
    print(f"      {covered['runs']} runs, fenetre couverte "
          f"{covered['from']} -> {covered['to']}", file=sys.stderr, flush=True)

    print("[2/3] census local des workflows", file=sys.stderr, flush=True)
    rows: list[dict] = []
    for path in sorted(WF_DIR.glob("*.yml")):
        rel = f".github/workflows/{path.name}"
        text = path.read_text(encoding="utf-8", errors="replace")
        triggers = top_level_on(text)
        wname = workflow_name(text)
        entry: dict = {
            "path": rel,
            "workflow_name": wname,
            "triggers": triggers,
            "pr": "pull_request" in triggers,
            "jobs": len(jobs_of(text)),
            "signals": sorted(
                n for n, rx in HEAVY_SIGNALS.items()
                if rx.search(code_lines(text))
            ),
        }
        if entry["pr"]:
            entry["jobs_detail"] = [
                {"job_id": jid, "job_name": jname,
                 "advisory": gate.is_advisory(jname, wname)}
                for jid, jname in jobs_of(text)
            ]
        rows.append(entry)

    by_path = {r["path"]: r for r in rows}
    agg: dict[str, dict] = {}
    for run in runs:
        rel = run.get("path") or ""
        entry = agg.setdefault(rel, {"runs": 0, "durations": [], "conclusions": {}})
        entry["runs"] += 1
        concl = run.get("conclusion") or run.get("status") or "?"
        entry["conclusions"][concl] = entry["conclusions"].get(concl, 0) + 1
        if run.get("status") == "completed" and run.get("run_started_at"):
            try:
                d = (parse_ts(run["updated_at"])
                     - parse_ts(run["run_started_at"])).total_seconds() / 60
            except Exception:  # noqa: BLE001
                continue
            if d >= 0:
                entry["durations"].append(d)

    for rel, data in agg.items():
        entry = by_path.get(rel)
        if entry is None:
            continue
        durs = data["durations"]
        entry["runs_pr"] = data["runs"]
        entry["durations"] = len(durs)
        entry["conclusions"] = data["conclusions"]
        entry["median"] = round(statistics.median(durs), 1) if durs else None
        entry["p90"] = round(pct(durs, 0.9), 1) if durs else None
        entry["max"] = round(max(durs), 1) if durs else None
        entry["heavy_measured"] = bool(
            durs and (entry["median"] > 5 or entry["p90"] > 15))

    print("[3/3] ecriture", file=sys.stderr, flush=True)
    jobs_total = sum(len(r.get("jobs_detail", [])) for r in rows if r["pr"])
    jobs_blocking = sum(
        1 for r in rows if r["pr"] for j in r.get("jobs_detail", []) if not j["advisory"]
    )
    payload = {
        "repo": REPO,
        "measured_at": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "window_requested_hours": args.hours,
        "window_created_since": created_since,
        "window_covered": covered,
        "workflows_total": len(rows),
        "workflows_pr": sum(1 for r in rows if r["pr"]),
        "constituents": {
            "jobs_total": jobs_total,
            "jobs_blocking": jobs_blocking,
            "jobs_advisory": jobs_total - jobs_blocking,
        },
        "rows": rows,
    }
    text = json.dumps(payload, ensure_ascii=False, indent=1)
    if args.out:
        Path(args.out).write_text(text, encoding="utf-8")
        print(f"ecrit : {args.out} -- {len(rows)} workflows, "
              f"{payload['workflows_pr']} sur pull_request, "
              f"{jobs_blocking} jobs bloquants, {covered['runs']} runs mesures")
    else:
        print(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
