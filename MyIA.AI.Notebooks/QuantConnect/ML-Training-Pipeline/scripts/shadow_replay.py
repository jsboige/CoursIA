"""Suivi en ombre (#18923, experience 5c de #18907) : geler des candidates, les rejouer chaque mois.

Principe (body de #18923) :

1. **Geler** : a une date D, une candidate entre dans le registre avec le SHA du commit, ses
   parametres et D. Son code ne change plus.
2. **Rejouer** : chaque mois, chaque candidate gelee est rejouee de D a la date du passage, avec
   son code gele ; une ligne s'ajoute au CSV.
3. **Ne rien retirer** : une candidate qui perd reste suivie. La modifier cree une **nouvelle**
   candidate (nouvel identifiant, nouveau D) ; l'ancienne continue d'etre rejouee.

Ce module rend ces trois regles mecaniques :

- chaque entree du registre porte une empreinte de ses champs ; `validate` refuse une entree
  modifiee apres coup, un identifiant en double, et une ligne de CSV dont la candidate a disparu
  du registre ;
- le CSV ne s'ecrit qu'en ajout, une ligne par candidate et par mois de passage ;
- le rejeu local execute le point d'entree **tel qu'il etait au SHA gele**, dans un worktree
  detache, jamais le code courant.

Point d'entree d'une candidate locale : `chemin/vers/module.py:fonction`, relatif a la racine du
depot. La fonction recoit `start` et `end` (dates ISO) et les parametres du registre, et rend un
dictionnaire :

- `dates` : les seances, au format ISO ;
- `net_returns` : les rendements journaliers nets de frais, un par seance ;
- `turnover` : la rotation journaliere (fraction de l'equite echangee), un par seance ;
- `fees` : le cout de transaction cumule sur la periode, en fraction de l'equite de depart.

Sharpe, CAGR et pire baisse reprennent les definitions de `voltarget_strategy_verdict.py` (#18943) :
Sharpe = moyenne / ecart-type (ddof=1) * sqrt(252) des rendements nets, taux sans risque nul ;
CAGR = produit des (1 + r) a la puissance 1 / annees, moins 1, les annees etant les jours
calendaires entre la premiere et la derniere seance divises par 365,25 ; pire baisse = minimum
de equite / maximum courant - 1.

Rejeu QuantConnect, en deux temps autour du MCP (l'API QC ne s'appelle que par lui) :

1. `plan-qc` extrait du depot les fichiers du projet **au SHA gele**, et ecrit un plan : projet
   QC dedie, empreintes des fichiers, parametres (`start` = D, `end` = date du passage),
   nom du backtest, plage du graphique a lire ;
2. l'operateur pousse ces fichiers par le MCP, lance le backtest avec ces parametres, attend
   `completed: true`, puis enregistre la sortie de `read_backtest` et le graphique `shadow` lu
   par `read_backtest_chart` (#18939) dans le dossier du plan ;
3. `ingest-qc` relit les deux fichiers et rend la meme ligne de CSV que le rejeu local.

Point d'entree d'une candidate QC : `chemin/du/projet:identifiant_du_projet_QC`. Contrat de la
candidate : voir `shadow/qc_example/main.py` et `shadow/README.md`.
"""
from __future__ import annotations

import argparse
import csv
import datetime as dt
import hashlib
import json
import subprocess
import sys
import tempfile
from pathlib import Path
from zoneinfo import ZoneInfo

import numpy as np

REGISTRY_FIELDS = ("id", "kind", "sha", "frozen_on", "entrypoint", "params", "fee_model")
KINDS = ("local", "qc")
CSV_COLUMNS = ["candidate", "sha", "frozen_on", "pass_date", "period_end", "n_days",
               "sharpe_net", "cagr", "max_drawdown", "turnover", "fees", "fee_model"]


# ---------------------------------------------------------------- registre

def fingerprint(entry: dict) -> str:
    """Empreinte des champs geles d'une entree (16 premiers caracteres du sha256)."""
    frozen = {k: entry[k] for k in REGISTRY_FIELDS}
    blob = json.dumps(frozen, sort_keys=True, ensure_ascii=False, separators=(",", ":"))
    return hashlib.sha256(blob.encode("utf-8")).hexdigest()[:16]


def load_registry(path: Path) -> list[dict]:
    if not path.exists():
        return []
    return json.loads(path.read_text(encoding="utf-8"))["candidates"]


def save_registry(path: Path, candidates: list[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    text = json.dumps({"candidates": candidates}, indent=2, ensure_ascii=False) + "\n"
    path.write_text(text, encoding="utf-8", newline="\n")


def freeze(candidates: list[dict], *, id: str, kind: str, sha: str, frozen_on: str,
           entrypoint: str, params: dict, fee_model: str) -> dict:
    """Ajoute une candidate gelee. Refuse un identifiant deja present : une modification
    est une nouvelle candidate, avec un nouvel identifiant."""
    if kind not in KINDS:
        raise ValueError(f"kind must be one of {KINDS}, got {kind!r}")
    if any(c["id"] == id for c in candidates):
        raise ValueError(f"candidate {id!r} already frozen; a change needs a new id")
    dt.date.fromisoformat(frozen_on)
    entry = {"id": id, "kind": kind, "sha": sha, "frozen_on": frozen_on,
             "entrypoint": entrypoint, "params": params, "fee_model": fee_model}
    entry["fingerprint"] = fingerprint(entry)
    candidates.append(entry)
    return entry


def validate(candidates: list[dict], rows: list[dict]) -> list[str]:
    """Rend la liste des violations (vide = registre et CSV conformes)."""
    problems = []
    seen = set()
    for c in candidates:
        if c["id"] in seen:
            problems.append(f"duplicate id {c['id']!r}")
        seen.add(c["id"])
        if c.get("fingerprint") != fingerprint(c):
            problems.append(f"{c['id']}: fields changed after freezing (fingerprint mismatch)")
    by_id = {c["id"]: c for c in candidates}
    months = set()
    for r in rows:
        c = by_id.get(r["candidate"])
        if c is None:
            problems.append(f"{r['candidate']}: replayed but missing from the registry")
            continue
        if (r["sha"], r["frozen_on"]) != (c["sha"], c["frozen_on"]):
            problems.append(f"{r['candidate']}: CSV row {r['pass_date']} does not match the frozen sha/D")
        key = (r["candidate"], r["pass_date"][:7])
        if key in months:
            problems.append(f"{r['candidate']}: two passes in month {key[1]}")
        months.add(key)
    return problems


# ---------------------------------------------------------------- CSV et echeances

def load_rows(path: Path) -> list[dict]:
    if not path.exists():
        return []
    with path.open(encoding="utf-8", newline="") as f:
        return list(csv.DictReader(f))


def append_row(path: Path, row: dict) -> None:
    """Ajoute une ligne ; refuse un second passage de la meme candidate dans le meme mois."""
    month = row["pass_date"][:7]
    if any(r["candidate"] == row["candidate"] and r["pass_date"][:7] == month
           for r in load_rows(path)):
        raise ValueError(f"{row['candidate']} already replayed in {month}")
    new = not path.exists()
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a", encoding="utf-8", newline="") as f:
        w = csv.DictWriter(f, fieldnames=CSV_COLUMNS, lineterminator="\n")
        if new:
            w.writeheader()
        w.writerow({k: row[k] for k in CSV_COLUMNS})


def due(candidates: list[dict], rows: list[dict], pass_date: str) -> list[dict]:
    """Candidates a rejouer au passage `pass_date` : gelees avant cette date, sans ligne ce mois-ci."""
    month = pass_date[:7]
    done = {r["candidate"] for r in rows if r["pass_date"][:7] == month}
    return [c for c in candidates if c["frozen_on"] < pass_date and c["id"] not in done]


# ---------------------------------------------------------------- metriques

def metrics(dates, net_returns, turnover, fees: float) -> dict:
    r = np.asarray(net_returns, dtype=float)
    if r.size < 2:
        raise ValueError("need at least two daily returns")
    years = (dt.date.fromisoformat(dates[-1]) - dt.date.fromisoformat(dates[0])).days / 365.25
    if years <= 0:
        raise ValueError("dates must span at least one calendar day")
    equity = np.cumprod(1.0 + r)
    sd = r.std(ddof=1)
    return {
        "n_days": int(r.size),
        # Ecart-type nul : Sharpe non defini, laisse vide dans le CSV.
        "sharpe_net": round(float(r.mean() / sd * np.sqrt(252)), 4) if sd > 0 else None,
        "cagr": round(float(equity[-1] ** (1.0 / years) - 1.0), 4),
        "max_drawdown": round(float((equity / np.maximum.accumulate(equity) - 1.0).min()), 4),
        "turnover": round(float(np.mean(np.asarray(turnover, dtype=float))), 6),
        "fees": round(float(fees), 6),
    }


# ---------------------------------------------------------------- rejeu local

def _git(repo: Path, *args: str) -> str:
    return subprocess.run(["git", "-C", str(repo), *args], check=True,
                          capture_output=True, text=True).stdout.strip()


# Le point d'entree tourne dans un processus a part, dont le seul chemin d'import est le dossier
# du module gele : un import voisin (`from realized_variance import ...`) ne peut pas tomber sur
# une version deja chargee du code courant.
_DRIVER = """
import importlib.util, json, os, sys
import numpy as np
req = json.load(sys.stdin)
sys.path.insert(0, os.path.dirname(req["module"]))
spec = importlib.util.spec_from_file_location("shadow_entry", req["module"])
module = importlib.util.module_from_spec(spec)
sys.modules["shadow_entry"] = module
spec.loader.exec_module(module)
out = getattr(module, req["function"])(start=req["start"], end=req["end"], **req["params"])
def plain(v):
    if isinstance(v, np.ndarray):
        return v.tolist()
    if isinstance(v, np.generic):
        return v.item()
    if isinstance(v, (list, tuple)):
        return [plain(x) for x in v]
    return v
json.dump({k: plain(v) for k, v in out.items()}, sys.stdout)
"""


def run_frozen(repo: Path, candidate: dict, pass_date: str) -> dict:
    """Execute le point d'entree au SHA gele, de D a `pass_date`, dans un worktree detache."""
    if candidate["kind"] != "local":
        raise ValueError(f"{candidate['id']} is a {candidate['kind']} candidate, not local")
    rel, _, func = candidate["entrypoint"].partition(":")
    with tempfile.TemporaryDirectory(prefix="shadow-") as tmp:
        wt = Path(tmp) / "wt"
        _git(repo, "worktree", "add", "--detach", str(wt), candidate["sha"])
        try:
            module_path = wt / rel
            request = {"module": str(module_path), "function": func,
                       "start": candidate["frozen_on"], "end": pass_date,
                       "params": candidate["params"]}
            proc = subprocess.run([sys.executable, "-c", _DRIVER],
                                  cwd=module_path.parent, input=json.dumps(request),
                                  capture_output=True, text=True)
            if proc.returncode != 0:
                raise RuntimeError(f"{candidate['id']}: frozen entrypoint failed:\n{proc.stderr}")
            out = json.loads(proc.stdout)
        finally:
            _git(repo, "worktree", "remove", "--force", str(wt))
    n = len(out["net_returns"])
    if len(out["dates"]) != n or len(out["turnover"]) != n:
        raise ValueError(f"{candidate['id']}: dates, net_returns and turnover must have the same length")
    return out


def replay_local(repo: Path, candidate: dict, pass_date: str,
                 series_dir: Path | None = None) -> dict:
    """Rejoue une candidate locale et rend sa ligne de CSV (la serie journaliere va hors depot)."""
    out = run_frozen(repo, candidate, pass_date)
    row = {"candidate": candidate["id"], "sha": candidate["sha"],
           "frozen_on": candidate["frozen_on"], "pass_date": pass_date,
           "period_end": out["dates"][-1], "fee_model": candidate["fee_model"],
           **metrics(out["dates"], out["net_returns"], out["turnover"], out["fees"])}
    if series_dir is not None:
        series_dir.mkdir(parents=True, exist_ok=True)
        with (series_dir / f"{candidate['id']}_{pass_date}.csv").open(
                "w", encoding="utf-8", newline="") as f:
            w = csv.writer(f, lineterminator="\n")
            w.writerow(["date", "net_return", "turnover"])
            w.writerows(zip(out["dates"], out["net_returns"], out["turnover"]))
    return row


# ---------------------------------------------------------------- rejeu QuantConnect

QC_CHART = "shadow"
QC_EQUITY_SERIES = [f"e{k}" for k in range(5)]
QC_RESERVED_PARAMS = ("start", "end")
QC_FILE_LIMIT = 64000   # caracteres par fichier de projet QC


def qc_entrypoint(candidate: dict) -> tuple[str, int]:
    """`chemin/du/projet:identifiant` -> (chemin relatif a la racine du depot, identifiant QC)."""
    if candidate["kind"] != "qc":
        raise ValueError(f"{candidate['id']} is a {candidate['kind']} candidate, not qc")
    path, _, project = candidate["entrypoint"].rpartition(":")
    if not path or not project.isdigit():
        raise ValueError(f"{candidate['id']}: qc entrypoint must be 'project/dir:<QC project id>'")
    return path.rstrip("/"), int(project)


def _unix(day: str) -> int:
    return int(dt.datetime.combine(dt.date.fromisoformat(day), dt.time(),
                                   tzinfo=dt.timezone.utc).timestamp())


def plan_qc(repo: Path, candidate: dict, pass_date: str, out_dir: Path) -> dict:
    """Ecrit dans `out_dir/<id>/` les fichiers du projet au SHA gele et le plan du passage."""
    project_dir, project_id = qc_entrypoint(candidate)
    clash = sorted(set(candidate["params"]) & set(QC_RESERVED_PARAMS))
    if clash:
        raise ValueError(f"{candidate['id']}: params {clash} are reserved for the replay dates")
    names = [n for n in _git(repo, "ls-tree", "-r", "--name-only", candidate["sha"], "--",
                             project_dir).splitlines() if n.endswith(".py")]
    if not names:
        raise ValueError(f"{candidate['id']}: no .py file under {project_dir} at {candidate['sha'][:10]}")
    target = out_dir / candidate["id"]
    files = []
    for name in names:
        content = subprocess.run(["git", "-C", str(repo), "show", f"{candidate['sha']}:{name}"],
                                 check=True, capture_output=True).stdout
        rel = name[len(project_dir) + 1:]
        if len(content.decode("utf-8")) > QC_FILE_LIMIT:
            raise ValueError(f"{candidate['id']}: {rel} exceeds the QC file limit ({QC_FILE_LIMIT})")
        dest = target / "files" / rel
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_bytes(content)
        files.append({"name": rel, "sha256": hashlib.sha256(content).hexdigest(),
                      "bytes": len(content)})
    span = (dt.date.fromisoformat(pass_date) - dt.date.fromisoformat(candidate["frozen_on"])).days
    plan = {"candidate": candidate["id"], "sha": candidate["sha"],
            "frozen_on": candidate["frozen_on"], "pass_date": pass_date,
            "qc_project_id": project_id, "project_dir": project_dir, "files": files,
            "parameters": {"start": candidate["frozen_on"], "end": pass_date,
                           **{k: str(v) for k, v in candidate["params"].items()}},
            "backtest_name": f"shadow-{candidate['id']}-{pass_date}",
            "chart": QC_CHART, "chart_start": _unix(candidate["frozen_on"]),
            "chart_end": _unix(pass_date) + 86400, "chart_count": span + 10}
    (target / "plan.json").write_text(json.dumps(plan, indent=2) + "\n", encoding="utf-8")
    return plan


def _chart_points(chart: dict, key: str) -> list[tuple[int, float]]:
    """Points [t, v], [t, o, h, l, c] (cloture) ou {x, y} d'une serie, tries par date."""
    s = (chart.get("series") or {}).get(key)
    if not s or not s.get("values"):
        raise ValueError(f"chart {QC_CHART!r}: missing series {key!r}")
    pts = [(v["x"], v["y"]) if isinstance(v, dict) else (v[0], v[-1]) for v in s["values"]]
    return sorted(pts)


def _session(ts: int) -> str:
    """Date de seance d'un horodatage QC, lue a New York (seances actions US)."""
    return dt.datetime.fromtimestamp(ts, ZoneInfo("America/New_York")).date().isoformat()


def qc_daily_equity(chart: dict) -> tuple[list[str], list[float]]:
    """Fusionne e0..e4 en une cloture par seance, et verifie l'alternance.

    La candidate trace la seance k dans `e{k % 5}` : rangees par date, les series doivent
    donc se succeder e0, e1, e2, e3, e4, e0... Un point perdu ou en trop casse ce cycle.
    """
    points = sorted((t, k, v) for k, key in enumerate(QC_EQUITY_SERIES)
                    for t, v in _chart_points(chart, key))
    for i, (t, k, _) in enumerate(points):
        if k != i % 5:
            raise ValueError(f"equity interleaving broken at point {i} ({_session(t)}): "
                             f"series e{k}, expected e{i % 5}")
    dates = [_session(t) for t, _, _ in points]
    if len(set(dates)) != len(dates):
        raise ValueError("two equity points on the same session")
    return dates, [v for _, _, v in points]


def ingest_qc(candidate: dict, plan: dict, backtest: dict, chart: dict,
              series_dir: Path | None = None) -> dict:
    """Ligne de CSV d'un passage QC, a partir de la sortie de `read_backtest` et du graphique."""
    if (plan["candidate"], plan["sha"], plan["frozen_on"]) != (
            candidate["id"], candidate["sha"], candidate["frozen_on"]):
        raise ValueError(f"plan does not match the frozen candidate {candidate['id']}")
    if backtest.get("error"):
        raise RuntimeError(f"{candidate['id']}: backtest failed: {backtest['error']}")
    if backtest.get("completed") is not True:
        raise ValueError(f"{candidate['id']}: backtest not completed, read it again later")
    if backtest.get("name") != plan["backtest_name"]:
        raise ValueError(f"{candidate['id']}: backtest {backtest.get('name')!r} is not "
                         f"{plan['backtest_name']!r}")
    dates, equity = qc_daily_equity(chart)
    if dates[0] < plan["frozen_on"] or dates[-1] > plan["pass_date"]:
        raise ValueError(f"{candidate['id']}: equity {dates[0]}..{dates[-1]} outside "
                         f"{plan['frozen_on']}..{plan['pass_date']}")
    costs = {}
    for key in ("fees", "turnover"):
        t, v = _chart_points(chart, key)[-1]
        if _session(t) != dates[-1]:
            raise ValueError(f"{candidate['id']}: last {key} point {_session(t)} is not on the "
                             f"last session {dates[-1]}")
        costs[key] = v
    eq = np.asarray(equity, dtype=float)
    returns = eq[1:] / eq[:-1] - 1.0
    turnover = np.full(returns.size, costs["turnover"] / max(returns.size, 1))
    row = {"candidate": candidate["id"], "sha": candidate["sha"],
           "frozen_on": candidate["frozen_on"], "pass_date": plan["pass_date"],
           "period_end": dates[-1], "fee_model": candidate["fee_model"],
           **metrics(dates, returns, turnover, costs["fees"])}
    if series_dir is not None:
        series_dir.mkdir(parents=True, exist_ok=True)
        with (series_dir / f"{candidate['id']}_{plan['pass_date']}.csv").open(
                "w", encoding="utf-8", newline="") as f:
            w = csv.writer(f, lineterminator="\n")
            w.writerow(["date", "equity"])
            w.writerows(zip(dates, equity))
    return row


# ---------------------------------------------------------------- CLI

def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--registry", type=Path, required=True)
    ap.add_argument("--csv", type=Path, required=True)
    sub = ap.add_subparsers(dest="cmd", required=True)

    f = sub.add_parser("freeze", help="geler une nouvelle candidate")
    f.add_argument("--id", required=True)
    f.add_argument("--kind", choices=KINDS, required=True)
    f.add_argument("--entrypoint", required=True,
                   help="local : module.py:fonction ; qc : chemin/du/projet:identifiant_du_projet_QC")
    f.add_argument("--sha", required=True, help="commit gele (resolu en SHA complet)")
    f.add_argument("--params", default="{}", help="parametres, en JSON")
    f.add_argument("--fee-model", required=True, help="hypothese de frais, ex. '5bps notional'")
    f.add_argument("--frozen-on", default=dt.date.today().isoformat())
    f.add_argument("--repo", type=Path, default=Path("."))

    sub.add_parser("validate", help="verifier registre et CSV")

    d = sub.add_parser("due", help="lister les candidates a rejouer")
    d.add_argument("--pass-date", default=dt.date.today().isoformat())

    r = sub.add_parser("replay-local", help="rejouer les candidates locales dues")
    r.add_argument("--pass-date", default=dt.date.today().isoformat())
    r.add_argument("--repo", type=Path, default=Path("."))
    r.add_argument("--series-dir", type=Path, default=None,
                   help="dossier hors depot pour les series journalieres")

    p = sub.add_parser("plan-qc", help="preparer le rejeu des candidates QC dues")
    p.add_argument("--pass-date", default=dt.date.today().isoformat())
    p.add_argument("--repo", type=Path, default=Path("."))
    p.add_argument("--out-dir", type=Path, required=True,
                   help="dossier hors depot : un sous-dossier par candidate")

    g = sub.add_parser("ingest-qc", help="ajouter la ligne d'un passage QC termine")
    g.add_argument("--plan-dir", type=Path, required=True,
                   help="dossier d'une candidate, avec plan.json, backtest.json et chart.json")
    g.add_argument("--series-dir", type=Path, default=None,
                   help="dossier hors depot pour les series journalieres")

    a = ap.parse_args(argv)
    candidates = load_registry(a.registry)
    rows = load_rows(a.csv)

    problems = validate(candidates, rows)
    if a.cmd == "validate" or problems:
        for p in problems:
            print(f"INVALID {p}")
        if not problems:
            print(f"OK {len(candidates)} candidates, {len(rows)} passes")
        return 1 if problems else 0

    if a.cmd == "freeze":
        sha = _git(a.repo, "rev-parse", "--verify", f"{a.sha}^{{commit}}")
        entry = freeze(candidates, id=a.id, kind=a.kind, sha=sha, frozen_on=a.frozen_on,
                       entrypoint=a.entrypoint, params=json.loads(a.params),
                       fee_model=a.fee_model)
        save_registry(a.registry, candidates)
        print(json.dumps(entry, ensure_ascii=False))
        return 0

    if a.cmd == "ingest-qc":
        plan = json.loads((a.plan_dir / "plan.json").read_text(encoding="utf-8"))
        candidate = next((c for c in candidates if c["id"] == plan["candidate"]), None)
        if candidate is None:
            print(f"INVALID {plan['candidate']}: not in the registry")
            return 1
        row = ingest_qc(candidate, plan,
                        json.loads((a.plan_dir / "backtest.json").read_text(encoding="utf-8")),
                        json.loads((a.plan_dir / "chart.json").read_text(encoding="utf-8")),
                        a.series_dir)
        append_row(a.csv, row)
        print(json.dumps(row, ensure_ascii=False))
        return 0

    todo = due(candidates, rows, a.pass_date)
    if a.cmd == "plan-qc":
        for c in (c for c in todo if c["kind"] == "qc"):
            plan = plan_qc(a.repo, c, a.pass_date, a.out_dir)
            print(json.dumps({k: plan[k] for k in ("candidate", "qc_project_id", "backtest_name",
                                                   "parameters")}, ensure_ascii=False))
        return 0

    if a.cmd == "due":
        for c in todo:
            print(f"{c['id']} {c['kind']} frozen_on={c['frozen_on']} sha={c['sha'][:10]}")
        return 0

    for c in (c for c in todo if c["kind"] == "local"):
        row = replay_local(a.repo, c, a.pass_date, a.series_dir)
        append_row(a.csv, row)
        print(json.dumps(row, ensure_ascii=False))
    skipped = [c["id"] for c in todo if c["kind"] != "local"]
    if skipped:
        print(f"SKIPPED (qc candidates, replay with plan-qc then ingest-qc): {' '.join(skipped)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
