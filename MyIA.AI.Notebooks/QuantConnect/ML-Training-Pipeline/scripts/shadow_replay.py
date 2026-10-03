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

Le rejeu QuantConnect (backtest par le MCP, dates passees en parametres) n'est pas dans ce
module : il depend de la lecture des graphiques (#18939). Il rendra la meme ligne de CSV.
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
                   help="local : module.py:fonction ; qc : identifiant du projet QC dedie")
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

    todo = due(candidates, rows, a.pass_date)
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
        print(f"SKIPPED (QC replay not in this module): {' '.join(skipped)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
