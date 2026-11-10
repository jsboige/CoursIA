"""Série du cœur actions pour la matrice de corrélation de la ligue (#20365, #19821 brique 4).

Une stratégie n'entre au panier que si elle se décorrèle du cœur : la matrice de
`league_correlation.py` a donc besoin d'une colonne pour le cœur actions. Ce cœur est la
règle de volatilité inverse du harnais paper (#19072, `inverse_vol_currency`) ; il n'a pas
de trace QC, sa série se calcule ici, hors QC, par le point d'entrée de l'ombre
(`shadow_inverse_vol.replay`), sans recopier la règle.

Protocole, amendé dans #20365 avant la mesure :

- convention `U` (volatilité des clôtures en USD, la règle du harnais), cible de
  volatilité `--target` (0,025 dans le verdict de #19072) ;
- **compte en USD** (`--account usd`) : mêmes poids, rendements des clôtures en USD,
  liquidité en USD. Les autres membres de la matrice sont des comptes QC en USD : un cœur
  compté en EUR porterait le change EUR/USD sur sa liquidité, et la corrélation mesurerait
  en partie le change. `--account eur` garde la lecture d'un investisseur en euros, comme
  sensibilité ;
- clôtures quotidiennes Yahoo (ajustées des dividendes) gardées dans `--closes-dir`, pour
  qu'une seconde lecture rejoue les mêmes cours : leurs empreintes vont dans
  `provenance.json`.

Sortie dans `--out` : `series.csv` (colonnes `date`, `net_return`, `turnover`, format de
`shadow_replay.py --series-dir`), lu par `league_correlation.py` pour un membre
`"kind": "local"`, et `provenance.json`.

    python league_core_series.py --out <traces>/20365-league-core/core-equity \\
        --closes-dir <traces>/20365-league-core/closes
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import subprocess
import sys
from pathlib import Path

import inverse_vol_currency as ivc
import shadow_inverse_vol as siv

SERIES = "series.csv"
PROVENANCE = "provenance.json"
DEFAULT_START = "2010-02-01"
DEFAULT_END = "2026-10-01"


def write_series(out: dict, path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8", newline="") as f:
        w = csv.writer(f, lineterminator="\n")
        w.writerow(["date", "net_return", "turnover"])
        w.writerows(zip(out["dates"], out["net_returns"], out["turnover"]))


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _commit() -> str | None:
    try:
        return subprocess.run(["git", "rev-parse", "HEAD"], cwd=Path(__file__).parent,
                              capture_output=True, text=True, check=True).stdout.strip()
    except (OSError, subprocess.CalledProcessError):
        return None


def core_series(start: str, end: str, closes_dir: Path, target: float = ivc.VERDICT_TARGET,
                account: str = "USD") -> dict:
    """Rendements quotidiens nets du cœur ouvert le `start`, sur `[start, end)`."""
    us_closes, fx = siv.fetch_closes(start, end, closes_dir)
    return siv.replay(us_closes, fx, start, end, "U", target, account=account)


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--out", type=Path, required=True, help="dossier du membre (hors dépôt)")
    ap.add_argument("--closes-dir", type=Path, required=True,
                    help="dossier des clôtures Yahoo, réutilisées si présentes")
    ap.add_argument("--start", default=DEFAULT_START)
    ap.add_argument("--end", default=DEFAULT_END, help="exclu")
    ap.add_argument("--target", type=float, default=ivc.VERDICT_TARGET)
    ap.add_argument("--account", choices=["usd", "eur"], default="usd")
    args = ap.parse_args(argv)

    out = core_series(args.start, args.end, args.closes_dir, args.target, args.account.upper())
    write_series(out, args.out / SERIES)
    closes = sorted(p for p in args.closes_dir.glob("*.csv"))
    provenance = {
        "issue": 20365,
        "rule": "inverse_vol_currency (#19072), convention U",
        "account": args.account.upper(), "target": args.target,
        "start": args.start, "end_excluded": args.end,
        "first": out["dates"][0], "last": out["dates"][-1], "sessions": len(out["dates"]),
        "lookback": ivc.LOOKBACK, "max_weight": ivc.MAX_WEIGHT, "band": ivc.BAND, "fee": ivc.FEE,
        "commit": _commit(),
        "closes": {p.name: sha256(p) for p in closes},
        "series_sha256": sha256(args.out / SERIES),
    }
    (args.out / PROVENANCE).write_text(json.dumps(provenance, indent=1) + "\n", encoding="utf-8")
    sys.stdout.write(f"{len(out['dates'])} sessions {out['dates'][0]} -> {out['dates'][-1]}"
                     f" ({args.account.upper()}, target {args.target:g}) -> {args.out / SERIES}\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
