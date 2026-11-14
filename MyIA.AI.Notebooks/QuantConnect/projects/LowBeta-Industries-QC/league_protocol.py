"""Protocole de la ligue applique au bras `bab` de LowBeta-Industries-QC (#25492).

Trois etapes, separees pour que la mesure soit rejouable sans acces QC :

  fetch    lit, pour chaque backtest QC Cloud, la statistique de la plateforme et les
           graphiques "shadow" (trace journaliere) et "Monthly" (controle d'innocuite),
           puis ecrit tout sur disque. Un graphique journalier sur seize ans ne passe
           jamais dans une fenetre de contexte.
  slice    decoupe la serie journaliere par fenetre et la re-encode au contrat
           `e0..e4` de #18923, de facon a ce que l'organe de la ligue la lise sans
           fenetre de depart (le cycle commence en e0).
  verdict  appelle l'organe de la ligue -- `Paradox46Benchmarks/significance.py`, qui
           fait les trois tests (Ledoit-Wolf, bootstrap stationnaire, Newey-West) et la
           correction de Holm -- puis applique la regle de verdict et ecrit les tables.

  control  compare deux executions d'un meme bras (reference et controle d'innocuite)
           sur les statistiques QC et sur la serie mesuree -- la trace journaliere
           `shadow` quand les deux executions la portent ; si une seule la
           porte, refuse le controle ; sinon compare `Monthly` serie par serie.

Les tests ne sont PAS reimplementes ici : l'organe de la ligue est appele tel quel.
Les identifiants QC viennent de variables d'environnement (jamais dans le code).

Usage :
  python league_protocol.py fetch --project 36854709 --out <dir> \
      --backtest bab=<id> --backtest spy=<id> --backtest 6040=<id> [--backtest ref=<id>]
  python league_protocol.py slice --dir <dir> [--out <dir>]
  python league_protocol.py verdict --dir <dir> [--out measures/league]
  python league_protocol.py control --project 36854709 --ref <id> --ctl <id>
"""
from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
from datetime import datetime
from pathlib import Path

HERE = Path(__file__).resolve().parent
QUANT = HERE.parents[1]                      # .../QuantConnect
LEAGUE = QUANT / "projects" / "Paradox46Benchmarks" / "significance.py"
SCRIPTS = QUANT / "ML-Training-Pipeline" / "scripts"
for path in (str(HERE), str(QUANT / "projects"), str(SCRIPTS)):
    if path not in sys.path:
        sys.path.insert(0, path)

import league_control  # noqa: E402 -- le critere de comparaison, pur et testable hors ligne

# Les acces QC (`analyze_arms`) et le contrat de lecture de la trace
# (`shadow_replay`) sont importes A LA DEMANDE, dans les seules fonctions qui
# les utilisent. Ces deux modules tirent `numpy` : les importer au chargement
# rendrait le protocole illisible hors QC -- et les tests du critere ne
# doivent dependre d'aucun paquet tiers.
def _acces_qc():
    """Les acces QC et le contrat de trace, importes a la demande."""
    from analyze_arms import _call, _chart, _points
    from shadow_replay import QC_EQUITY_SERIES, qc_daily_equity
    return _call, _chart, _points, QC_EQUITY_SERIES, qc_daily_equity

# Fenetres du protocole de la ligue (coupee au 1er janvier 2025).
WINDOWS = {
    "w1": ("2010-01-02", "2024-12-31"),
    "w2": ("2025-01-01", "2026-08-31"),
}
STAT_KEYS = (
    "Sharpe Ratio", "Probabilistic Sharpe Ratio", "Compounding Annual Return", "Drawdown",
    "Annual Standard Deviation", "Alpha", "Beta", "Total Fees", "Total Orders",
    "Portfolio Turnover", "Net Profit", "End Equity",
)
REGIME = "UTC"


# ---------------------------------------------------------------------------- lecture

def _session_date(ts: int) -> str:
    """Date de seance d'un horodatage QC, lue a New York (seances actions US)."""
    from zoneinfo import ZoneInfo
    return datetime.fromtimestamp(ts, ZoneInfo("America/New_York")).date().isoformat()


def _read_stats(project: int, backtest: str) -> dict:
    _call, _, _, _, _ = _acces_qc()
    bt = _call("/backtests/read", {"projectId": project, "backtestId": backtest})["backtest"]
    return {
        "backtestId": backtest,
        "name": bt.get("name"),
        "parameterSet": bt.get("parameterSet"),
        "completed": bt.get("completed"),
        "statistics": {k: (bt.get("statistics") or {}).get(k) for k in STAT_KEYS},
    }


def _series_points(chart: dict) -> dict[str, list[tuple[int, float]]]:
    """Les points de chaque serie d'un graphique, ranges par horodatage.

    Serie par serie, et non concatenation : deux graphiques qui n'exposent pas
    le meme jeu de series doivent pouvoir etre compares sur ce qu'ils ont en
    commun, sans que la comparaison se fonde sur une difference de longueur.
    """
    out = {}
    _, _, _points, _, _ = _acces_qc()
    for name, serie in (chart.get("series") or {}).items():
        points = []
        for t, v in _points(serie):
            points.append((int(t), float(v)))
        out[name] = sorted(points)
    return out


def _shadow_rows(chart: dict) -> list[tuple[str, float]]:
    """La trace journaliere d'un graphique `shadow`, une valeur par seance.

    L'organe de lecture (`qc_daily_equity`) verifie l'alternance `e0..e4` :
    une trace qui perd un point est refusee avant meme la comparaison.
    """
    _, _, _, _, qc_daily_equity = _acces_qc()
    dates, equity = qc_daily_equity(chart)
    return list(zip(dates, equity))


# ---------------------------------------------------------------------------- fetch

def cmd_fetch(args) -> int:
    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=True)
    index = {}
    for item in args.backtest:
        arm, backtest = item.split("=", 1)
        _, _chart, _, _, _ = _acces_qc()
        stats = _read_stats(args.project, backtest)
        shadow = _chart(args.project, backtest, "shadow")
        (out / f"{arm}_shadow.json").write_text(json.dumps(shadow), encoding="utf-8")
        monthly = _chart(args.project, backtest, "Monthly")
        (out / f"{arm}_monthly.json").write_text(json.dumps(monthly), encoding="utf-8")
        index[arm] = {"backtestId": backtest, "name": stats.get("name"),
                      "parameterSet": stats.get("parameterSet"),
                      "statistics": stats["statistics"]}
        print(f"{arm}: {backtest} ({stats.get('name')})", flush=True)
    (out / "index.json").write_text(json.dumps(index, indent=1, ensure_ascii=False) + "\n", encoding="utf-8")
    return 0


# ---------------------------------------------------------------------------- slice

def _raw_points(chart: dict) -> list[tuple[int, float]]:
    """Les points (t, v) de la trace, tries par date.

    Seules les series du contrat `e0..e4` sont lues : c'est ce que
    l'organe (`qc_daily_equity`) compte, et les deux lectures doivent
    couvrir le meme ensemble de seances.

    Les horodatages sont **conserves** : le contrat `e0..e4` se relit par
    `fromtimestamp`, une date en chaine de caracteres y echouerait.
    """
    series = chart.get("series") or {}
    points = []
    _, _, _, QC_EQUITY_SERIES, _ = _acces_qc()
    for key in QC_EQUITY_SERIES:
        for p in (series.get(key) or {}).get("values") or []:
            t, v = (p.get("x"), p.get("y")) if isinstance(p, dict) else (p[0], p[-1])
            if t is not None and v is not None:
                points.append((int(t), float(v)))
    return sorted(points)


def _daily(path: Path) -> tuple[list[str], list[float], list[tuple[int, float]]]:
    """La serie journaliere d'un graphique "shadow", validee par l'organe (#18923).

    REND les dates, les valeurs ET les points bruts : la re-encode par
    fenetre doit conserver l'horodatage d'origine.
    """
    chart = json.loads(path.read_text(encoding="utf-8"))
    _, _, _, _, qc_daily_equity = _acces_qc()
    dates, equity = qc_daily_equity(chart)
    points = _raw_points(chart)
    if len(points) != len(dates):
        raise SystemExit(f"{path.name} : {len(points)} points pour {len(dates)} seances")
    return dates, equity, points


def _encode(points: list[tuple[int, float]]) -> dict:
    """Re-encode une serie journaliere au contrat `e0..e4` : le cycle commence en e0.

    Les horodatages d'origine sont conserves : l'organe de la ligue lit les
    points par `fromtimestamp` et refuse une date en chaine de caracteres.
    """
    series = {f"e{k}": {"values": []} for k in range(5)}
    for i, (t, v) in enumerate(points):
        series[f"e{i % 5}"]["values"].append([int(t), float(v)])
    return {"name": "shadow", "series": series}


def cmd_slice(args) -> int:
    src = Path(args.dir)
    out = Path(args.out) if args.out else src / "windows"
    out.mkdir(parents=True, exist_ok=True)
    index = json.loads((src / "index.json").read_text(encoding="utf-8"))
    arms = [arm for arm in index if arm != "ref"]
    series = {}
    for arm in arms:
        dates, equity, points = _daily(src / f"{arm}_shadow.json")
        series[arm] = (dates, equity, points)
        print(f"{arm}: {len(dates)} seances, {dates[0]} -> {dates[-1]}", flush=True)
    for window, (lo, hi) in WINDOWS.items():
        kept = {}
        for arm in arms:
            dates, equity, points = series[arm]
            keep = [pt for pt, d in zip(points, dates) if lo <= d <= hi]
            if not keep:
                raise SystemExit(f"{window}/{arm} : aucune seance dans la fenetre")
            kept[arm] = ([d for d in dates if lo <= d <= hi], keep)
            chart = _encode(keep)
            (out / f"{window}_{arm}.json").write_text(json.dumps(chart), encoding="utf-8")
        n = {arm: len(kept[arm][1]) for arm in arms}
        print(f"{window} ({lo} -> {hi}) : {n}", flush=True)
        if len(set(n.values())) != 1:
            raise SystemExit(f"{window} : calendriers differents entre bras {n}")
        # Meme nombre de seances ne veut pas dire memes seances : l'organe de
        # la ligue apparie les rendements par date et refuse une divergence.
        ref = kept[arms[0]][0]
        for arm in arms[1:]:
            if kept[arm][0] != ref:
                raise SystemExit(f"{window} : les seances de {arm} different de {arms[0]}")
    return 0


# ---------------------------------------------------------------------------- verdict

def _verdict(res: dict) -> str:
    """Regle de verdict de la ligue, par fenetre.

    BEATS  : ecart de Sharpe positif et p de Holm (Ledoit-Wolf) < 0,05 contre LES DEUX
             references ;
    NO BEATS : Sharpe ponctuel inferieur a celui de SPY detenu ;
    INCONCLUSIVE : tous les autres cas.
    """
    cmp_spy = res["comparisons"]["spy"]
    cmp_6040 = res["comparisons"]["6040"]
    p_spy = res["p_holm"]["spy/ledoit_wolf"]
    p_6040 = res["p_holm"]["6040/ledoit_wolf"]
    if (cmp_spy["sharpe_diff"] > 0 and cmp_6040["sharpe_diff"] > 0
            and p_spy < 0.05 and p_6040 < 0.05):
        return "BEATS"
    if cmp_spy["sharpe_a"] < cmp_spy["sharpe_b"]:
        return "NO BEATS"
    return "INCONCLUSIVE"


def cmd_verdict(args) -> int:
    src = Path(args.dir)
    windows_dir = src / "windows"
    out = Path(args.out) if args.out else HERE / "measures" / "league"
    out.mkdir(parents=True, exist_ok=True)
    results = {}
    for window in WINDOWS:
        strategy = windows_dir / f"{window}_bab.json"
        spy = windows_dir / f"{window}_spy.json"
        ref6040 = windows_dir / f"{window}_6040.json"
        raw = out / f"{window}_significance.json"
        cmd = [sys.executable, str(LEAGUE),
               "--strategy", str(strategy),
               "--bench", f"spy={spy}",
               "--bench", f"6040={ref6040}",
               "--out", str(raw)]
        subprocess.run(cmd, check=True, cwd=str(QUANT / "ML-Training-Pipeline" / "scripts"))
        res = json.loads(raw.read_text(encoding="utf-8"))
        res["verdict"] = _verdict(res)
        results[window] = res
        print(f"{window}: {res['verdict']}", flush=True)
    (out / "verdict.json").write_text(json.dumps(results, indent=1, ensure_ascii=False) + "\n", encoding="utf-8")
    (out / "verdict.md").write_text(_markdown(results), encoding="utf-8")
    return 0


def _fr(x: float, nd: int = 3) -> str:
    return f"{x:.{nd}f}".replace(".", ",")


def _markdown(results: dict) -> str:
    lines = ["# Protocole de la ligue -- bras `bab` de LowBeta-Industries-QC", ""]
    for window, res in results.items():
        lo, hi = WINDOWS[window]
        lines += [f"## Fenetre {window} ({lo} -> {hi})", ""]
        lines += ["| Reference | Sharpe bab | Sharpe reference | ecart | p brute (LW) | p de Holm (LW) | p de Holm (bootstrap) | p de Holm (NW) |",
                  "|---|---|---|---|---|---|---|---|"]
        for name in ("spy", "6040"):
            c = res["comparisons"][name]
            lines.append(
                f"| `{name}` | {_fr(c['sharpe_a'])} | {_fr(c['sharpe_b'])} | {_fr(c['sharpe_diff'])} "
                f"| {_fr(c['ledoit_wolf']['p_two_sided'], 4)} | {_fr(res['p_holm'][f'{name}/ledoit_wolf'], 4)} "
                f"| {_fr(res['p_holm'][f'{name}/bootstrap'], 4)} | {_fr(res['p_holm'][f'{name}/mean_diff'], 4)} |")
        lines += ["", f"**Verdict : {res['verdict']}**", ""]
    return "\n".join(lines) + "\n"


# ---------------------------------------------------------------------------- control

def _chart_or_none(project: int, backtest: str, name: str):
    """Le graphique s'il est expose par ce run, None sinon.

    Un run anterieur a la trace `shadow` ne l'expose pas : son absence est une
    information, pas une erreur. Seul `RuntimeError` -- leve par `_chart`
    quand la plateforme n'a pas le graphique -- est traite comme une absence ;
    toute autre erreur remonte.
    """
    try:
        _, _chart, _, _, _ = _acces_qc()
        chart = _chart(project, backtest, name)
    except RuntimeError:
        return None
    return chart if (chart.get("series") or {}) else None


def cmd_control(args) -> int:
    """Controle d'innocuite : deux executions d'un meme bras doivent coincider.

    Deux comparaisons :

      1. les statistiques de la plateforme, cle par cle ;
      2. la serie **mesuree** -- la trace journaliere `shadow` quand les deux
         executions la portent (c'est elle que le protocole consomme). Si une
         seule execution la porte, le controle est refuse ; si aucune ne la
         porte, la serie mensuelle `Monthly` est comparee serie par serie.

    Une serie exposee d'un seul cote est RAPPORTEE, pas comptee comme
    divergence : un graphique peut n'exposer qu'une partie de ses series.
    Mesure 2026-11-09 : le run instrume du bras `bab` n'expose que `ret` sur
    `Monthly`, la ou le run de reference expose `ret`, `spy`, `netexp` et
    `gross` -- le code trace ces quatre series inconditionnellement, la
    difference est cote exposition, pas cote valeurs. Comparer la
    concatenation des series rendait ce controle rouge pour une raison qui
    n'est pas une divergence.

    La porte reste sur la divergence de VALEURS des series presentes des deux
    cotes : c'est ce qui distingue une divergence d'une exposition differente.
    """
    _, _chart, _, _, _ = _acces_qc()
    ref = _read_stats(args.project, args.ref)
    ctl = _read_stats(args.project, args.ctl)
    diffs = {k: (ref["statistics"][k], ctl["statistics"][k])
             for k in STAT_KEYS if ref["statistics"][k] != ctl["statistics"][k]}

    ref_shadow = _chart_or_none(args.project, args.ref, "shadow")
    ctl_shadow = _chart_or_none(args.project, args.ctl, "shadow")
    out = {"reference": ref, "control": ctl, "statistics_diff": diffs}

    if ref_shadow is not None and ctl_shadow is not None:
        out.update(_compare_shadow(ref_shadow, ctl_shadow))
    elif (ref_shadow is None) != (ctl_shadow is None):
        missing = "reference" if ref_shadow is None else "controle"
        out.update({"compared": "shadow", "divergence": [],
                    "refus": f"trace journaliere absente du cote {missing}"})
    else:
        out.update(_compare_monthly(_chart(args.project, args.ref, "Monthly"),
                                    _chart(args.project, args.ctl, "Monthly")))
    if "refus" in out:
        out["verdict"] = "REFUS"
    else:
        out["verdict"] = "OK" if not diffs and not out["divergence"] else "DIVERGENCE"
    print(json.dumps(out, indent=1, ensure_ascii=False))
    if args.out:
        Path(args.out).write_text(json.dumps(out, indent=1, ensure_ascii=False) + "\n", encoding="utf-8")
    return 0 if out["verdict"] == "OK" else 1


def _compare_monthly(chart_ref: dict, chart_ctl: dict) -> dict:
    """Compare deux graphiques `Monthly`, serie par serie.

    La lecture des points est ici (cote QC) ; le **critere** est dans
    `league_control`, qui le teste hors ligne. La porte porte sur la
    divergence de VALEURS des series presentes des deux cots ; une serie
    exposee d'un seul cote est **rapportee**, pas comptee comme divergence.
    C'est ce qui distingue une divergence de mesure d'une exposition
    differente (mesure du 2026-11-09 : le run instrume du bras `bab` n'expose
    que `ret`, la ou la reference en expose quatre).
    """
    out = league_control.compare_series(_series_points(chart_ref),
                                        _series_points(chart_ctl))
    out["compared"] = "Monthly"
    return out


def _compare_shadow(chart_ref: dict, chart_ctl: dict) -> dict:
    """Compare deux traces journalieres : seances et valeurs, point par point.

    C'est la comparaison que le protocole consomme : la trace journaliere, pas
    la serie mensuelle. La lecture de la trace est ici (cote QC) ; le
    critere est dans `league_control`.
    """
    out = league_control.compare_rows(_shadow_rows(chart_ref), _shadow_rows(chart_ctl))
    out["compared"] = "shadow"
    return out


# ---------------------------------------------------------------------------- main

def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    sub = ap.add_subparsers(dest="cmd", required=True)

    p = sub.add_parser("fetch")
    p.add_argument("--project", type=int, required=True)
    p.add_argument("--out", required=True)
    p.add_argument("--backtest", action="append", required=True)
    p.set_defaults(func=cmd_fetch)

    p = sub.add_parser("slice")
    p.add_argument("--dir", required=True)
    p.add_argument("--out")
    p.set_defaults(func=cmd_slice)

    p = sub.add_parser("verdict")
    p.add_argument("--dir", required=True)
    p.add_argument("--out")
    p.set_defaults(func=cmd_verdict)

    p = sub.add_parser("control")
    p.add_argument("--project", type=int, required=True)
    p.add_argument("--ref", required=True)
    p.add_argument("--ctl", required=True)
    p.add_argument("--out")
    p.set_defaults(func=cmd_control)

    args = ap.parse_args(argv)
    return args.func(args)


if __name__ == "__main__":
    raise SystemExit(main())
