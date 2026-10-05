"""Cadence du suivi en ombre (#18923, etape 3) : planifier les passages mensuels, repartis.

Le rejeu lui-meme est l'affaire de ``shadow_replay.py`` (etape 1) : geler, rejouer, valider.
Ce module ne decide que de QUAND : il lit le registre et l'historique CSV (sans jamais les
ecrire) et rend un plan ordonne -- une marche horodatee qui garde chaque passage sous la
limite d'appels MCP de la flotte (10/min pour toute la flotte, un backtest a la fois, annonce
sur le dashboard avant de lancer).

La cadence documentee (``shadow/README.md``) est un passage par mois a la premiere seance du
mois ; ``first_session_of_month`` en rend la date deterministe (premier jour ouvre du mois).
Le passage reste porte par une lane -- une PR qui ne touche que ``passes.csv`` -- : ce plan
est l'organe de decision, pas le declencheur. Tout cablage d'horloge (workflow ``.github/``
ou tache planifiee machine) revient au coordinateur, pas a ce module.

La marche suit la grammaire de ``shadow_replay.py`` : ``replay-local`` et ``plan-qc``
traitent toutes les candidates dues d'une invocation, la boucle MCP puis ``ingest-qc``
se font candidate par candidate. D'ou l'ordre du plan :

1. ``replay-local`` : toutes les locales dues, aucun appel QC ;
2. ``plan-qc`` : extraction au SHA gele de toutes les QC dues, aucun appel QC ;
3. pour chaque candidate QC, une ``qc-passage`` (pousser les fichiers, compiler, lancer le
   backtest, attendre ``completed: true``, lire backtest et graphique -- **MCP uniquement**,
   coute ``QC_CALLS_PER_PASS`` appels) puis son ``ingest-qc`` ; deux ``qc-passage`` sont
   espacees de ``min_interval_min`` minutes.

``qc_rate`` refuse un espacement dont le debit moyen depasserait le budget partage.

Determinisme : meme registre, meme CSV, meme date -- meme plan. L'ordre des candidates est
``frozen_on`` puis ``id`` ; l'heure de depart est explicite (``--start``), jamais l'horloge.
"""
from __future__ import annotations

import argparse
import datetime as dt
import json
import sys
from pathlib import Path
from zoneinfo import ZoneInfo

sys.path.insert(0, str(Path(__file__).resolve().parent))
from shadow_replay import due, load_registry, load_rows, qc_entrypoint, validate  # noqa: E402

TZ = ZoneInfo("Europe/Paris")
QC_CALLS_PER_PASS = 5
FLEET_BUDGET_PER_MIN = 10
DEFAULT_INTERVAL_MIN = 10
DEFAULT_HOUR = (9, 17)  # heure de depart des marches, hors des minutes pleines


def first_session_of_month(year: int, month: int) -> dt.date:
    """Premier jour ouvre (lundi-vendredi) du mois : approximation de la premiere seance.

    Un jour ferie qui tombe le premier jour ouvre decale la vraie seance ; la PR de passage
    note alors la date reellement jouee, le CSV reste la verite.
    """
    d = dt.date(year, month, 1)
    while d.weekday() >= 5:
        d += dt.timedelta(days=1)
    return d


def pass_date_for(today: dt.date | None = None) -> dt.date:
    """Date du passage a planifier aujourd'hui : premiere seance du mois, au plus tot aujourd'hui."""
    today = today or dt.date.today()
    return max(first_session_of_month(today.year, today.month), today)


def qc_rate(min_interval_min: int, calls_per_pass: int = QC_CALLS_PER_PASS) -> float:
    """Debit moyen d'appels MCP par minute du plan ; espacement nul ou negatif = debit infini."""
    if min_interval_min <= 0:
        return float("inf")
    return calls_per_pass / min_interval_min


def _base_command(registry_path: Path, csv_path: Path, sub: str, *extra: str) -> list[str]:
    # Chemin relatif a la racine du pipeline, la forme que documente shadow/README.md.
    return ["python", "scripts/shadow_replay.py",
            "--registry", str(registry_path), "--csv", str(csv_path), sub, *extra]


def plan_pass(
    registry_path: Path,
    csv_path: Path,
    pass_date: str,
    start: dt.datetime,
    min_interval_min: int = DEFAULT_INTERVAL_MIN,
    budget_per_min: int = FLEET_BUDGET_PER_MIN,
    qc_out_root: Path | None = None,
) -> dict:
    """Plan ordonne du passage de `pass_date` : locals gratuites d'abord, QC espacees ensuite.

    Refuse (ValueError) un registre/CSV invalide et un espacement dont le debit depasserait
    le budget de la flotte. Ne lit que le registre et le CSV ; n'ecrit rien.
    """
    candidates = load_registry(registry_path)
    rows = load_rows(csv_path)
    problems = validate(candidates, rows)
    if problems:
        raise ValueError("registre ou CSV invalide : " + "; ".join(problems))
    rate = qc_rate(min_interval_min)
    if rate > budget_per_min:
        raise ValueError(
            f"espacement {min_interval_min} min -> {rate:.1f} appels/min > budget {budget_per_min}")

    due_candidates = due(candidates, rows, pass_date)
    locals_due = sorted((c for c in due_candidates if c["kind"] == "local"),
                        key=lambda c: (c["frozen_on"], c["id"]))
    qc_due = sorted((c for c in due_candidates if c["kind"] == "qc"),
                    key=lambda c: (c["frozen_on"], c["id"]))
    qc_out_root = qc_out_root or registry_path.parent / "plans"
    qc_out = qc_out_root / pass_date

    def step(slot: dt.datetime, kind: str, ids, qc_calls: int, **extra) -> dict:
        s = {"slot": slot.isoformat(), "kind": kind, "candidate": ids, "qc_calls": qc_calls}
        s.update(extra)
        return s

    steps: list[dict] = []
    slot = start
    if locals_due:
        ids = [c["id"] for c in locals_due]
        steps.append(step(slot, "replay-local", ids, 0,
                          command=_base_command(registry_path, csv_path,
                                                "replay-local", "--pass-date", pass_date)))
        slot += dt.timedelta(minutes=1)
    if qc_due:
        ids = [c["id"] for c in qc_due]
        steps.append(step(slot, "plan-qc", ids, 0, out_dir=str(qc_out),
                          command=_base_command(registry_path, csv_path, "plan-qc",
                                                "--pass-date", pass_date,
                                                "--out-dir", str(qc_out))))
        slot += dt.timedelta(minutes=1)
        for c in qc_due:
            project = qc_entrypoint(c)[1]
            out_dir = qc_out / c["id"]
            steps.append(step(slot, "qc-passage", c["id"], QC_CALLS_PER_PASS,
                              qc_project=project, out_dir=str(out_dir),
                              note="MCP uniquement : pousser les fichiers du dossier au SHA gele, "
                                   "create_compile, create_backtest, attendre completed:true, "
                                   "read_backtest + read_backtest_chart vers out_dir ; "
                                   "annoncer le backtest sur le dashboard avant de lancer"))
            slot += dt.timedelta(minutes=min_interval_min)
            steps.append(step(slot, "ingest-qc", c["id"], 0,
                              command=_base_command(registry_path, csv_path, "ingest-qc",
                                                    "--plan-dir", str(out_dir))))
            slot += dt.timedelta(minutes=1)

    n_qc = len(qc_due)
    return {
        "pass_date": pass_date,
        "n_due": len(due_candidates),
        "n_local": len(locals_due),
        "n_qc": n_qc,
        "qc_calls_total": n_qc * QC_CALLS_PER_PASS,
        "rate_per_min": round(rate, 3),
        "budget_per_min": budget_per_min,
        "min_interval_min": min_interval_min,
        "steps": steps,
    }


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--registry", type=Path, default=Path("shadow/registry.json"))
    ap.add_argument("--csv", type=Path, default=Path("shadow/passes.csv"))
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("plan", help="plan ordonne du passage mensuel")
    p.add_argument("--on", default=None,
                   help="date du passage ISO (defaut : premiere seance du mois, au plus tot aujourd'hui)")
    p.add_argument("--start", default=None,
                   help="heure de depart ISO avec fuseau (defaut : %02d:%02d Europe/Paris le jour du passage)"
                        % DEFAULT_HOUR)
    p.add_argument("--min-interval-min", type=int, default=DEFAULT_INTERVAL_MIN,
                   help="minutes entre deux passages QC (defaut : %d)" % DEFAULT_INTERVAL_MIN)
    p.add_argument("--budget-per-min", type=int, default=FLEET_BUDGET_PER_MIN,
                   help="budget MCP partage de la flotte (defaut : %d)" % FLEET_BUDGET_PER_MIN)
    p.add_argument("--qc-out-root", type=Path, default=None,
                   help="racine des dossiers de plan QC (defaut : <registre>/../plans)")
    p.add_argument("--json", action="store_true", help="sortie machine (defaut : lisible)")
    args = ap.parse_args(argv)

    day = dt.date.fromisoformat(args.on) if args.on else pass_date_for()
    if args.start:
        start = dt.datetime.fromisoformat(args.start)
        if start.tzinfo is None:
            start = start.replace(tzinfo=TZ)
    else:
        start = dt.datetime(day.year, day.month, day.day, *DEFAULT_HOUR, tzinfo=TZ)

    plan = plan_pass(args.registry, args.csv, day.isoformat(), start,
                     min_interval_min=args.min_interval_min,
                     budget_per_min=args.budget_per_min,
                     qc_out_root=args.qc_out_root)
    if args.json:
        print(json.dumps(plan, indent=2, ensure_ascii=False))
        return 0
    print(f"Passage du {plan['pass_date']} : {plan['n_due']} candidate(s) due(s) "
          f"({plan['n_local']} locale(s), {plan['n_qc']} QC, "
          f"{plan['qc_calls_total']} appels MCP, {plan['rate_per_min']}/min pour un budget de "
          f"{plan['budget_per_min']}/min).")
    for s in plan["steps"]:
        calls = f", {s['qc_calls']} appels" if s["qc_calls"] else ""
        ids = s["candidate"] if isinstance(s["candidate"], str) else ", ".join(s["candidate"])
        print(f"  {s['slot']}  {s['kind']}: {ids}{calls}")
        if "command" in s:
            print(f"    {' '.join(s['command'])}")
        elif "note" in s:
            print(f"    {s['note']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
