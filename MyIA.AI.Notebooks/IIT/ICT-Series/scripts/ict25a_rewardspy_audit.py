"""Audit rewardspy d'un artefact de montee en echelle ICT-25a (Gate 21, #5105).

Ce que fait ce script
---------------------
Il prend un artefact `runs/ict25a_*.json`, traduit ses records en
`RolloutRecord` (via `ict25_records.audit_rows`), les fait passer dans le
**vrai** moteur `rewardspy` (`MetricStore.append` -> `DetectionEngine.process`)
et imprime le verdict par detecteur et le verdict global.

Pourquoi il existe : Gate 21 demande « rewardspy rend-il le meme verdict N/I ? ».
Tant que les artefacts ne portaient que des agregats par graine, la question
n'avait pas d'instrument. Le pont est desormais explicite et testable.

Fenetres
--------
L'artefact porte deux echantillons (`records_sample` tete, `records_sample_tail`
queue). L'audit les traite **separement** quand ils sont disjoints : un detecteur
de derive peut voir la tete saine et la queue pathologique, ou l'inverse, et
moyenner les deux effacerait exactement l'information cherchee.

Le paquet `rewardspy` n'est pas sur PyPI : il s'installe depuis son depot git
(cf `MyIA.AI.Notebooks/GenAI/PostTraining/requirements.txt`). Le script echoue
proprement, avec la marche a suivre, quand il est absent.

Usage :
    python ict25a_rewardspy_audit.py --artifact runs/ict25a_N_traces_1.5B.json
    python ict25a_rewardspy_audit.py --artifact ... --window tail --json
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from ict25_records import audit_rows  # noqa: E402

WINDOWS = ("head", "tail", "both")


def _load_artifact(path):
    payload = json.loads(Path(path).read_text(encoding="utf-8"))
    if "seeds" not in payload:
        raise SystemExit(f"artefact sans cle 'seeds' : {path}")
    return payload


def _windows_of(seed_entry, window):
    """(nom, records) pour la ou les fenetres demandees."""
    head = list(seed_entry.get("records_sample") or [])
    tail = list(seed_entry.get("records_sample_tail") or [])
    if window == "head":
        return [("head", head)]
    if window == "tail":
        return [("tail", tail)]
    # both : la queue n'est utile que si elle n'est pas deja couverte par la tete
    return [("head", head)] + ([("tail", tail)] if tail else [])


def _audit(rows, sensitivity):
    import rewardspy
    from rewardspy.detectors import DetectionEngine

    store = rewardspy.MetricStore(name="ict25a")
    engine = DetectionEngine(store, sensitivity=sensitivity)
    alerts = []
    for row in rows:
        record = rewardspy.RolloutRecord(**row)
        store.append(record)
        alerts.extend(engine.process(record))
    counts = {}
    for alert in alerts:
        key = getattr(alert, "detector", None) or getattr(alert, "name", None) \
            or type(alert).__name__
        counts[str(key)] = counts.get(str(key), 0) + 1
    return {"alerts": counts, "n_alerts": len(alerts), "overall": str(engine.overall)}


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--artifact", required=True,
                    help="artefact JSON produit par ict25a_scaleup_grpo.py")
    ap.add_argument("--seed", type=int, default=None,
                    help="graine a auditer (defaut : toutes celles de l'artefact)")
    ap.add_argument("--window", choices=WINDOWS, default="both")
    ap.add_argument("--sensitivity", default="medium",
                    help="sensibilite du DetectionEngine (defaut medium)")
    ap.add_argument("--json", action="store_true")
    args = ap.parse_args()

    try:
        import rewardspy  # noqa: F401
    except ImportError:
        print("REFUS: rewardspy absent de cet interpretateur. Il ne s'installe pas "
              "depuis PyPI -- voir MyIA.AI.Notebooks/GenAI/PostTraining/requirements.txt "
              "(pip install git+https://github.com/AvAdiii/rewardspy.git).")
        return 2

    payload = _load_artifact(args.artifact)
    report = {"artifact": str(args.artifact), "arm": payload.get("arm"),
              "model": payload.get("model"), "sensitivity": args.sensitivity,
              "protocol": payload.get("protocol"), "seeds": []}

    for entry in payload["seeds"]:
        if args.seed is not None and entry.get("seed") != args.seed:
            continue
        for name, records in _windows_of(entry, args.window):
            if not records:
                report["seeds"].append({"seed": entry.get("seed"), "window": name,
                                        "n": 0, "skipped": "fenetre vide ou absente"})
                continue
            rows = audit_rows(records, arm=str(payload.get("arm")),
                              seed=int(entry.get("seed", 0)))
            result = _audit(rows, args.sensitivity)
            result.update({"seed": entry.get("seed"), "window": name, "n": len(rows)})
            report["seeds"].append(result)
            if not args.json:
                print(f"seed {entry.get('seed')} [{name}] n={len(rows)} -> "
                      f"{result['overall']} ({result['n_alerts']} alertes)"
                      + (f" {result['alerts']}" if result["alerts"] else ""))

    if args.json:
        print(json.dumps(report, indent=2, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
