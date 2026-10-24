"""Re-derive les enveloppes VRAM 8 Go depuis leur trace brute.

Les manifestes de `scripts/results/3d_enveloppe_8go/` portent des agregats
(pic, repos, plateaux par phase) dont la valeur de preuve depend entierement de
la serie `nvidia-smi` qui les a produits. Cet organe refait le calcul depuis la
trace, sans GPU et sans rejouer les carnets, et compare aux champs des
manifestes.

Trois familles de controles :

1. **Empreinte** : le `sha256` enregistre dans `provenance.trace_sha256` doit
   etre celui du fichier present sur le disque. Une trace remplacee est donc
   detectee, meme si ses agregats tombent juste par hasard.
2. **Derivation** : `vram.samples`, `vram.sample_period_s`, `vram.peak_mib`
   doivent etre reproductibles depuis la serie ; `vram.idle_mib` doit figurer
   parmi les premiers echantillons (repos d'avant run), et non etre une valeur
   posee sans reference.
3. **Existence des echantillons cites** : chaque `profil_par_phase_mib[i]
   .plateau_mib` doit etre une valeur reellement presente dans la fenetre de sa
   phase. C'est la lecture arbitree en #22110 : le champ designe un echantillon
   de palier, pas la statistique du palier — l'organe affiche la statistique a
   cote pour que l'ecart reste lisible.

Ce qu'il ne fait pas : il ne rejoue rien, ne corrige aucun manifeste et n'est
pas cable en CI. Un ecart se lit et se discute, il ne se rabote pas.

Usage :

    python scripts/audit/check_vram_envelope_rederivable.py
    python scripts/audit/check_vram_envelope_rederivable.py --json
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import statistics
import sys
from collections import Counter
from datetime import datetime
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
RESULTS = ROOT / "scripts" / "results" / "3d_enveloppe_8go"
TRACES = RESULTS / "traces"

# Un run par trace presente. 3D-4d n'y figure pas : sa serie est perdue, ce que
# son manifeste declare (`provenance.trace == "perdue"`) et qu'aucun organe ne
# peut re-deriver.
RUNS = {
    "3d01": {
        "manifest": "3d01_enveloppe_8go.json",
        "trace": "vram-3d01.csv",
        "idle_looked_up_in_first_n_samples": 5,
    },
    "3d02": {
        "manifest": "3d02_enveloppe_8go.json",
        "trace": "vram-3d02.csv",
        "idle_looked_up_in_first_n_samples": 5,
    },
}

PERIOD_TOLERANCE_S = 0.5


def load_trace(path: Path) -> list[tuple[float, int]]:
    """Rend [(secondes depuis le premier echantillon, memoire Mio)]."""
    text = path.read_bytes().decode("utf-8-sig")
    rows = list(csv.DictReader(text.splitlines()))
    if not rows:
        raise SystemExit(f"trace vide : {path}")
    if "horodatage" not in rows[0] or "memoire_mib" not in rows[0]:
        raise SystemExit(f"en-tete inattendu dans {path} : {list(rows[0])}")
    t0 = datetime.fromisoformat(rows[0]["horodatage"])
    return [
        ((datetime.fromisoformat(r["horodatage"]) - t0).total_seconds(), int(r["memoire_mib"]))
        for r in rows
    ]


def window_bounds(spec: str) -> tuple[float, float]:
    start, _, end = spec.partition("-")
    return float(start), float(end)


def check_run(key: str, cfg: dict) -> dict:
    manifest = json.loads((RESULTS / cfg["manifest"]).read_text(encoding="utf-8"))
    trace_path = TRACES / cfg["trace"]
    series = load_trace(trace_path)
    times = [t for t, _ in series]
    values = [v for _, v in series]

    findings: list[dict] = []

    def record(check: str, ok: bool, measured, declared, note: str = "") -> None:
        findings.append(
            {"check": check, "ok": ok, "measured": measured, "declared": declared, "note": note}
        )

    declared_sha = (manifest.get("provenance") or {}).get("trace_sha256")
    actual_sha = hashlib.sha256(trace_path.read_bytes()).hexdigest()
    record("trace_sha256", declared_sha == actual_sha, actual_sha[:12], (declared_sha or "")[:12],
           "empreinte du fichier present sur le disque")

    vram = manifest.get("vram", {})
    record("samples", vram.get("samples") == len(series), len(series), vram.get("samples"))

    deltas = [b - a for a, b in zip(times, times[1:])]
    observed_period = statistics.median(deltas) if deltas else 0.0
    declared_period = vram.get("sample_period_s")
    record(
        "sample_period_s",
        declared_period is not None and abs(observed_period - declared_period) <= PERIOD_TOLERANCE_S,
        round(observed_period, 2),
        declared_period,
        f"cadence observee, tolerance {PERIOD_TOLERANCE_S} s",
    )

    peak = max(values)
    record("peak_mib", vram.get("peak_mib") == peak, peak, vram.get("peak_mib"),
           f"indices {[i for i, v in enumerate(values) if v == peak]}")

    idle = vram.get("idle_mib")
    head = values[: cfg["idle_looked_up_in_first_n_samples"]]
    record("idle_mib", idle in head, head, idle,
           f"doit figurer parmi les {cfg['idle_looked_up_in_first_n_samples']} premiers echantillons")

    for index, phase in enumerate(vram.get("profil_par_phase_mib", [])):
        lo, hi = window_bounds(phase["fenetre_s"])
        window = [(i, v) for i, (t, v) in enumerate(series) if lo <= t < hi]
        if not window:
            record(f"phase[{index}].plateau_mib", False, "fenetre vide", phase["plateau_mib"],
                   phase["fenetre_s"])
            continue
        window_values = [v for _, v in window]
        stat = {
            "n": len(window_values),
            "min": min(window_values),
            "max": max(window_values),
            "median": statistics.median(window_values),
            "mode": Counter(window_values).most_common(1)[0][0],
        }
        record(
            f"phase[{index}].plateau_mib",
            phase["plateau_mib"] in window_values,
            phase["plateau_mib"],
            phase["plateau_mib"],
            f"fenetre {phase['fenetre_s']} | statistique : n={stat['n']} min={stat['min']} "
            f"max={stat['max']} mediane={stat['median']} mode={stat['mode']}",
        )

    return {"run": key, "trace": cfg["trace"], "bytes": trace_path.stat().st_size,
            "checks": findings}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true", help="sortie machine")
    args = parser.parse_args(argv)

    reports = [check_run(key, cfg) for key, cfg in RUNS.items()]
    failures = [f for r in reports for f in r["checks"] if not f["ok"]]

    if args.json:
        print(json.dumps({"reports": reports, "failures": len(failures)}, ensure_ascii=False, indent=1))
        return 1 if failures else 0

    for report in reports:
        print(f"== {report['run']} ({report['trace']}, {report['bytes']} octets)")
        for f in report["checks"]:
            status = "ok  " if f["ok"] else "FAIL"
            print(f"  {status} {f['check']:<32} mesure={f['measured']!s:<18} declare={f['declared']!s:<18} {f['note']}")
    print()
    if failures:
        print(f"ECHEC : {len(failures)} controle(s) en desaccord avec la trace")
        return 1
    print("OK : tous les agregats des manifestes se re-derivent de leur trace brute")
    return 0


if __name__ == "__main__":
    sys.exit(main())
