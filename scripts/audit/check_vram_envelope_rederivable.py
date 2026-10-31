"""Re-derive les enveloppes VRAM 8 Go depuis leur trace brute.

Les manifestes de `scripts/results/3d_enveloppe_8go/` portent des agregats
(pic, repos, plateaux par phase) dont la valeur de preuve depend entierement de
la serie `nvidia-smi` qui les a produits. Cet organe refait le calcul depuis la
trace, sans GPU et sans rejouer les carnets, et compare aux champs des
manifestes.

Trois familles de controles :

1. **Empreinte** : le `sha256` enregistre dans `provenance.trace_sha256` doit
   etre celui du fichier present sur le disque, et celui du JOURNAL aussi
   (`provenance.journal_sha256`) : une trace ou un journal remplace est donc
   detecte, meme si ses agregats tombent juste par hasard.
2. **Derivation exacte** : tout champ scalaire re-calculable l'est, sans
   tolerance -- `vram.samples`, `vram.sample_period_s` (tolerance de cadence
   declaree), `vram.peak_mib`, `vram.peak_pct`, `vram.temp_max_c`,
   `vram.util_max_pct`, et les trois `provenance.trace_bytes` /
   `trace_samples` / `trace_span_s`. Un champ qui derive rougit.
3. **Echantillon ancre** : `vram.idle_mib` est compare a l'echantillon que le
   `field_map` du manifeste designe. L'indice est **lu dans le manifeste**
   (`provenance.field_map.idle_mib` : « trace indice 2 (t=10 s) » dans les deux
   runs), puis recoupe avec l'ancre attendue par l'organe : les deux doivent
   designer le meme echantillon, sinon le controle echoue. Une ancre que le
   manifeste ne nomme plus en clair echoue aussi — l'organe ne suppose pas
   d'ancre a la place du manifeste.
4. **Existence des echantillons cites** : chaque `profil_par_phase_mib[i]
   .plateau_mib` doit etre une valeur reellement presente dans la fenetre de sa
   phase. C'est la lecture arbitree en #22110 : le champ designe un echantillon
   de palier, pas la statistique du palier — l'organe affiche la statistique
   (n, min, max, mediane, mode) a cote pour que l'ecart reste lisible, et
   n'arbitre pas lequel des echantillons merite le nom de palier.

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
import re
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
#
# `idle_sample_index` n'est pas une commodite : c'est l'ancre ATTENDUE par
# l'organe, celle que le `provenance.field_map` du manifeste designe (« trace
# indice 2 (t=10 s) » dans 3D-01 comme dans 3D-02). L'organe LIT l'indice
# dans le manifeste et le recoupe avec celui-ci : une divergence, ou une ancre
# que le manifeste ne nomme plus en clair, fait echouer le controle. C'est ce
# recoupement qui empeche l'appartenance vague aux premiers echantillons -- qui
# laissait passer la valeur de rampe (2 912, indice 4 de 3D-01) pour un repos.
RUNS = {
    "3d01": {
        "manifest": "3d01_enveloppe_8go.json",
        "trace": "vram-3d01.csv",
        "journal": "3d01-enveloppe.log",
        "idle_sample_index": 2,
    },
    "3d02": {
        "manifest": "3d02_enveloppe_8go.json",
        "trace": "vram-3d02.csv",
        "journal": "3d02-enveloppe.log",
        "idle_sample_index": 2,
    },
}

PERIOD_TOLERANCE_S = 0.5

# L'ancre de `idle_mib` est nommee en clair par le manifeste. La forme stricte
# (« trace indice 2 ») est cherchee d'abord ; la forme large (« indice 2 ») sert
# de repli. Si aucune ne donne d'indice, l'ancre est None et le controle
# echoue : une ancre illisible ne vaut pas une ancre supposee.
IDLE_ANCHOR_RE = re.compile(r"trace\s+indice\s+(\d+)", re.IGNORECASE)
IDLE_ANCHOR_LOOSE_RE = re.compile(r"indice\s+(\d+)", re.IGNORECASE)


def _idle_anchor(provenance: dict) -> int | None:
    """Indice que `provenance.field_map.idle_mib` designe, lu dans le manifeste.

    Retourne None si le manifeste ne nomme pas d'indice lisible : l'appelant
    traite alors l'absence comme un echec, pas comme une ancre par defaut.
    """
    field_map = provenance.get("field_map") or {}
    text = field_map.get("idle_mib")
    if not isinstance(text, str):
        return None
    for pattern in (IDLE_ANCHOR_RE, IDLE_ANCHOR_LOOSE_RE):
        match = pattern.search(text)
        if match:
            return int(match.group(1))
    return None


def load_trace(path: Path) -> list[tuple[float, int, int, int]]:
    """Rend [(secondes depuis le premier echantillon, memoire Mio, util %, temp C)]."""
    text = path.read_bytes().decode("utf-8-sig")
    rows = list(csv.DictReader(text.splitlines()))
    if not rows:
        raise SystemExit(f"trace vide : {path}")
    expected = {"horodatage", "memoire_mib", "utilisation_gpu", "temp_gpu_c"}
    if not expected <= set(rows[0]):
        raise SystemExit(f"en-tete inattendu dans {path} : {list(rows[0])}")
    t0 = datetime.fromisoformat(rows[0]["horodatage"])
    return [
        (
            (datetime.fromisoformat(r["horodatage"]) - t0).total_seconds(),
            int(r["memoire_mib"]),
            int(r["utilisation_gpu"]),
            int(r["temp_gpu_c"]),
        )
        for r in rows
    ]


def window_bounds(spec: str) -> tuple[float, float]:
    start, _, end = spec.partition("-")
    return float(start), float(end)


def check_run(key: str, cfg: dict) -> dict:
    manifest = json.loads((RESULTS / cfg["manifest"]).read_text(encoding="utf-8"))
    trace_path = TRACES / cfg["trace"]
    journal_path = TRACES / cfg["journal"]
    raw = trace_path.read_bytes()
    series = load_trace(trace_path)
    times = [t for t, _, _, _ in series]
    values = [v for _, v, _, _ in series]
    utils = [u for _, _, u, _ in series]
    temps = [c for _, _, _, c in series]

    findings: list[dict] = []

    def record(check: str, ok: bool, measured, declared, note: str = "") -> None:
        findings.append(
            {"check": check, "ok": ok, "measured": measured, "declared": declared, "note": note}
        )

    provenance = manifest.get("provenance") or {}
    declared_sha = provenance.get("trace_sha256")
    actual_sha = hashlib.sha256(raw).hexdigest()
    record("trace_sha256", declared_sha == actual_sha, actual_sha[:12], (declared_sha or "")[:12],
           "empreinte du fichier present sur le disque")

    journal_sha = hashlib.sha256(journal_path.read_bytes()).hexdigest() if journal_path.is_file() else None
    declared_journal_sha = provenance.get("journal_sha256")
    record(
        "journal_sha256",
        journal_sha is not None and declared_journal_sha == journal_sha,
        (journal_sha or "journal absent")[:12] if journal_sha else "journal absent",
        (declared_journal_sha or "")[:12],
        f"empreinte du journal brut ({journal_path.stat().st_size if journal_path.is_file() else 0} octets)"
        " -- c'est lui qui porte le transcodage UTF-16",
    )

    vram = manifest.get("vram", {})
    record("samples", vram.get("samples") == len(series), len(series), vram.get("samples"))

    declared_bytes = provenance.get("trace_bytes")
    record("trace_bytes", declared_bytes == len(raw), len(raw), declared_bytes,
           "taille du fichier sur le disque")

    declared_trace_samples = provenance.get("trace_samples")
    record("trace_samples", declared_trace_samples == len(series), len(series),
           declared_trace_samples)

    declared_span = provenance.get("trace_span_s")
    span = round(times[-1], 1) if times else 0.0
    record("trace_span_s", declared_span is not None and abs(span - declared_span) <= 0.05,
           span, declared_span, "dernier horodatage moins le premier")

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

    card = vram.get("card_mib")
    declared_pct = vram.get("peak_pct")
    peak_pct = round(peak / card * 100, 1) if card else None
    record("peak_pct", peak_pct is not None and abs(peak_pct - declared_pct) <= 0.05,
           peak_pct, declared_pct, f"pic / {card} Mio, arrondi au dixieme")

    idle = vram.get("idle_mib")
    declared_anchor = _idle_anchor(provenance)
    expected_anchor = cfg["idle_sample_index"]
    if declared_anchor is None:
        record(
            "idle_mib",
            False,
            "ancre non lisible dans le field_map",
            idle,
            "provenance.field_map.idle_mib ne nomme aucun indice lisible ; "
            "l'organe ne suppose pas d'ancre (fail-closed)",
        )
    elif declared_anchor != expected_anchor:
        record(
            "idle_mib",
            False,
            f"ancre field_map={declared_anchor}",
            idle,
            f"l'ancre que le field_map designe ({declared_anchor}) diverge de "
            f"l'ancre attendue par l'organe ({expected_anchor})",
        )
    else:
        in_range = 0 <= declared_anchor < len(values)
        record(
            "idle_mib",
            in_range and values[declared_anchor] == idle,
            values[declared_anchor] if in_range else "indice hors serie",
            idle,
            f"egalite a l'echantillon d'indice {declared_anchor}, lu dans "
            f"provenance.field_map.idle_mib et recoupe avec l'ancre attendue "
            f"({expected_anchor}) ; serie : min={min(values)} "
            f"mediane={statistics.median(values)}",
        )

    temp_max = max(temps)
    record("temp_max_c", vram.get("temp_max_c") == temp_max, temp_max, vram.get("temp_max_c"),
           f"maximum de temp_gpu_c sur {len(temps)} echantillons")

    util_max = max(utils)
    record("util_max_pct", vram.get("util_max_pct") == util_max, util_max,
           vram.get("util_max_pct"),
           f"maximum de utilisation_gpu sur {len(utils)} echantillons")

    for index, phase in enumerate(vram.get("profil_par_phase_mib", [])):
        lo, hi = window_bounds(phase["fenetre_s"])
        window = [(i, v) for i, (t, v, _, _) in enumerate(series) if lo <= t < hi]
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
            f"max={stat['max']} mediane={stat['median']} mode={stat['mode']} | "
            "verifie la PRESENCE d'un echantillon, pas sa representativite",
        )

    return {"run": key, "trace": cfg["trace"], "bytes": len(raw), "checks": findings}


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
