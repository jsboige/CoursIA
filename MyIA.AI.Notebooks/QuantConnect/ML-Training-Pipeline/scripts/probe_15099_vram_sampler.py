"""Echantillonneur VRAM pour les runs GPU du harnais ML-Training-Pipeline.

Le harnais `probe_15099_dapo_grpo.py` produit des artefacts JSON (rewards,
durees, compteurs), mais **rien** sur la consommation memoire du GPU : un pic
VRAM annonce sans serie brute n'est pas re-derivable, et les comptes, cadences
et durees de phase finissent par se contredire (constat sur la PR #21624).

Cet instrument comble ce manque : il echantillonne `nvidia-smi` a cadence fixe
et ecrit **une ligne JSON par echantillon** (horodatage, MiB utilises,
utilisation %, temperature) dans un fichier `.jsonl`, accompagne d'un sidecar
`.meta.json` qui porte la cadence **declaree**, la cadence **observee**, la
carte et la version de `nvidia-smi`.

La serie brute est la source de verite ; les agregats (pic, moyenne, fenetre
haute memoire) se **derivent** du `.jsonl` et ne sont jamais saisis a la main.

Usage :

    python scripts/probe_15099_vram_sampler.py --out C:/dev/probe15099_runs/vram.jsonl
    python scripts/probe_15099_vram_sampler.py --out ... --interval 1.0 --duration 1800
    python scripts/probe_15099_vram_sampler.py --out ... --stop-file C:/dev/STOP

L'arret propre se fait soit par `--duration`, soit par la creation du fichier
`--stop-file`, soit par Ctrl-C : dans les trois cas la serie deja ecrite est
conservee et le sidecar est complete.
"""

from __future__ import annotations

import argparse
import json
import os
import statistics
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

# Les colonnes interrogees par nvidia-smi, dans l'ordre attendu par _read_sample.
_QUERY_FIELDS = "timestamp,memory.used,utilization.gpu,temperature.gpu"


def _utc_now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="milliseconds")


def _read_sample(gpu_index: int) -> dict[str, Any] | None:
    """Lit un echantillon nvidia-smi. Retourne None si la carte est absente."""
    cmd = [
        "nvidia-smi",
        f"--query-gpu={_QUERY_FIELDS}",
        "--format=csv,noheader,nounits",
        "-i",
        str(gpu_index),
    ]
    try:
        out = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=20,
            check=False,
        )
    except (OSError, subprocess.SubprocessError):
        return None
    if out.returncode != 0:
        return None
    line = out.stdout.strip().splitlines()[0] if out.stdout.strip() else ""
    parts = [p.strip() for p in line.split(",")]
    if len(parts) != 4:
        return None
    try:
        return {
            "nvidia_timestamp": parts[0],
            "mem_used_MiB": int(float(parts[1])),
            "util_pct": int(float(parts[2])),
            "temp_C": int(float(parts[3])),
        }
    except ValueError:
        return None


def _gpu_description(gpu_index: int) -> dict[str, Any]:
    """Nom de la carte, version de nvidia-smi et VRAM totale."""
    desc: dict[str, Any] = {"index": gpu_index}
    try:
        name = subprocess.run(
            ["nvidia-smi", f"--query-gpu=name,memory.total", "--format=csv,noheader", "-i", str(gpu_index)],
            capture_output=True,
            text=True,
            timeout=20,
            check=False,
        )
        if name.returncode == 0 and name.stdout.strip():
            parts = [p.strip() for p in name.stdout.strip().splitlines()[0].split(",")]
            desc["name"] = parts[0]
            desc["memory_total_MiB"] = parts[1]
    except (OSError, subprocess.SubprocessError):
        pass
    try:
        ver = subprocess.run(
            ["nvidia-smi", "--version"], capture_output=True, text=True, timeout=20, check=False
        )
        if ver.returncode == 0 and ver.stdout.strip():
            desc["nvidia_smi_version"] = ver.stdout.strip().splitlines()[0]
    except (OSError, subprocess.SubprocessError):
        pass
    return desc


def _derive_aggregates(samples: list[dict[str, Any]]) -> dict[str, Any]:
    """Agregats DERIVES de la serie brute -- jamais saisis a la main."""
    if not samples:
        return {}
    mem = [s["mem_used_MiB"] for s in samples]
    temps = [s["temp_C"] for s in samples]
    utils = [s["util_pct"] for s in samples]
    elapsed = [s["elapsed_s"] for s in samples]
    gaps = [round(b - a, 3) for a, b in zip(elapsed, elapsed[1:])]
    return {
        "n_samples": len(samples),
        "peak_mem_MiB": max(mem),
        "mean_mem_MiB": round(statistics.fmean(mem), 1),
        "min_mem_MiB": min(mem),
        "peak_util_pct": max(utils),
        "peak_temp_C": max(temps),
        "span_s": round(elapsed[-1] - elapsed[0], 3),
        "observed_interval_s": {
            "min": min(gaps) if gaps else None,
            "median": round(statistics.median(gaps), 3) if gaps else None,
            "max": max(gaps) if gaps else None,
        },
    }


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--out", required=True, help="chemin du fichier .jsonl a ecrire")
    ap.add_argument("--interval", type=float, default=1.0, help="cadence declaree, en secondes")
    ap.add_argument("--duration", type=float, default=0.0, help="duree max en s (0 = illimitee)")
    ap.add_argument("--stop-file", default="", help="fichier dont l'arret termine le sampling")
    ap.add_argument("--gpu", type=int, default=0, help="index de la carte")
    args = ap.parse_args()

    if args.interval <= 0:
        print("ERREUR : --interval doit etre > 0", file=sys.stderr)
        return 2

    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    meta_path = out_path.with_suffix(".meta.json")
    stop_path = Path(args.stop_file) if args.stop_file else None

    meta: dict[str, Any] = {
        "instrument": "probe_15099_vram_sampler.py",
        "declared_interval_s": args.interval,
        "gpu": _gpu_description(args.gpu),
        "started_at": _utc_now_iso(),
        "stop_reason": "",
        "host": os.environ.get("COMPUTERNAME") or os.uname().nodename,
    }

    samples: list[dict[str, Any]] = []
    t0 = time.monotonic()
    next_due = t0
    try:
        with out_path.open("w", encoding="utf-8", newline="\n") as fh:
            while True:
                now = time.monotonic()
                if args.duration > 0 and (now - t0) >= args.duration:
                    meta["stop_reason"] = "duration"
                    break
                if stop_path is not None and stop_path.exists():
                    meta["stop_reason"] = "stop-file"
                    break
                sample = _read_sample(args.gpu)
                if sample is not None:
                    record = {
                        "t": _utc_now_iso(),
                        "elapsed_s": round(now - t0, 3),
                        **sample,
                    }
                    fh.write(json.dumps(record, ensure_ascii=False) + "\n")
                    fh.flush()
                    samples.append(record)
                next_due += args.interval
                sleep_for = next_due - time.monotonic()
                if sleep_for > 0:
                    time.sleep(sleep_for)
                else:
                    # echantillonnage en retard : on repart de maintenant plutot que d'accumuler
                    next_due = time.monotonic()
    except KeyboardInterrupt:
        meta["stop_reason"] = "interrupted"
    finally:
        meta["stopped_at"] = _utc_now_iso()
        meta["aggregates_derived"] = _derive_aggregates(samples)
        meta_path.write_text(json.dumps(meta, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")

    agg = meta["aggregates_derived"]
    print(f"sampler: {agg.get('n_samples', 0)} echantillons -> {out_path}")
    print(
        "derive: pic={peak} Mio moyenne={mean} Mio cadence observee mediane={cad} s ({reason})".format(
            peak=agg.get("peak_mem_MiB"),
            mean=agg.get("mean_mem_MiB"),
            cad=agg.get("observed_interval_s", {}).get("median"),
            reason=meta["stop_reason"] or "inconnu",
        )
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
