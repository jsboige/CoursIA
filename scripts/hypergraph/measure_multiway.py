"""Rejouer le protocole multiway ; écrire les observations brutes en JSON."""
import argparse
import json
import math
import platform
import resource
import statistics
import subprocess
from pathlib import Path


def limit_memory() -> None:
    resource.setrlimit(resource.RLIMIT_AS, (512 * 1024 * 1024, 512 * 1024 * 1024))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("binary", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--raw", type=Path, required=True)
    args = parser.parse_args()
    subprocess.run([str(args.binary.resolve()), "--self-test"], check=True, timeout=40, preexec_fn=limit_memory)
    rows = []
    raw = []
    for depth in (16, 24, 32, 40, 48):
        observations = [json.loads(subprocess.check_output([str(args.binary.resolve()), str(depth)], text=True, timeout=40, preexec_fn=limit_memory))
                        for _ in range(5)]
        for index, observation in enumerate(observations, start=1):
            seconds = observation.get("seconds") if isinstance(observation, dict) else None
            if (not isinstance(observation, dict)
                    or observation.get("depth") != depth
                    or observation.get("states") != depth + 1
                    or observation.get("witness") is not True
                    or isinstance(seconds, bool)
                    or not isinstance(seconds, (int, float))
                    or not math.isfinite(seconds) or seconds <= 0):
                raise SystemExit(
                    f"Observation invalide : profondeur {depth}, répétition {index} : {observation!r}"
                )
        raw.extend(observations)
        rows.append({"depth": depth, "states": depth + 1,
                     "median_seconds": statistics.median(x["seconds"] for x in observations),
                     "min_seconds": min(x["seconds"] for x in observations),
                     "max_seconds": max(x["seconds"] for x in observations)})
    xs = [math.log(row["states"]) for row in rows]
    ys = [math.log(row["median_seconds"]) for row in rows]
    xm, ym = statistics.mean(xs), statistics.mean(ys)
    alpha = sum((x-xm)*(y-ym) for x, y in zip(xs, ys)) / sum((x-xm)**2 for x in xs)
    predicted = [ym + alpha * (x-xm) for x in xs]
    r2 = 1 - sum((y-p)**2 for y, p in zip(ys, predicted)) / sum((y-ym)**2 for y in ys)
    report = {"protocol": "MULTIWAY-PROTOCOLE.md", "engine_commit": "44c868bf4622e4542b306846ffdcc47c19d0bba8",
              "platform": platform.platform(), "rows": rows, "alpha": alpha, "r_squared": r2,
              "interpretation": "ajustement descriptif" if r2 >= .95 else "ajustement peu informatif"}
    args.raw.write_text(json.dumps(raw, indent=2) + "\n", encoding="utf-8")
    args.output.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(json.dumps(report, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
