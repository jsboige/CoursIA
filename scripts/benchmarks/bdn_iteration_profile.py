#!/usr/bin/env python3
"""Profil par iteration des journaux BenchmarkDotNet (#25644).

Pourquoi cet outil
------------------
Le rapport final de BDN ne publie qu'une moyenne par cellule. Or, quand le JIT
passe du tier0 au tier1 *pendant* la fenetre mesuree, cette moyenne est un
melange de deux regimes, et la position de la marche varie d'une passe a
l'autre : c'est ce qui a ete mesure sur le banc 1 (section « Controle du banc
1 » de ``docs/dotnet/net11-runtime-deltas.md``, #25641). Le seul artefact qui
rende ce melange visible est le journal d'iterations (``WorkloadActual`` et
``WorkloadResult``), que le rapport final n'imprime pas.

Cet outil extrait cette serie, cherche le point de coupe qui maximise le
rapport des medianes avant/apres, et -- c'est le point methodologique -- le
confronte a un **controle par permutation** : sur une serie sans ordre
temporel, le meilleur point de coupe trouve toujours un rapport superieur a 1.
Un rapport n'est donc publiable comme marche que si l'ordre reel fait mieux
que le hasard. La p-valeur est unilaterale et sa resolution vaut
``1 / (permutations + 1)``.

Usage
-----
    python scripts/benchmarks/bdn_iteration_profile.py \\
        --artifact docs/dotnet/banc4-regime-25644.json \\
        --out-csv docs/dotnet/banc4-regime-25644-profile.csv \\
        --out-md  docs/dotnet/banc4-regime-25644-profile.md

    python scripts/benchmarks/bdn_iteration_profile.py --journal run.log

Ce que l'outil ne dit pas
-------------------------
La non-significativite n'est **pas** l'absence de marche : avec quinze
iterations et une dispersion de 40 a 80 %, la puissance est faible. Un p eleve
dit « rien de detectable dans cette serie », jamais « pas de melange ». De meme,
une marche detectee n'identifie pas sa cause : le tiering est une explication
possible, pas une conclusion de cet outil.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import random
import re
import statistics
import sys
from pathlib import Path
from typing import Iterable, Sequence

ACTUAL_RE = re.compile(
    r"^WorkloadActual\s+(\d+):\s+[\d,]+\s+op,\s+([\d.]+)\s+ns,\s+([\d.]+)\s+(ns|us|ms|s)/op"
)
RESULT_RE = re.compile(
    r"^WorkloadResult\s+(\d+):\s+[\d,]+\s+op,\s+([\d.]+)\s+ns,\s+([\d.]+)\s+(ns|us|ms|s)/op"
)
RUNTIME_RE = re.compile(r"^//\s*Runtime=(.+?)\s*$")

# BDN choisit l'unite par colonne selon l'ordre de grandeur : un cout sous la
# microseconde sort en ns/op, un cout de plusieurs secondes en s/op. Un motif
# qui n accepte que us/op ne rend pas une erreur -- il rend une serie VIDE, et
# la jambe disparait du recensement sans laisser de trace. C est exactement le
# faux negatif silencieux que la campagne a produit sur les douze jambes
# Signature_Matches avant correction.
_UNIT_TO_US = {"ns": 1e-3, "us": 1.0, "ms": 1e3, "s": 1e6}

COLUMNS = [
    "method",
    "runtime",
    "mode",
    "tiering",
    "pass",
    "n",
    "mean_us",
    "median_us",
    "min_us",
    "max_us",
    "step_position",
    "pre_median_us",
    "post_median_us",
    "step_ratio",
    "p_value",
    "pre_share",
]


def parse_series(lines: Iterable[str], kind: str = "actual") -> list[float]:
    """Extrait la serie des couts par iteration (us/op), dans l'ordre du journal.

    ``kind`` vaut ``actual`` (serie brute, avant filtrage BDN) ou ``result``
    (serie retenue par BDN). Le cout par iteration est lu sur la colonne
    ``<unite>/op`` du journal et ramene en microsecondes ; le total en ns sert
    de controle de coherence dans les tests.
    """
    rx = ACTUAL_RE if kind == "actual" else RESULT_RE
    out: list[float] = []
    for line in lines:
        match = rx.match(line.strip())
        if match is not None:
            out.append(float(match.group(3)) * _UNIT_TO_US[match.group(4)])
    return out


def best_step(values: Sequence[float], min_side: int = 3) -> dict | None:
    """Point de coupe qui maximise le rapport mediane(avant) / mediane(apres).

    ``position`` est l'indice du premier point de la partie « apres » : une
    position a 9 signifie que les iterations 1 a 9 forment la partie « avant ».
    Retourne ``None`` si la serie est trop courte pour tenir ``min_side`` points
    de chaque cote.
    """
    n = len(values)
    if n < 2 * min_side:
        return None
    best: dict | None = None
    for position in range(min_side, n - min_side + 1):
        pre = values[:position]
        post = values[position:]
        pre_median = statistics.median(pre)
        post_median = statistics.median(post)
        if post_median <= 0:
            continue
        ratio = pre_median / post_median
        if best is None or ratio > best["ratio"]:
            best = {
                "ratio": ratio,
                "position": position,
                "pre_median": pre_median,
                "post_median": post_median,
                "pre_n": len(pre),
                "post_n": len(post),
            }
    return best


def permutation_pvalue(
    values: Sequence[float],
    observed_ratio: float,
    shuffles: int,
    rng: random.Random,
    min_side: int = 3,
) -> float:
    """p-valeur unilaterale du rapport observe contre l'ordre melange.

    Le melange conserve la distribution marginale et detruit l'ordre temporel :
    il mesure donc « ce que le meilleur point de coupe trouve sans marche ».
    """
    if shuffles < 1:
        raise ValueError("shuffles doit valoir au moins 1")
    buffer = list(values)
    hits = 0
    for _ in range(shuffles):
        rng.shuffle(buffer)
        step = best_step(buffer, min_side)
        if step is not None and step["ratio"] >= observed_ratio:
            hits += 1
    return (hits + 1) / (shuffles + 1)


def profile(
    values: Sequence[float],
    shuffles: int = 500,
    seed: int = 20261115,
    min_side: int = 3,
) -> dict:
    """Profil d'une serie : dispersion, marche la plus marquee, p-valeur.

    ``pre_share`` est la part de la moyenne totale qui disparait si l'on prend
    la mediane de la partie « apres » comme cout etabli :
    ``(moyenne - mediane_apres) / moyenne``. Une valeur positive quantifie
    l'inflation portee par le regime d'avant la marche ; elle peut etre
    negative quand la mediane d'apres depasse la moyenne.
    """
    n = len(values)
    if n == 0:
        raise ValueError("serie vide")
    mean = sum(values) / n
    row: dict = {
        "n": n,
        "mean_us": mean,
        "median_us": statistics.median(values),
        "min_us": min(values),
        "max_us": max(values),
        "step_position": None,
        "pre_median_us": None,
        "post_median_us": None,
        "step_ratio": None,
        "p_value": None,
        "pre_share": None,
    }
    step = best_step(values, min_side)
    if step is None:
        return row
    rng = random.Random(seed)
    row.update(
        step_position=step["position"],
        pre_median_us=step["pre_median"],
        post_median_us=step["post_median"],
        step_ratio=step["ratio"],
        p_value=permutation_pvalue(values, step["ratio"], shuffles, rng, min_side),
        pre_share=(mean - step["post_median"]) / mean,
    )
    return row


def load_artifact(path: str | Path) -> list[dict]:
    """Lit un artefact de campagne : ``runs[]`` avec ``workload`` (journal)."""
    data = json.loads(Path(path).read_text(encoding="utf-8"))
    runs = data.get("runs")
    if not isinstance(runs, list):
        raise ValueError(f"{path} : cle 'runs' absente ou invalide")
    return runs


def sha256_of(path: str | Path) -> str:
    digest = hashlib.sha256()
    with open(path, "rb") as handle:
        for chunk in iter(lambda: handle.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def rows_from_artifact(
    runs: Sequence[dict],
    kind: str,
    shuffles: int,
    seed: int,
    min_side: int,
    filters: dict,
) -> list[dict]:
    """Construit une ligne par jambe, filtres appliques sur les metadonnees."""
    rows: list[dict] = []
    for run in runs:
        meta = {
            "method": run.get("method", ""),
            "runtime": run.get("runtime", ""),
            "mode": run.get("mode", ""),
            "tiering": run.get("tiering", ""),
            "pass": run.get("pass_number", ""),
        }
        if any(meta[key] not in wanted for key, wanted in filters.items()):
            continue
        series = parse_series(run.get("workload") or [], kind=kind)
        if not series:
            continue
        row = dict(meta)
        row.update(profile(series, shuffles=shuffles, seed=seed, min_side=min_side))
        rows.append(row)
    return rows


def _fmt(value, digits: int = 3) -> str:
    if value is None:
        return "-"
    if isinstance(value, float):
        return f"{value:.{digits}f}"
    return str(value)


def sort_rows(rows: Sequence[dict]) -> list[dict]:
    """Les series sans marche exploitable passent en queue ; sinon p puis ratio."""
    return sorted(
        rows,
        key=lambda row: (
            row["p_value"] is None,
            row["p_value"] if row["p_value"] is not None else 1.0,
            -(row["step_ratio"] or 0.0),
        ),
    )


def write_csv(path: str | Path, rows: Sequence[dict]) -> None:
    with open(path, "w", encoding="utf-8", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=COLUMNS)
        writer.writeheader()
        for row in rows:
            writer.writerow({key: row.get(key) for key in COLUMNS})


def summarise(rows: Sequence[dict], shuffles: int, skipped: int | None = None) -> list[str]:
    """Constats mesures, formules pour rester vrais quels que soient les chiffres.

    ``skipped`` est le nombre de jambes presentes dans la source mais sans
    journal exploitable. Il est publie, et pas seulement compte : une jambe peut
    disparaitre parce que son journal porte une unite inattendue (``ns/op``
    plutot que ``us/op``), et un recensement qui tait les disparues se lit comme
    complet.
    """
    total = len(rows)
    no_step = sum(1 for row in rows if row["p_value"] is None)
    significant_5 = sum(1 for row in rows if row["p_value"] is not None and row["p_value"] < 0.05)
    significant_1 = sum(1 for row in rows if row["p_value"] is not None and row["p_value"] < 0.01)
    ratios = [row["step_ratio"] for row in rows if row["step_ratio"] is not None]
    lines = [
        f"- Jambes lues : **{total}** ; series trop courtes pour un point de coupe : **{no_step}**.",
        f"- Marche significative contre l'ordre melange : **{significant_5}** a p < 0,05, "
        f"dont **{significant_1}** a p < 0,01 ({shuffles} permutations par jambe).",
    ]
    if skipped:
        lines.append(
            f"- **{skipped}** jambe(s) de la source n'ont pas de journal exploitable "
            "(serie vide) : elles sont absentes de la table, non mesurees, et ce n'est pas "
            "un resultat -- verifier le format des lignes avant de lire le reste."
        )
    if ratios:
        lines.append(
            f"- Rapport mediane avant / mediane apres, sur les {len(ratios)} jambes mesurables : "
            f"de {min(ratios):.2f} a {max(ratios):.2f}."
        )
    lines.append(
        "- Un p eleve ne prouve pas l'absence de marche : la puissance est faible a quinze "
        "iterations et forte dispersion. Une marche detectee n'identifie pas sa cause."
    )
    return lines


def write_md(
    path: str | Path,
    rows: Sequence[dict],
    title: str,
    source: str,
    source_sha: str,
    shuffles: int,
    seed: int,
    min_side: int,
    kind: str,
    skipped: int | None = None,
) -> None:
    ordered = sort_rows(rows)
    parts: list[str] = []
    parts.append(f"# {title}\n")
    parts.append(
        "Genere par `scripts/benchmarks/bdn_iteration_profile.py` depuis "
        f"`{source}` (SHA-256 `{source_sha}`), lignes `Workload"
        f"{'Actual' if kind == 'actual' else 'Result'}`.\n"
    )
    parts.append(
        f"Controle : {shuffles} permutations par jambe, graine {seed}, "
        f"au moins {min_side} iterations de chaque cote du point de coupe. "
        "Le rapport publie est celui des medianes ; la p-valeur est unilaterale "
        f"et sa resolution vaut 1/{shuffles + 1}.\n"
    )
    parts.append("## Synthese\n")
    parts.extend(summarise(rows, shuffles, skipped))
    parts.append("")
    parts.append("## Ce que chaque colonne dit\n")
    parts.append(
        "- **position** : nombre d'iterations dans la partie « avant ». Une position a 9 "
        "signifie que les iterations 1 a 9 precedent la marche.\n"
        "- **ratio** : mediane(avant) / mediane(apres), sans arrondi favorable.\n"
        "- **part** : `(moyenne - mediane apres) / moyenne`, c'est-a-dire la part de la "
        "moyenne totale portee par le regime d'avant la marche. Negative quand la mediane "
        "d'apres depasse la moyenne.\n"
        "- **p** : p-valeur du rapport contre l'ordre melange. Seules les lignes a p < 0,05 "
        "portent une marche distinguable du hasard.\n"
    )
    parts.append("## Table\n")
    parts.append(
        "| Methode | Runtime | Regime | Tiering | Passe | n | moyenne (us/op) | position | "
        "ratio | p | part |"
    )
    parts.append("|---|---|---|---|---:|---:|---:|---:|---:|---:|---:|")
    for row in ordered:
        parts.append(
            "| `{method}` | {runtime} | {mode} | {tiering} | {pass} | {n} | {mean} | "
            "{position} | {ratio} | {p} | {share} |".format(
                method=row["method"],
                runtime=row["runtime"],
                mode=row["mode"],
                tiering=row["tiering"],
                **{"pass": row["pass"]},
                n=row["n"],
                mean=_fmt(row["mean_us"]),
                position=_fmt(row["step_position"]),
                ratio=_fmt(row["step_ratio"], 2),
                p=_fmt(row["p_value"]),
                share=_fmt(row["pre_share"]),
            )
        )
    parts.append("")
    Path(path).write_text("\n".join(parts), encoding="utf-8", newline="")


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        description="Profil par iteration d'un journal BenchmarkDotNet (#25644).",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    source = parser.add_mutually_exclusive_group(required=True)
    source.add_argument("--artifact", help="Artefact de campagne JSON (cle runs[].workload).")
    source.add_argument("--journal", help="Journal BDN brut (une seule jambe).")
    parser.add_argument("--kind", choices=("actual", "result"), default="actual")
    parser.add_argument("--shuffles", type=int, default=500)
    parser.add_argument("--seed", type=int, default=20261115)
    parser.add_argument("--min-side", type=int, default=3)
    parser.add_argument("--out-csv")
    parser.add_argument("--out-md")
    parser.add_argument("--title", default="Profil par iteration — campagne BDN")
    parser.add_argument("--method", action="append", default=[])
    parser.add_argument("--runtime", action="append", default=[])
    parser.add_argument("--mode", action="append", default=[])
    parser.add_argument("--tiering", action="append", default=[])
    parser.add_argument("--pass-number", action="append", default=[], type=int)
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    filters = {
        "method": set(args.method),
        "runtime": set(args.runtime),
        "mode": set(args.mode),
        "tiering": set(args.tiering),
        "pass": set(args.pass_number),
    }
    filters = {key: value for key, value in filters.items() if value}

    if args.artifact:
        runs = load_artifact(args.artifact)
        rows = rows_from_artifact(
            runs, args.kind, args.shuffles, args.seed, args.min_side, filters
        )
        source = args.artifact
        source_sha = sha256_of(args.artifact)
        skipped = len(runs) - len(rows)
    else:
        text = Path(args.journal).read_text(encoding="utf-8", errors="replace")
        series = parse_series(text.splitlines(), kind=args.kind)
        if not series:
            print(
                f"aucune ligne Workload{'Actual' if args.kind == 'actual' else 'Result'} "
                f"dans {args.journal}",
                file=sys.stderr,
            )
            return 2
        row = {"method": Path(args.journal).name, "runtime": "", "mode": "", "tiering": "", "pass": ""}
        row.update(profile(series, shuffles=args.shuffles, seed=args.seed, min_side=args.min_side))
        rows = [row]
        source = args.journal
        source_sha = sha256_of(args.journal)
        skipped = 0

    if not rows:
        print("aucune jambe ne correspond aux filtres", file=sys.stderr)
        return 2

    if args.out_csv:
        write_csv(args.out_csv, sort_rows(rows))
    if args.out_md:
        write_md(
            args.out_md,
            rows,
            args.title,
            source,
            source_sha,
            args.shuffles,
            args.seed,
            args.min_side,
            args.kind,
            skipped,
        )

    for line in summarise(rows, args.shuffles, skipped):
        print(line.lstrip("- "))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())