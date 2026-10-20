#!/usr/bin/env python3
"""Construit le corpus aligne (texte, noeud Argumentum) pour le test externe humain (#20222).

Critere 1 de #20222 (tranche C de #17578, EPIC #10355) : l'echantillonneur
``sample_external_eval.py`` consomme un JSONL portant ``text`` et ``node`` ;
ce builder produit ce JSONL en joignant les spans du gold standard MAFALDA
(#20217, verbatim CC-BY-SA) a la table d'alignement mergee (#20315, reprise de
#20028).

Le join n'est PAS mecanique, et il ne pretend pas l'etre : le vocabulaire
d'annotation du dataset MAFALDA (celui des spans du gold standard) differe de
la liste L2 du papier (celle de la table d'alignement, 23 entrees). Trois
classes de correspondance, toutes mesurees et distinguees dans le rapport :

1. **exact** : egalite insensible a la casse entre le label du span et
   ``academic_label`` de la table ;
2. **pont declare** : alias explicite, chaque pont portant sa justification --
   un pont est une decision de subsumption (le label du dataset est un
   sous-type reconnu du L2 du papier), jamais une approximation floue ;
3. **exclu** : sans pont honnete, avec le motif consigne (marqueur ``nothing``
   d'absence de sophisme, artefact ``to clean``, labels sans entree L2).

Les lignes NOT_FOUND de la table (``Appeal to values``, ``Fallacy of logic``)
ne produisent jamais de paire : verdict sans noeud cible.

Le rapport ``join_report.json`` consigne, par label : le nombre de spans, la
classe de correspondance, le pont utilise le cas echeant, et pour les exclus
le motif -- de sorte qu'un coordinateur peut rayer un pont et relancer sans
relire le code. Les effectifs par famille Argumentum y sont totals, y compris
les familles a zero paire source (mesure, pas supposition).

Usage :

    python scripts/fallacy_detection/build_aligned_eval_corpus.py \
        --gold MyIA.AI.Notebooks/GenAI/FallacyDetection/data/academic/MAFALDA/gold_standard_dataset.jsonl \
        --table MyIA.AI.Notebooks/GenAI/FallacyDetection/data/academic/logic_mafalda_to_argumentum.csv \
        --out-dir MyIA.AI.Notebooks/GenAI/FallacyDetection/data/academic/aligned
"""

from __future__ import annotations

import argparse
import csv
import json
import sys
from collections import Counter
from pathlib import Path

# ---------------------------------------------------------------------------
# Ponts declares : label du dataset MAFALDA -> academic_label de la table.
# Chaque pont est une subsumption documentee (sous-type -> L2 du papier), pas
# une ressemblance de surface. Retirer un pont = retirer sa ligne : le rapport
# porte le reste.
# ---------------------------------------------------------------------------
DECLARED_BRIDGES: dict[str, tuple[str, str]] = {
    "ad populum": ("Appeal to popularity", "synonyme standard : ad populum = appel a la popularite (table : Appel a la bande)"),
    "appeal to (false) authority": ("Appeal to authority", "variante typographique du meme concept"),
    "false causality": ("False cause", "synonyme standard"),
    "causal oversimplification": ("Causal fallacy", "sous-type causal : simplification abusive de la cause (L2 papier plus grossiere)"),
    "appeal to anger": ("Appeal to emotion", "sous-type emotionnel du L2 Appeal to emotion"),
    "appeal to positive emotion": ("Appeal to emotion", "sous-type emotionnel du L2 Appeal to emotion"),
    "appeal to pity": ("Appeal to emotion", "sous-type emotionnel du L2 Appeal to emotion"),
    "appeal to ridicule": ("Appeal to emotion", "le ridicule est un appel emotionnel ; le L2 papier n'a pas d'entree dediee"),
    "guilt by association": ("Ad hominem", "sous-type reconnu de l'ad hominem (attaque par association)"),
    "tu quoque": ("Ad hominem", "sous-type reconnu de l'ad hominem (appel a l'hypocrisie)"),
}

# Labels du dataset exclus sans pont, avec motif -- mesure, pas gout.
EXCLUSIONS: dict[str, str] = {
    "nothing": "marqueur d'absence de sophisme (pas une paire evaluable)",
    "to clean": "artefact operationnel du dataset, pas un sophisme",
    "appeal to worse problems": "privation relative : aucune entree L2 honnete dans la table",
    "false dilemma": "aucune entree L2 dans la table (mesure)",
}


def load_table(table_path: Path) -> dict[str, dict]:
    """Charge la table d'alignement ; cle normalisee (minuscules, espaces plies)."""
    rows: dict[str, dict] = {}
    with table_path.open(encoding="utf-8", newline="") as handle:
        for row in csv.DictReader(handle):
            if row["academic_source"] != "MAFALDA-L2":
                continue
            rows[norm(row["academic_label"])] = row
    return rows


def norm(label: str) -> str:
    """Normalisation minimale : casse + espacements -- jamais de traduction."""
    return " ".join(label.lower().split())


def iter_spans(gold_path: Path):
    """Yield (fragment, label) pour chaque span annote du gold standard."""
    with gold_path.open(encoding="utf-8") as handle:
        for lineno, line in enumerate(handle, start=1):
            line = line.strip()
            if not line:
                continue
            record = json.loads(line)
            for start, end, label in record.get("labels", []):
                yield lineno, record["text"][start:end], label


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--gold", required=True, type=Path, help="gold_standard_dataset.jsonl MAFALDA")
    parser.add_argument("--table", required=True, type=Path, help="logic_mafalda_to_argumentum.csv (table mergee)")
    parser.add_argument("--out-dir", required=True, type=Path, help="repertoire de sortie (corpus + rapport)")
    args = parser.parse_args(argv)

    table = load_table(args.table)
    args.out_dir.mkdir(parents=True, exist_ok=True)
    corpus_path = args.out_dir / "aligned_corpus.jsonl"
    report_path = args.out_dir / "join_report.json"

    pairs: list[dict] = []
    label_stats: dict[str, dict] = {}
    excluded: Counter[str] = Counter()

    for lineno, fragment, label in iter_spans(args.gold):
        entry = label_stats.setdefault(label, {"spans": 0, "joined_exact": 0, "joined_bridge": 0,
                                               "excluded": 0, "bridge": None, "reason": None})
        entry["spans"] += 1
        key = norm(label)
        row = table.get(key)
        bridge = None
        if row is None and key in DECLARED_BRIDGES:
            bridge = DECLARED_BRIDGES[key]
            row = table.get(norm(bridge[0]))
        if label in EXCLUSIONS:
            entry["excluded"] += 1
            entry["reason"] = EXCLUSIONS[label]
            excluded[label] += 1
            continue
        if row is None:
            entry["excluded"] += 1
            entry["reason"] = "sans entree L2 ni pont declare"
            excluded[label] += 1
            continue
        if row["verdict"] == "NOT_FOUND":
            entry["excluded"] += 1
            entry["reason"] = f"ligne table NOT_FOUND ({row['best_famille']})"
            excluded[label] += 1
            continue
        node = f"{row['best_famille']}/{row['best_name']}"
        pairs.append({
            "text": fragment,
            "node": node,
            "source_label": label,
            "match": "bridge:" + bridge[0] if bridge else "exact",
            "gold_line": lineno,
        })
        if bridge:
            entry["joined_bridge"] += 1
            entry["bridge"] = {"to": bridge[0], "rationale": bridge[1]}
        else:
            entry["joined_exact"] += 1

    with corpus_path.open("w", encoding="utf-8") as handle:
        for pair in pairs:
            handle.write(json.dumps(pair, ensure_ascii=False) + "\n")

    family_counts = Counter(p["node"].split("/")[0] for p in pairs)
    # Familles de la table absentes du corpus source : mesurees a zero, pas omises.
    for row in table.values():
        fam = row["best_famille"]
        family_counts.setdefault(fam, 0)

    report = {
        "issue": 20222,
        "gold": str(args.gold),
        "table": str(args.table),
        "pairs_total": len(pairs),
        "joined_exact": sum(1 for p in pairs if p["match"] == "exact"),
        "joined_bridge": sum(1 for p in pairs if p["match"].startswith("bridge:")),
        "excluded_total": sum(excluded.values()),
        "excluded_by_label": dict(sorted(excluded.items())),
        "label_stats": {k: label_stats[k] for k in sorted(label_stats)},
        "family_counts": dict(sorted(family_counts.items())),
        "note": "Ponts declares = subsumptions documentees (DECLARED_BRIDGES) ; rayer un pont et relancer retire ses paires sans toucher au reste.",
    }
    report_path.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")

    print(f"Corpus aligne : {len(pairs)} paires ({report['joined_exact']} exactes, {report['joined_bridge']} par pont declare, {report['excluded_total']} exclues)")
    print(f"Familles : " + ", ".join(f"{f}={n}" for f, n in sorted(family_counts.items())))
    print(f"Corpus  : {corpus_path}")
    print(f"Rapport : {report_path}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
