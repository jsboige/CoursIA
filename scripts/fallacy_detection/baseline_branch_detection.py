#!/usr/bin/env python3
"""Baselines de la Phase 3 (gate de #17578, EPIC #10355) sur le corpus enseignant.

Le gate de la Phase 3 exige une macro-F1 superieure a « la baseline majoritaire et a
une baseline a regles ». Aucune des deux n'existait dans le depot : cet instrument les
mesure, et il mesure surtout **a quel niveau elles sont mesurables**.

Trois decisions portent l'instrument, chacune falsifiable :

1. **Le niveau se mesure ou il se refuse.** Une macro-F1 par etiquette sur un seul
   exemple par etiquette ne mesure pas le corpus, elle mesure le tirage. L'outil
   verifie le support de chaque etiquette et **refuse** le niveau demande en nommant
   le deficit (nombre d'etiquettes, support maximal, plancher exige) au lieu de rendre
   un chiffre qui aurait l'air d'un resultat.

2. **Les plis sont groupes par scenario.** Les paires du corpus partagent leurs
   scenarios (un scenario porte plusieurs paires). Un decoupage naif met le meme
   scenario des deux cotes de la barriere : le modele apprend la formulation du
   scenario, pas la famille, et le chiffre publie est gonfle. Les plis groupes
   interdisent ce recouvrement.

3. **La fuite est mesuree, pas supposee.** Le meme modele est evalue deux fois, plis
   groupes et plis naifs ; l'ecart est rapporte comme une grandeur du rapport. Un ecart
   nul dit qu'il n'y avait rien a fuir ; un ecart large dit ce que le chiffre naif
   devait a la fuite.

Le modele lexical est un TF-IDF (uni- et bigrammes de mots) suivi d'un plus proche
centroide, en bibliotheque standard : la place du corpus (280 documents, ~48 mots)
rend l'implementation directe, et le depot ne declare aucune dependance scientifique
pour `scripts/`. L'implementation a ete contre-verifiee contre `sklearn`
(`TfidfVectorizer` + `NearestCentroid`) ; le resultat de cette contre-verification est
rapporte dans la PR, il n'est pas rejoue ici (pas de dependance ajoutee au depot).

Usage::

    python scripts/fallacy_detection/baseline_branch_detection.py \
        --corpus MyIA.AI.Notebooks/GenAI/FallacyDetection/data/teacher/val_fr.jsonl \
        --out-dir MyIA.AI.Notebooks/GenAI/FallacyDetection/data/teacher \
        --level branch --folds 5 --random-draws 200 --seed 42
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import random
import re
import sys
from collections import Counter
from pathlib import Path

TOKEN_RE = re.compile(r"[0-9a-zà-öø-ÿ]+")

#: Champs du corpus enseignant, par niveau de mesure.
LEVEL_FIELDS = {"branch": "family", "node": "node_key"}

#: Support minimal par etiquette : en dessous, la macro-F1 mesure le tirage.
MIN_EXAMPLES_PER_LABEL = 2


def sha256_of(path: Path) -> str:
    """Empreinte SHA-256 d'un fichier, lue par blocs."""
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def tokenize(text: str) -> list[str]:
    """Jetons en minuscules : lettres accentuees et chiffres."""
    return TOKEN_RE.findall(text.lower())


def load_corpus(path: Path, level: str) -> list[dict]:
    """Charge le corpus ; echoue (fail-closed) sur toute ligne inexploitable."""
    if level not in LEVEL_FIELDS:
        raise SystemExit(f"Niveau inconnu '{level}' : attendu {sorted(LEVEL_FIELDS)}.")
    label_field = LEVEL_FIELDS[level]
    if not path.exists():
        raise SystemExit(f"Corpus introuvable : {path}")
    items: list[dict] = []
    with path.open(encoding="utf-8") as handle:
        for lineno, line in enumerate(handle, start=1):
            line = line.strip()
            if not line:
                continue
            record = json.loads(line)
            missing = [f for f in ("text", label_field, "scenario_path") if f not in record]
            if missing:
                raise SystemExit(f"Ligne {lineno} de {path} : champs manquants {missing}.")
            if not str(record["text"]).strip():
                raise SystemExit(f"Ligne {lineno} : texte vide.")
            items.append({
                "text": str(record["text"]),
                "label": str(record[label_field]),
                "group": str(record["scenario_path"]),
            })
    if not items:
        raise SystemExit(f"{path} : aucun enregistrement charge.")
    return items


def require_measurable(support: Counter, level: str, floor: int = MIN_EXAMPLES_PER_LABEL) -> None:
    """Refuse un niveau dont le support par etiquette est trop faible pour une macro-F1."""
    deficits = {label: n for label, n in support.items() if n < floor}
    if not deficits:
        return
    worst = max(support.values())
    raise SystemExit(
        f"Niveau '{level}' non mesurable sur ce corpus : {len(support)} etiquettes, "
        f"support maximal {worst}, plancher exige {floor}. Une macro-F1 par etiquette "
        "calculee sur un seul exemple mesure le tirage, pas le corpus. "
        "Fournir un corpus ou chaque etiquette porte au moins "
        f"{floor} paires, ou mesurer un niveau plus large."
    )


def grouped_folds(items: list[dict], n_folds: int) -> list[list[int]]:
    """Plis groupes par scenario, equilibres en taille, sans aucun alea.

    Un scenario entier tombe dans un seul pli : aucune paire d'un scenario de test
    n'a de soeur dans l'entrainement. L'affectation est deterministe (groupes tries
    par taille decroissante puis par nom, chacun au pli le plus leger), pour qu'un
    meme corpus rende toujours les memes plis.
    """
    if n_folds < 2:
        raise SystemExit(f"Nombre de plis invalide : {n_folds} (minimum 2).")
    by_group: dict[str, list[int]] = {}
    for index, item in enumerate(items):
        by_group.setdefault(item["group"], []).append(index)
    loads = [0] * n_folds
    folds: list[list[int]] = [[] for _ in range(n_folds)]
    for group in sorted(by_group, key=lambda g: (-len(by_group[g]), g)):
        target = min(range(n_folds), key=lambda k: (loads[k], k))
        folds[target].extend(by_group[group])
        loads[target] += len(by_group[group])
    for fold in folds:
        fold.sort()
    return folds


def stratified_folds(items: list[dict], n_folds: int) -> list[list[int]]:
    """Plis naifs : stratifies par etiquette, **sans** egard au scenario.

    C'est le decoupage qu'on ecrit par reflexe, et c'est celui qui fuit : deux paires
    d'un meme scenario se retrouvent de part et d'autre de la barriere. Il n'est pas
    la pour etre utilise comme protocole, mais pour etre l'**objet** de la mesure.
    """
    if n_folds < 2:
        raise SystemExit(f"Nombre de plis invalide : {n_folds} (minimum 2).")
    by_label: dict[str, list[int]] = {}
    for index, item in enumerate(items):
        by_label.setdefault(item["label"], []).append(index)
    folds: list[list[int]] = [[] for _ in range(n_folds)]
    for label in sorted(by_label):
        for position, index in enumerate(by_label[label]):
            folds[position % n_folds].append(index)
    for fold in folds:
        fold.sort()
    return folds


def macro_f1(y_true: list[str], y_pred: list[str]) -> tuple[float, dict[str, float]]:
    """Macro-F1 sur l'union des etiquettes vues -- une etiquette inventee dilue la moyenne."""
    labels = sorted(set(y_true) | set(y_pred))
    if not labels:
        raise SystemExit("macro_f1 : aucun label a evaluer.")
    pairs = list(zip(y_true, y_pred))
    per_label: dict[str, float] = {}
    for label in labels:
        tp = sum(1 for t, p in pairs if t == label and p == label)
        fp = sum(1 for t, p in pairs if t != label and p == label)
        fn = sum(1 for t, p in pairs if t == label and p != label)
        precision = tp / (tp + fp) if tp + fp else 0.0
        recall = tp / (tp + fn) if tp + fn else 0.0
        per_label[label] = 2 * precision * recall / (precision + recall) if precision + recall else 0.0
    return sum(per_label.values()) / len(per_label), per_label


class TfidfCentroids:
    """TF-IDF (uni- et bigrammes) + plus proche centroide, en bibliotheque standard.

    Conventions de ponderation alignees sur `sklearn` : tf brut,
    `idf = ln((1+n)/(1+df)) + 1`, vecteurs normalises L2, centroide = moyenne des
    vecteurs normalises de la classe.

    **La regle d'affectation, elle, differe de `NearestCentroid`** : ici le plus grand
    produit scalaire avec le centroide ; `NearestCentroid` minimise la distance
    euclidienne, dont le terme `||c||^2` varie d'une classe a l'autre et favorise donc
    les classes au centroide proche de l'origine. Les deux regles ne coincident pas.
    Mesure sur le corpus enseignant, memes plis groupes : 0,2197 ici, 0,2062 avec
    `TfidfVectorizer` + `NearestCentroid` (ecart 0,0135, inferieur a l'ecart-type
    inter-plis de 0,042) -- accord dans le bruit, pas identite.
    """

    def __init__(self) -> None:
        self.vocabulary: dict[str, int] = {}
        self.idf: list[float] = []
        self.n_documents = 0

    @staticmethod
    def features(tokens: list[str]) -> list[str]:
        bigrams = [f"{a} {b}" for a, b in zip(tokens, tokens[1:])]
        return tokens + bigrams

    def fit(self, texts: list[str]) -> "TfidfCentroids":
        document_frequency: Counter = Counter()
        for text in texts:
            document_frequency.update(set(self.features(tokenize(text))))
        self.n_documents = len(texts)
        self.vocabulary = {term: i for i, term in enumerate(sorted(document_frequency))}
        self.idf = [0.0] * len(self.vocabulary)
        for term, index in self.vocabulary.items():
            self.idf[index] = math.log((1 + self.n_documents) / (1 + document_frequency[term])) + 1.0
        return self

    def transform(self, text: str) -> dict[int, float]:
        counts = Counter(self.vocabulary[t] for t in self.features(tokenize(text)) if t in self.vocabulary)
        if not counts:
            return {}
        weights = {i: count * self.idf[i] for i, count in counts.items()}
        norm = math.sqrt(sum(w * w for w in weights.values()))
        return {i: w / norm for i, w in weights.items()} if norm else {}

    def centroids(self, items: list[dict]) -> dict[str, dict[int, float]]:
        accumulators: dict[str, dict[int, float]] = {}
        counts: Counter = Counter()
        for item in items:
            vector = self.transform(item["text"])
            accumulator = accumulators.setdefault(item["label"], {})
            for index, weight in vector.items():
                accumulator[index] = accumulator.get(index, 0.0) + weight
            counts[item["label"]] += 1
        return {
            label: {i: w / counts[label] for i, w in accumulator.items()}
            for label, accumulator in accumulators.items()
        }

    @staticmethod
    def predict(vector: dict[int, float], centroids: dict[str, dict[int, float]]) -> str:
        best_label, best_score = None, None
        for label in sorted(centroids):
            score = sum(weight * centroids[label].get(i, 0.0) for i, weight in vector.items())
            if best_score is None or score > best_score:
                best_label, best_score = label, score
        if best_label is None:
            raise SystemExit("Aucun centroide : entrainement vide.")
        return best_label


def evaluate(predict, items: list[dict], folds: list[list[int]]) -> dict:
    """Evalue un predicat sur des plis donnes ; le rapport porte la couverture des etiquettes."""
    labelled = sorted(set(item["label"] for item in items))
    per_fold = []
    for number, test_indices in enumerate(folds):
        if not test_indices:
            per_fold.append({"fold": number, "n_test": 0, "macro_f1": None,
                             "labels_in_test": 0, "labels_unseen_in_train": None})
            continue
        test_set = set(test_indices)
        test_items = [items[i] for i in test_indices]
        train_items = [item for i, item in enumerate(items) if i not in test_set]
        predictions = predict(train_items, test_items, number)
        score, per_label = macro_f1([item["label"] for item in test_items], predictions)
        train_labels = set(item["label"] for item in train_items)
        unseen = sorted(set(item["label"] for item in test_items) - train_labels)
        per_fold.append({
            "fold": number,
            "n_test": len(test_items),
            "macro_f1": round(score, 4),
            "labels_in_test": len(set(item["label"] for item in test_items)),
            "labels_unseen_in_train": len(unseen),
            "worst_labels": sorted(per_label, key=lambda l: (per_label[l], l))[:3],
        })
    scored = [f["macro_f1"] for f in per_fold if f["macro_f1"] is not None]
    mean = sum(scored) / len(scored) if scored else None
    spread = None
    if len(scored) > 1:
        spread = math.sqrt(sum((s - mean) ** 2 for s in scored) / (len(scored) - 1))
    return {
        "folds": per_fold,
        "labels_total": len(labelled),
        "macro_f1_mean": round(mean, 4) if mean is not None else None,
        "macro_f1_std": round(spread, 4) if spread is not None else None,
    }


def predictor_majority(train_items: list[dict], test_items: list[dict], _fold: int) -> list[str]:
    """Baseline majoritaire : l'etiquette la plus frequente de l'entrainement (ex aequo : ordre alphabetique)."""
    counts = Counter(item["label"] for item in train_items)
    if not counts:
        raise SystemExit("Baseline majoritaire : entrainement vide.")
    label = sorted(counts.items(), key=lambda kv: (-kv[1], kv[0]))[0][0]
    return [label] * len(test_items)


def predictor_random(seed: int, draws: int, draw: int):
    """Baseline aleatoire : tirage uniforme sur les etiquettes vues a l'entrainement."""
    def predict(train_items: list[dict], test_items: list[dict], fold: int) -> list[str]:
        labels = sorted(set(item["label"] for item in train_items))
        if not labels:
            raise SystemExit("Baseline aleatoire : entrainement vide.")
        # Graine textuelle : `random.Random` n'accepte pas de tuple, et une graine
        # derivee de (graine, tirage, pli) garde la reproductibilite par pli.
        rng = random.Random(f"{seed}:{draw}:{fold}")
        return [labels[rng.randrange(len(labels))] for _ in test_items]
    return predict


def predictor_lexical(train_items: list[dict], test_items: list[dict], _fold: int) -> list[str]:
    """Baseline lexicale : TF-IDF + plus proche centroide, entraine sur le seul pli d'entrainement."""
    space = TfidfCentroids().fit([item["text"] for item in train_items])
    centroids = space.centroids(train_items)
    return [TfidfCentroids.predict(space.transform(item["text"]), centroids) for item in test_items]


def quantile(sorted_values: list[float], fraction: float) -> float:
    """Quantile par interpolation lineaire (convention `statistics.quantiles`)."""
    if not sorted_values:
        raise SystemExit("quantile : serie vide.")
    position = fraction * (len(sorted_values) - 1)
    low = math.floor(position)
    high = math.ceil(position)
    if low == high:
        return sorted_values[low]
    return sorted_values[low] + (sorted_values[high] - sorted_values[low]) * (position - low)


def run(corpus_path: Path, level: str, folds_count: int, random_draws: int, seed: int) -> dict:
    """Mesure complete : structure, plis, baselines, et l'ecart de fuite."""
    items = load_corpus(corpus_path, level)
    support = Counter(item["label"] for item in items)
    groups = Counter(item["group"] for item in items)
    structure = {
        "rows": len(items),
        "labels": len(support),
        "support_min": min(support.values()),
        "support_max": max(support.values()),
        "groups": len(groups),
        "group_max_reuse": max(groups.values()),
    }
    # Le niveau nœud se mesure sur le corpus reel : il est refuse ici, nommement.
    node_support = None
    if level == "branch":
        with corpus_path.open(encoding="utf-8") as handle:
            node_keys = [json.loads(line)["node_key"] for line in handle if line.strip()]
        node_support = Counter(node_keys)
        structure["node_labels"] = len(node_support)
        structure["node_support_max"] = max(node_support.values())

    require_measurable(support, level)

    grouped = grouped_folds(items, folds_count)
    naive = stratified_folds(items, folds_count)
    overlap = sum(1 for a, b in zip(grouped, naive) if sorted(a) == sorted(b))

    results = {
        "majority_grouped": evaluate(predictor_majority, items, grouped),
        "lexical_centroid_grouped": evaluate(predictor_lexical, items, grouped),
        "lexical_centroid_naive": evaluate(predictor_lexical, items, naive),
    }

    draw_scores = []
    for draw in range(random_draws):
        scores = [f["macro_f1"] for f in evaluate(predictor_random(seed, random_draws, draw), items, grouped)["folds"]
                  if f["macro_f1"] is not None]
        if scores:
            draw_scores.append(sum(scores) / len(scores))
    draw_scores.sort()
    results["random_grouped"] = {
        "draws": random_draws,
        "macro_f1_mean": round(sum(draw_scores) / len(draw_scores), 4) if draw_scores else None,
        "macro_f1_p2_5": round(quantile(draw_scores, 0.025), 4) if draw_scores else None,
        "macro_f1_p97_5": round(quantile(draw_scores, 0.975), 4) if draw_scores else None,
    }

    grouped_mean = results["lexical_centroid_grouped"]["macro_f1_mean"]
    naive_mean = results["lexical_centroid_naive"]["macro_f1_mean"]
    return {
        "issue": "Phase 3 gate (tranche de #17578, EPIC #10355)",
        "corpus": {"path": str(corpus_path).replace("\\", "/"), "sha256": sha256_of(corpus_path)},
        "level": level,
        "seed": seed,
        "folds": folds_count,
        "structure": structure,
        "node_level": {
            "measurable": node_support is not None and min(node_support.values()) >= MIN_EXAMPLES_PER_LABEL,
            "labels": len(node_support) if node_support else None,
            "support_max": max(node_support.values()) if node_support else None,
            "floor": MIN_EXAMPLES_PER_LABEL,
        },
        "folds_identical": overlap,
        "baselines": results,
        "leakage": {
            "grouped_mean": grouped_mean,
            "naive_mean": naive_mean,
            "gap": round(naive_mean - grouped_mean, 4) if None not in (naive_mean, grouped_mean) else None,
        },
    }


def render_report(report: dict) -> str:
    """Table markdown du rapport de baselines."""
    structure = report["structure"]
    lines = [
        "# Baselines de la Phase 3 — niveau « branche »",
        "",
        f"Corpus : `{report['corpus']['path']}` (SHA-256 `{report['corpus']['sha256'][:12]}`), "
        f"{structure['rows']} paires, {structure['labels']} etiquettes, "
        f"{structure['groups']} scenarios (le plus reemploye {structure['group_max_reuse']} fois).",
        "",
        "| Baseline | Protocole | Macro-F1 moyenne | Ecart-type |",
        "|---|---|---:|---:|",
    ]
    labels = {
        "majority_grouped": "Majoritaire",
        "random_grouped": "Aleatoire (uniforme sur l'entrainement)",
        "lexical_centroid_grouped": "Lexicale (TF-IDF + centroide)",
        "lexical_centroid_naive": "Lexicale, plis naifs (controle de fuite)",
    }
    order = ["majority_grouped", "random_grouped", "lexical_centroid_grouped", "lexical_centroid_naive"]
    for key in order:
        block = report["baselines"][key]
        protocol = "plis groupes par scenario" if "naive" not in key else "plis stratifies, sans groupes"
        mean = block["macro_f1_mean"]
        std = block.get("macro_f1_std")
        if std is None and block.get("macro_f1_p2_5") is not None:
            std = f"IC 95 % [{block['macro_f1_p2_5']} ; {block['macro_f1_p97_5']}]"
        lines.append(f"| {labels[key]} | {protocol} | {mean} | {std if std is not None else '—'} |")
    leak = report["leakage"]
    lines += [
        "",
        f"**Ecart de fuite mesure** : {leak['naive_mean']} (plis naifs) − {leak['grouped_mean']} "
        f"(plis groupes) = **{leak['gap']}** de macro-F1 attribuables au recouvrement de scenario.",
        "",
        f"Niveau « nœud » : **{structure.get('node_labels')} etiquettes pour "
        f"{structure['rows']} paires** (support maximal {structure.get('node_support_max')}) — "
        f"sous le plancher de {report['node_level']['floor']} par etiquette, donc "
        "**non mesurable** sur ce corpus. Le gate de Phase 3 exige une exactitude a la "
        "feuille exacte : elle demande un corpus ou chaque nœud porte plusieurs paires.",
        "",
    ]
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--corpus", required=True, type=Path, help="JSONL du corpus enseignant")
    parser.add_argument("--out-dir", required=True, type=Path, help="repertoire de sortie")
    parser.add_argument("--level", default="branch", choices=sorted(LEVEL_FIELDS))
    parser.add_argument("--folds", type=int, default=5)
    parser.add_argument("--random-draws", type=int, default=200)
    parser.add_argument("--seed", type=int, default=42)
    args = parser.parse_args(argv)

    report = run(args.corpus, args.level, args.folds, args.random_draws, args.seed)
    args.out_dir.mkdir(parents=True, exist_ok=True)
    json_path = args.out_dir / f"baselines_{args.level}.json"
    md_path = args.out_dir / f"baselines_{args.level}.md"
    json_path.write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    md_path.write_text(render_report(report), encoding="utf-8")
    print(json.dumps(report, ensure_ascii=False, indent=2))
    print(f"Rapport : {json_path}")
    print(f"Rapport : {md_path}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
