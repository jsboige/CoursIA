#!/usr/bin/env python3
"""Mesure du test externe humain : alpha de Krippendorff, IC de Wilson, desaccords.

Grain 2 de #20222 (tranche C de #17578, grand-mere #10355). Le grain 1 a livre
l'**echantillonneur** (``sample_external_eval.py``) : il produit une feuille
aveugle pour les evaluateurs et une cle de correction. Ce grain livre
l'**instrument de mesure** : il transforme des feuilles remplies en les chiffres
du tableau 4 du protocole (``data/external_eval/PROTOCOL.md``).

Ce que l'outil mesure, et pourquoi ces trois mesures precisement :

1. **Accord inter-evaluateurs (alpha de Krippendorff, metrique nominale)** aux
   deux niveaux du protocole -- noeud exact et branche de premier niveau. L'alpha
   est retenu plutot qu'un simple pourcentage d'accord parce qu'il corrige
   l'accord du a la chance : sur une grille de sophismes fortement desequilibree,
   deux evaluateurs qui repondraient au hasard s'accorderaient deja sur les
   classes frequentes. La matrice de coincidence suit Krippendorff (2011),
   ``alpha = 1 - D_o/D_e`` ; les unites portant moins de deux notations sont
   ecartees du calcul **et comptees**, jamais silencieusement perdues.

2. **Exactitude humaine contre l'etiquette du corpus**, avec intervalle de
   Wilson a 95 %. Wilson est retenu plutot que l'intervalle normal parce qu'il
   reste valide aux extremites (0 succes ou 100 % de succes), ou l'intervalle
   normal produit des bornes hors de [0, 1]. Quand chaque evaluateur note chaque
   item, la moyenne par evaluateur et le taux groupe **coincident** : c'est ce
   que l'outil rapporte, et un test verrouille cette coincidence.

3. **Liste des desaccords** -- les items sans valeur majoritaire stricte, qui
   partent en re-vue selon le paragraphe 5 du protocole. L'outil ne reecrit
   jamais la donnee qu'il mesure : il rend la liste, la correction eventuelle
   passe par une PR dediee.

Les seuils sont **announces avant la mesure** (tableau 4 du protocole) et
arrivent ici en parametres (``--alpha-node-threshold``, ``--alpha-branch-threshold``)
pour que l'invocation les epingle : un seuil ajuste apres coup se voit dans la
ligne de commande, pas dans un re-run silencieux.

Tout est stdlib-only, comme les scripts soeurs de ``scripts/fallacy_detection/``.

Usage::

    python scripts/fallacy_detection/score_external_eval.py \
        --key MyIA.AI.Notebooks/GenAI/FallacyDetection/data/external_eval/run1/key.jsonl \
        --annotations MyIA.AI.Notebooks/GenAI/FallacyDetection/data/external_eval/run1/pass1/ \
        --out-dir MyIA.AI.Notebooks/GenAI/FallacyDetection/data/external_eval/run1/report/
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from collections import Counter
from pathlib import Path

# z(0.975) -- quantile normal a 95 %. Fige ici pour que l'intervalle soit
# reproductible sans dependance a une table externe.
Z_95 = 1.959963984540054


def sha256_of(path: Path) -> str:
    """Empreinte SHA-256 d'un fichier, lue par blocs."""
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def read_jsonl(path: Path) -> list[dict]:
    """Lit un JSONL, en refusant explicitement une ligne illisible."""
    records: list[dict] = []
    with path.open(encoding="utf-8") as handle:
        for lineno, line in enumerate(handle, start=1):
            line = line.strip()
            if not line:
                continue
            try:
                record = json.loads(line)
            except json.JSONDecodeError as exc:
                raise SystemExit(f"{path}:{lineno} : JSON illisible ({exc.msg}).")
            if not isinstance(record, dict):
                raise SystemExit(f"{path}:{lineno} : objet JSON attendu, {type(record).__name__} recu.")
            records.append(record)
    if not records:
        raise SystemExit(f"{path} : aucun enregistrement.")
    return records


def branch_of(node: str, separator: str) -> str:
    """Branche de premier niveau d'un noeud, selon le separateur du protocole."""
    branch = node.split(separator)[0].strip()
    if not branch:
        raise SystemExit(
            f"Noeud '{node}' : branche de premier niveau vide (separateur '{separator}')."
        )
    return branch


def load_key(path: Path, separator: str) -> dict[str, dict[str, str]]:
    """Cle de correction : item_id -> {node, branch}. Refuse les doublons."""
    key: dict[str, dict[str, str]] = {}
    for record in read_jsonl(path):
        missing = [f for f in ("item_id", "node") if f not in record]
        if missing:
            raise SystemExit(f"{path} : champs manquants {missing} dans la cle.")
        item_id = record["item_id"]
        if item_id in key:
            raise SystemExit(f"{path} : item_id '{item_id}' present deux fois dans la cle.")
        key[item_id] = {"node": record["node"], "branch": branch_of(record["node"], separator)}
    return key


def load_raters(directory: Path, key: dict[str, dict[str, str]], separator: str) -> dict[str, dict[str, dict[str, str]]]:
    """Feuilles d'evaluation : evaluateur -> item_id -> {node, branch}.

    Fail-closed sur trois classes d'erreur de saisie : item inconnu de la cle
    (feuille d'une autre campagne), item note deux fois par le meme evaluateur
    (ambigu), et famille declaree qui contredit le noeud (colonnes transposees).
    Un evaluateur qui n'a pas note un item est accepte -- la donnee manquante
    est legitime dans l'alpha -- mais il est compte et rapporte.
    """
    if not directory.is_dir():
        raise SystemExit(f"{directory} : repertoire d'annotations introuvable.")
    files = sorted(p for p in directory.glob("*.jsonl") if p.is_file())
    if not files:
        raise SystemExit(f"{directory} : aucune feuille '*.jsonl' -- rien a mesurer.")

    raters: dict[str, dict[str, dict[str, str]]] = {}
    for path in files:
        rater = path.stem
        ratings: dict[str, dict[str, str]] = {}
        for record in read_jsonl(path):
            missing = [f for f in ("item_id", "node") if f not in record]
            if missing:
                raise SystemExit(f"{path} : champs manquants {missing}.")
            item_id = record["item_id"]
            if item_id not in key:
                raise SystemExit(
                    f"{path} : item '{item_id}' absent de la cle de correction -- "
                    "feuille d'une autre campagne ?"
                )
            if item_id in ratings:
                raise SystemExit(f"{path} : item '{item_id}' note deux fois par '{rater}'.")
            branch = branch_of(record["node"], separator)
            declared = record.get("family")
            if declared is not None and declared.strip() != branch:
                raise SystemExit(
                    f"{path} : item '{item_id}' -- famille declaree '{declared}' "
                    f"contredit le noeud '{record['node']}' (branche '{branch}')."
                )
            ratings[item_id] = {"node": record["node"], "branch": branch}
        if not ratings:
            raise SystemExit(f"{path} : feuille vide.")
        if rater in raters:
            raise SystemExit(f"{directory} : deux feuilles pour l'evaluateur '{rater}'.")
        raters[rater] = ratings
    return raters


def krippendorff_alpha(units: list[list[str]]) -> dict:
    """Alpha nominal de Krippendorff sur une liste d'unites (une par item).

    Chaque unite porte la liste des notations recues ; les unites a moins de
    deux notations sont ecartees du calcul et **comptees** (champ ``dropped``).
    Quand l'accord attendu par chance est nul (toutes les notations identiques,
    aucune variation), l'alpha est conventionnellement 1 : l'accord est parfait
    et le denominateur est nul.
    """
    pairable = [unit for unit in units if len(unit) >= 2]
    dropped = len(units) - len(pairable)
    if not pairable:
        return {"alpha": None, "dropped": dropped, "pairable_values": 0, "values": []}

    values = sorted({value for unit in pairable for value in unit})
    index = {value: position for position, value in enumerate(values)}
    size = len(values)
    coincidence = [[0.0] * size for _ in range(size)]
    for unit in pairable:
        counts = Counter(unit)
        denominator = len(unit) - 1
        for left, left_count in counts.items():
            for right, right_count in counts.items():
                pairs = left_count * (left_count - 1) if left == right else left_count * right_count
                coincidence[index[left]][index[right]] += pairs / denominator

    marginals = [sum(row) for row in coincidence]
    total = sum(marginals)
    if total <= 1:
        return {"alpha": None, "dropped": dropped, "pairable_values": total, "values": values}

    observed = sum(
        coincidence[i][j] for i in range(size) for j in range(size) if i != j
    ) / total
    expected = (total * total - sum(marginal * marginal for marginal in marginals)) / (
        total * (total - 1)
    )
    alpha = 1.0 if expected == 0 else 1.0 - observed / expected
    return {
        "alpha": alpha,
        "dropped": dropped,
        "pairable_values": total,
        "values": values,
        "observed_disagreement": observed,
        "expected_disagreement": expected,
    }


def wilson_interval(successes: int, trials: int, z: float = Z_95) -> tuple[float, float]:
    """Intervalle de Wilson a 95 % pour une proportion binomiale.

    Valide aux extremites (contrairement a l'intervalle normal, qui produit des
    bornes hors de [0, 1] quand la proportion est proche de 0 ou de 1).
    """
    if trials <= 0:
        raise SystemExit("Intervalle de Wilson demande sur zero essai.")
    if not 0 <= successes <= trials:
        raise SystemExit(f"Succes ({successes}) hors de [0, {trials}].")
    proportion = successes / trials
    z_squared = z * z
    denominator = 1 + z_squared / trials
    center = (proportion + z_squared / (2 * trials)) / denominator
    half = (z / denominator) * ((proportion * (1 - proportion) / trials + z_squared / (4 * trials * trials)) ** 0.5)
    return (_clamp01(center - half), _clamp01(center + half))


def _clamp01(value: float) -> float:
    """Ramene une borne dans [0, 1], en absorbant le residu flottant des extremites.

    Sans cette absorption, une proportion de 0 succes rend une borne basse a
    ~3,5e-18, qui s'imprimerait telle quelle dans un rapport au lieu du 0 attendu.
    """
    if value <= 1e-12:
        return 0.0
    if value >= 1 - 1e-12:
        return 1.0
    return value


def strict_majority(values: list[str]) -> str | None:
    """Valeur recueillie par plus de la moitie des notations, sinon None."""
    if not values:
        return None
    counts = Counter(values)
    value, count = counts.most_common(1)[0]
    if count * 2 > len(values):
        return value
    return None


def score(
    key: dict[str, dict[str, str]],
    raters: dict[str, dict[str, dict[str, str]]],
    alpha_node_threshold: float,
    alpha_branch_threshold: float,
) -> dict:
    """Calcule les mesures du tableau 4 du protocole."""
    rater_ids = sorted(raters)
    item_ids = sorted(key)

    levels = {
        "node": lambda item_id, rater: raters[rater].get(item_id, {}).get("node"),
        "branch": lambda item_id, rater: raters[rater].get(item_id, {}).get("branch"),
    }

    def reference(item_id: str, level: str) -> str:
        return key[item_id][level]

    results: dict[str, dict] = {}
    for level in ("node", "branch"):
        units = [
            [value for rater in rater_ids if (value := levels[level](item_id, rater)) is not None]
            for item_id in item_ids
        ]
        alpha = krippendorff_alpha(units)

        per_rater: dict[str, dict] = {}
        pooled_successes = 0
        pooled_trials = 0
        for rater in rater_ids:
            successes = sum(
                1
                for item_id in item_ids
                if (value := levels[level](item_id, rater)) is not None
                and value == reference(item_id, level)
            )
            trials = sum(1 for item_id in item_ids if levels[level](item_id, rater) is not None)
            low, high = wilson_interval(successes, trials)
            per_rater[rater] = {
                "rated": trials,
                "coverage": trials / len(item_ids),
                "correct": successes,
                "accuracy": successes / trials,
                "wilson_95": [low, high],
            }
            pooled_successes += successes
            pooled_trials += trials

        pooled_low, pooled_high = wilson_interval(pooled_successes, pooled_trials)
        # Quand chaque evaluateur note chaque item, moyenne par evaluateur et
        # taux groupe coincident ; l'ecart est rapporte sinon, jamais masque.
        mean_of_raters = sum(entry["accuracy"] for entry in per_rater.values()) / len(rater_ids)
        results[level] = {
            "alpha": alpha["alpha"],
            "alpha_dropped_units": alpha["dropped"],
            "alpha_pairable_values": alpha["pairable_values"],
            "distinct_values": len(alpha["values"]),
            "pooled": {
                "correct": pooled_successes,
                "rated": pooled_trials,
                "accuracy": pooled_successes / pooled_trials,
                "wilson_95": [pooled_low, pooled_high],
            },
            "mean_of_raters": mean_of_raters,
            "mean_equals_pooled": abs(mean_of_raters - pooled_successes / pooled_trials) < 1e-12,
            "per_rater": per_rater,
        }

    # Desaccords : items sans majorite stricte, au niveau noeud (le plus fin).
    disagreements: list[dict] = []
    unanimous = 0
    for item_id in item_ids:
        values = [raters[rater][item_id]["node"] for rater in rater_ids if item_id in raters[rater]]
        if len(set(values)) == 1 and len(values) >= 2:
            unanimous += 1
        winner = strict_majority(values)
        if winner is None:
            disagreements.append({
                "item_id": item_id,
                "counts": dict(sorted(Counter(values).items(), key=lambda kv: (-kv[1], kv[0]))),
                "reference_node": key[item_id]["node"],
                "ratings": len(values),
            })

    return {
        "key_items": len(item_ids),
        "raters": rater_ids,
        "levels": results,
        "agreement": {
            "unanimous": unanimous,
            "with_strict_majority": len(item_ids) - len(disagreements),
            "disagreements": len(disagreements),
        },
        "disagreement_items": disagreements,
        "thresholds": {
            "alpha_node": alpha_node_threshold,
            "alpha_branch": alpha_branch_threshold,
        },
        "verdicts": {
            "alpha_node": _verdict(results["node"]["alpha"], alpha_node_threshold),
            "alpha_branch": _verdict(results["branch"]["alpha"], alpha_branch_threshold),
        },
    }


def _verdict(alpha: float | None, threshold: float) -> str:
    if alpha is None:
        return "INDETERMINE (aucune unite appariable)"
    return "SEUIL ATTEINT" if alpha >= threshold else "SEUIL NON ATTEINT"


def render_report(scores: dict) -> str:
    """Tableau 4 du protocole, rempli. Markdown lisible, aucune donnee nominative."""
    lines: list[str] = []
    lines.append("# Mesure du test externe humain (#20222)")
    lines.append("")
    lines.append(
        f"{scores['key_items']} items, {len(scores['raters'])} evaluateurs : "
        f"{', '.join(scores['raters'])}."
    )
    lines.append("")
    lines.append("| Mesure | Niveau | Seuil annonce | Valeur mesuree | Verdict |")
    lines.append("|---|---|---|---|---|")
    node = scores["levels"]["node"]
    branch = scores["levels"]["branch"]
    lines.append(
        f"| alpha de Krippendorff | noeud | >= {scores['thresholds']['alpha_node']:.2f} | "
        f"{_fmt(node['alpha'])} | {scores['verdicts']['alpha_node']} |"
    )
    lines.append(
        f"| alpha de Krippendorff | branche | >= {scores['thresholds']['alpha_branch']:.2f} | "
        f"{_fmt(branch['alpha'])} | {scores['verdicts']['alpha_branch']} |"
    )
    lines.append(
        f"| exactitude humaine moyenne | noeud | rapportee | {node['mean_of_raters']:.3f} "
        f"(IC 95 % {node['pooled']['wilson_95'][0]:.3f}-{node['pooled']['wilson_95'][1]:.3f}) | - |"
    )
    lines.append(
        f"| exactitude humaine moyenne | branche | rapportee | {branch['mean_of_raters']:.3f} "
        f"(IC 95 % {branch['pooled']['wilson_95'][0]:.3f}-{branch['pooled']['wilson_95'][1]:.3f}) | - |"
    )
    lines.append("")
    lines.append("## Detail par evaluateur")
    lines.append("")
    lines.append("| Evaluateur | Items notes | Couverture | Exactitude noeud | Exactitude branche |")
    lines.append("|---|---|---|---|---|")
    for rater in scores["raters"]:
        node_rater = node["per_rater"][rater]
        branch_rater = branch["per_rater"][rater]
        lines.append(
            f"| {rater} | {node_rater['rated']} | {node_rater['coverage']:.1%} | "
            f"{node_rater['accuracy']:.3f} | {branch_rater['accuracy']:.3f} |"
        )
    lines.append("")
    agreement = scores["agreement"]
    lines.append(
        f"## Accord\n\nUnanimes : {agreement['unanimous']} · majorite stricte : "
        f"{agreement['with_strict_majority']} · a revoir : {agreement['disagreements']}."
    )
    if node["alpha_dropped_units"]:
        lines.append(
            f"\n{node['alpha_dropped_units']} item(s) ecarte(s) de l'alpha "
            "(moins de deux notations)."
        )
    if scores["disagreement_items"]:
        lines.append("")
        lines.append("## Items a revoir (aucune majorite stricte)")
        lines.append("")
        lines.append("| Item | Etiquette corpus | Reponses |")
        lines.append("|---|---|---|")
        for item in scores["disagreement_items"]:
            counts = ", ".join(f"{value} x{count}" for value, count in item["counts"].items())
            lines.append(f"| {item['item_id']} | {item['reference_node']} | {counts} |")
    lines.append("")
    return "\n".join(lines)


def _fmt(value: float | None) -> str:
    return "n/a" if value is None else f"{value:.3f}"


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--key", required=True, type=Path, help="cle de correction (JSONL item_id, node)")
    parser.add_argument("--annotations", required=True, type=Path, help="repertoire des feuilles remplies (*.jsonl)")
    parser.add_argument("--out-dir", required=True, type=Path, help="repertoire de sortie (report.md, scores.json)")
    parser.add_argument("--family-separator", default="/", help="separateur de chemin du noeud (defaut '/')")
    # Seuils annonces AVANT la mesure (protocole, tableau 4). Les figer en
    # parametres rend tout ajustement apres coup visible dans l'invocation.
    parser.add_argument("--alpha-node-threshold", type=float, default=0.60)
    parser.add_argument("--alpha-branch-threshold", type=float, default=0.70)
    args = parser.parse_args(argv)

    key = load_key(args.key, args.family_separator)
    raters = load_raters(args.annotations, key, args.family_separator)
    if len(raters) < 2:
        raise SystemExit(
            f"{len(raters)} feuille(s) d'evaluation : l'accord inter-evaluateurs "
            "exige au moins deux evaluateurs."
        )

    scores = score(key, raters, args.alpha_node_threshold, args.alpha_branch_threshold)
    scores["inputs"] = {
        "key": {"path": str(args.key), "sha256": sha256_of(args.key)},
        "annotations": {
            rater: {"path": str(path), "sha256": sha256_of(path)}
            for rater, path in (
                (path.stem, path) for path in sorted(args.annotations.glob("*.jsonl"))
            )
        },
    }

    args.out_dir.mkdir(parents=True, exist_ok=True)
    report_path = args.out_dir / "report.md"
    scores_path = args.out_dir / "scores.json"
    report_path.write_text(render_report(scores), encoding="utf-8")
    scores_path.write_text(json.dumps(scores, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")

    node = scores["levels"]["node"]
    branch = scores["levels"]["branch"]
    print(f"Alpha noeud    : {_fmt(node['alpha'])} (seuil {args.alpha_node_threshold:.2f}) -- {scores['verdicts']['alpha_node']}")
    print(f"Alpha branche  : {_fmt(branch['alpha'])} (seuil {args.alpha_branch_threshold:.2f}) -- {scores['verdicts']['alpha_branch']}")
    print(f"Exactitude noeud   : {node['mean_of_raters']:.3f} (IC 95 % {node['pooled']['wilson_95'][0]:.3f}-{node['pooled']['wilson_95'][1]:.3f})")
    print(f"Exactitude branche : {branch['mean_of_raters']:.3f} (IC 95 % {branch['pooled']['wilson_95'][0]:.3f}-{branch['pooled']['wilson_95'][1]:.3f})")
    print(f"Items a revoir : {scores['agreement']['disagreements']} / {scores['key_items']}")
    print(f"Rapport : {report_path}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
