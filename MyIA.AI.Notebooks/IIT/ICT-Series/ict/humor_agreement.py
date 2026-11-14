# -*- coding: utf-8 -*-
"""Mesure de l'accord inter-annotateurs et du cout en tokens (residue #20301).

Ce module est l'**instrument de mesure** d'une campagne d'annotation humour : il
ne produit aucune annotation (le producteur — corpus public + annotation par
modele — vit dans `scripts/humor_detection/` et `ict/humor_annotation.py`, sur
les perimetres d'autres lanes), il **mesure** ce qu'une campagne deja produite
donne :

- l'accord inter-annotateurs, par le **kappa de Cohen** (categories nominales,
  multi-categories), avec la matrice de confusion et les marges ;
- le **cout en tokens** de la campagne, par annotateur et au total ;
- la **ligne de base du hasard** (distribution de kappa par permutation), qui
  est le temoin negatif de l'experience : un annotateur nul ne doit pas
  depasser cette bande, sinon l'accord mesure n'est pas un accord.

Decoupage des responsabilites (producteur / verificateur) : ce module ne
connait ni le corpus, ni les modeles, ni les prompts — il ne manipule que des
**etiquettes deja produites** et leur **facture de tokens**. Il est donc
rejouable hors ligne, deterministe, sans cle et sans reseau.

Format des enregistrements (une ligne par item annote) :

    {"id": "item-001", "annotator": "modele-A", "label": "humour",
     "prompt_tokens": 812, "completion_tokens": 7}

Les lectures/ecritures se font en JSONL, fichier **hors depot** par defaut
(le corpus public n'est pas recopi dans le depot ; cf. `bibliography-hygiene`).

Bandes d'interpretation du kappa (Landis & Koch, 1977) : le seuil est ici, ecrit
et teste, pour qu'il ne soit pas decide au moment de la lecture du resultat.

Stdlib uniquement : le module ne depend ni de numpy ni d'un client de modele.
"""

from __future__ import annotations

import json
import random
from pathlib import Path
from typing import Any, Iterable, Mapping, Sequence

__all__ = [
    "KAPPA_BANDS",
    "agreement_report",
    "chance_kappa_distribution",
    "cohen_kappa",
    "group_by_annotator",
    "interpret_kappa",
    "pairwise_agreement",
    "read_annotations_jsonl",
    "token_cost",
    "write_annotations_jsonl",
]


# --------------------------------------------------------------------------- #
# Bandes d'interpretation (Landis & Koch, 1977)
# --------------------------------------------------------------------------- #

#: ``(borne_inferieure_inclusive, libelle)``, bornes croissantes. Le libelle
#: retenu est celui de la plus grande borne inferieure <= kappa.
KAPPA_BANDS: tuple[tuple[float, str], ...] = (
    (-1.01, "accord pauvre (kappa negatif : les annotateurs se desaccordent plus que le hasard)"),
    (0.00, "accord faible"),
    (0.21, "accord modere"),
    (0.41, "accord substantiel"),
    (0.61, "accord fort"),
    (0.81, "accord presque parfait"),
)


def interpret_kappa(kappa: float | None) -> str:
    """Libelle de la bande d'interpretation du kappa (Landis & Koch, 1977).

    ``kappa=None`` (accord attendu par le hasard nul, marges degenerees) est
    signale explicitement : c'est une mesure indefinie, pas un accord nul.
    """
    if kappa is None:
        return "indefini : l'accord attendu par le hasard est nul (marges degenerees)"
    label = KAPPA_BANDS[0][1]
    for lower, candidate in KAPPA_BANDS:
        if kappa >= lower:
            label = candidate
    return label


# --------------------------------------------------------------------------- #
# Kappa de Cohen
# --------------------------------------------------------------------------- #


def cohen_kappa(
    labels_a: Sequence[Any],
    labels_b: Sequence[Any],
    *,
    categories: Sequence[Any] | None = None,
) -> dict[str, Any]:
    """Kappa de Cohen entre deux series d'etiquettes nominales.

    Retourne un dictionnaire : ``kappa`` (float ou ``None`` si l'accord attendu
    par le hasard est nul), ``n``, ``observed_agreement``,
    ``expected_agreement``, ``categories``, ``confusion`` (lignes = annotateur
    A, colonnes = annotateur B), ``marginals`` et ``undefined_reason``.
    """
    a = list(labels_a)
    b = list(labels_b)
    if len(a) != len(b):
        raise ValueError(
            f"series de longueurs differentes : {len(a)} et {len(b)}"
        )
    if not a:
        raise ValueError("series vides : kappa indefini")

    if categories is None:
        cats = sorted(set(a) | set(b), key=repr)
    else:
        cats = list(categories)
    unknown = (set(a) | set(b)) - set(cats)
    if unknown:
        raise ValueError(f"etiquettes hors categories declarees : {sorted(unknown, key=repr)}")

    n = len(a)
    confusion: dict[Any, dict[Any, int]] = {c: {d: 0 for d in cats} for c in cats}
    for x, y in zip(a, b):
        confusion[x][y] += 1

    observed = sum(confusion[c][c] for c in cats) / n
    marg_a = {c: sum(confusion[c].values()) / n for c in cats}
    marg_b = {c: sum(confusion[c][d] for d in cats) / n for c in cats}
    expected = sum(marg_a[c] * marg_b[c] for c in cats)

    if expected >= 1.0:
        kappa: float | None = None
        reason = "accord attendu par le hasard nul (une seule categorie presente des deux cotes)"
    else:
        kappa = (observed - expected) / (1.0 - expected)
        reason = None

    return {
        "kappa": kappa,
        "n": n,
        "observed_agreement": observed,
        "expected_agreement": expected,
        "categories": cats,
        "confusion": confusion,
        "marginals": {"a": marg_a, "b": marg_b},
        "undefined_reason": reason,
        "interpretation": interpret_kappa(kappa),
    }


def group_by_annotator(records: Iterable[Mapping[str, Any]]) -> dict[str, dict[Any, Any]]:
    """Regroupe des enregistrements d'annotation par annotateur.

    Chaque annotateur est associe a ``{item_id: label}``. Un item annote deux
    fois par le **meme** annotateur est refuse : l'accord n'a pas de sens sur
    une annotation reecrite, et l'ecraser masquerait la rewrite.
    """
    grouped: dict[str, dict[Any, Any]] = {}
    for record in records:
        annotator = str(record["annotator"])
        item = record["id"]
        bucket = grouped.setdefault(annotator, {})
        if item in bucket:
            raise ValueError(
                f"item {item!r} annote deux fois par {annotator!r} : "
                "l'accord suppose une annotation unique par item et par annotateur"
            )
        bucket[item] = record["label"]
    return grouped


def pairwise_agreement(
    records: Iterable[Mapping[str, Any]],
    *,
    categories: Sequence[Any] | None = None,
) -> dict[str, dict[str, Any]]:
    """Kappa de chaque paire d'annotateurs, sur les items annotes par les deux.

    ``categories`` fige le jeu d'etiquettes. Laisse a ``None``, chaque paire
    deduit ses categories de l'union de ses deux series : deux paires n'ayant
    pas vu les memes categories produisent alors des kappa qui ne sont pas
    strictement comparables entre eux. Pour comparer des paires dans un
    rapport de campagne, passer un jeu explicite -- par exemple via
    ``agreement_report(categories=...)``, qui le propage a chaque paire.
    """
    grouped = group_by_annotator(records)
    names = sorted(grouped)
    out: dict[str, dict[str, Any]] = {}
    for i, first in enumerate(names):
        for second in names[i + 1 :]:
            shared = sorted(set(grouped[first]) & set(grouped[second]), key=repr)
            labels_a = [grouped[first][item] for item in shared]
            labels_b = [grouped[second][item] for item in shared]
            key = f"{first} vs {second}"
            if not shared:
                out[key] = {
                    "kappa": None,
                    "n": 0,
                    "undefined_reason": "aucun item annote par les deux annotateurs",
                    "interpretation": interpret_kappa(None),
                }
                continue
            summary = cohen_kappa(labels_a, labels_b, categories=categories)
            summary["items"] = shared
            out[key] = summary
    return out


# --------------------------------------------------------------------------- #
# Cout en tokens
# --------------------------------------------------------------------------- #


def token_cost(records: Iterable[Mapping[str, Any]]) -> dict[str, Any]:
    """Facture de tokens d'une campagne d'annotation, par annotateur et au total."""
    per_annotator: dict[str, dict[str, Any]] = {}
    for record in records:
        annotator = str(record["annotator"])
        bucket = per_annotator.setdefault(
            annotator,
            {"items": 0, "prompt_tokens": 0, "completion_tokens": 0, "total_tokens": 0},
        )
        prompt = int(record.get("prompt_tokens", 0) or 0)
        completion = int(record.get("completion_tokens", 0) or 0)
        bucket["items"] += 1
        bucket["prompt_tokens"] += prompt
        bucket["completion_tokens"] += completion
        bucket["total_tokens"] += prompt + completion

    for bucket in per_annotator.values():
        items = bucket["items"]
        bucket["mean_total_tokens_per_item"] = (
            bucket["total_tokens"] / items if items else 0.0
        )

    total_tokens = sum(b["total_tokens"] for b in per_annotator.values())
    total_items = sum(b["items"] for b in per_annotator.values())
    return {
        "per_annotator": per_annotator,
        "total_tokens": total_tokens,
        "total_items": total_items,
        "mean_total_tokens_per_item": (
            total_tokens / total_items if total_items else 0.0
        ),
    }


# --------------------------------------------------------------------------- #
# Temoin negatif : la bande du hasard
# --------------------------------------------------------------------------- #


def chance_kappa_distribution(
    labels_a: Sequence[Any],
    labels_b: Sequence[Any],
    *,
    n_draws: int = 200,
    seed: int = 42,
) -> dict[str, Any]:
    """Distribution du kappa quand l'annotateur B est permute au hasard.

    C'est le **temoin negatif** de l'experience d'accord : un annotateur sans
    information (permutation) ne doit pas produire un kappa au-dessus de cette
    bande. Un kappa mesure qui traine dedans n'est pas un accord.
    """
    a = list(labels_a)
    b = list(labels_b)
    if len(a) != len(b):
        raise ValueError(f"series de longueurs differentes : {len(a)} et {len(b)}")
    if not a:
        raise ValueError("series vides : distribution indefinee")

    rng = random.Random(seed)
    shuffled = list(b)
    values: list[float] = []
    for _ in range(n_draws):
        rng.shuffle(shuffled)
        summary = cohen_kappa(a, shuffled)
        if summary["kappa"] is not None:
            values.append(summary["kappa"])
    if not values:
        return {
            "n_draws": n_draws,
            "seed": seed,
            "values": [],
            "mean": None,
            "p95": None,
            "max": None,
            "interpretation": "distribution vide (aucun kappa defini sous permutation)",
        }
    values.sort()
    index_95 = min(len(values) - 1, int(round(0.95 * (len(values) - 1))))
    return {
        "n_draws": n_draws,
        "seed": seed,
        "values": values,
        "mean": sum(values) / len(values),
        "p95": values[index_95],
        "max": values[-1],
        "interpretation": (
            "bande du hasard : un kappa mesure au-dessus du p95 de cette "
            "distribution depasse l'accord que le hasard produirait"
        ),
    }


# --------------------------------------------------------------------------- #
# Rapport
# --------------------------------------------------------------------------- #


def agreement_report(
    records: Iterable[Mapping[str, Any]],
    *,
    reference: Mapping[Any, Any] | None = None,
    categories: Sequence[Any] | None = None,
) -> dict[str, Any]:
    """Rapport d'une campagne d'annotation : accords, cout, ligne de base.

    ``reference`` est un etiquetage de reference (typiquement humain) sous la
    forme ``{item_id: label}`` : l'accord de chaque annotateur avec cette
    reference est alors mesure sur les items partages.

    ``categories`` fige le jeu d'etiquettes, et le propage a chaque paire --
    a passer des lors que le rapport compare des paires entre elles (voir
    ``pairwise_agreement``).
    """
    materialized = list(records)
    grouped = group_by_annotator(materialized)
    report: dict[str, Any] = {
        "n_records": len(materialized),
        "n_items": len({record["id"] for record in materialized}),
        "annotators": sorted(grouped),
        "pairwise": pairwise_agreement(materialized, categories=categories),
        "token_cost": token_cost(materialized),
        "vs_reference": None,
    }

    if reference is not None:
        vs_reference: dict[str, Any] = {}
        for annotator, labels in sorted(grouped.items()):
            shared = sorted(set(labels) & set(reference), key=repr)
            key = f"{annotator} vs reference"
            if not shared:
                vs_reference[key] = {
                    "kappa": None,
                    "n": 0,
                    "undefined_reason": "aucun item annote par cet annotateur et present dans la reference",
                    "interpretation": interpret_kappa(None),
                }
                continue
            summary = cohen_kappa(
                [labels[item] for item in shared],
                [reference[item] for item in shared],
                categories=categories,
            )
            summary["items"] = shared
            vs_reference[key] = summary
        report["vs_reference"] = vs_reference

    return report


# --------------------------------------------------------------------------- #
# Lecture / ecriture JSONL (fichiers hors depot par defaut)
# --------------------------------------------------------------------------- #


def read_annotations_jsonl(path: str | Path) -> list[dict[str, Any]]:
    """Lit un fichier d'annotations JSONL (une ligne JSON par item annote)."""
    records: list[dict[str, Any]] = []
    with Path(path).open("r", encoding="utf-8") as handle:
        for line_no, line in enumerate(handle, start=1):
            line = line.strip()
            if not line:
                continue
            try:
                payload = json.loads(line)
            except json.JSONDecodeError as exc:
                raise ValueError(f"ligne {line_no} illisible : {exc}") from exc
            for key in ("id", "annotator", "label"):
                if key not in payload:
                    raise ValueError(f"ligne {line_no} : champ {key!r} manquant")
            records.append(payload)
    return records


def write_annotations_jsonl(path: str | Path, records: Iterable[Mapping[str, Any]]) -> int:
    """Ecrit des enregistrements d'annotation en JSONL ; retourne le nombre ecrit."""
    written = 0
    with Path(path).open("w", encoding="utf-8", newline="\n") as handle:
        for record in records:
            handle.write(json.dumps(record, ensure_ascii=False, sort_keys=True))
            handle.write("\n")
            written += 1
    return written
