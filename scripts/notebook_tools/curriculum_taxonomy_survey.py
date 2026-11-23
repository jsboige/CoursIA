#!/usr/bin/env python3
"""Relevé de densité et de ponts sur l'ensemble des taxonomies du cursus.

Fonctions pures, sans accès disque : elles reçoivent un corpus déjà lu,
`{nom de taxonomie: données JSON}`, où le nom est celui du fichier sans
extension. L'unité de mesure est la taxonomie (un fichier, un vocabulaire) :
deux fichiers peuvent déclarer le même champ `series`, ils restent deux
taxonomies.

Le relevé mesure, il ne valide pas : il lit ce qui est écrit, y compris dans
un fichier en cours de rédaction. Le contrôle des références et des cellules
reste `curriculum_taxonomy.py --all`.
"""

from __future__ import annotations

import re
import statistics
import unicodedata
from collections import defaultdict
from itertools import combinations

Corpus = dict[str, dict]
MATCH_KINDS = ("exact", "close")


def concepts_of(data: dict) -> list[dict]:
    """Concepts exploitables d'une taxonomie : objets portant un identifiant."""
    concepts = data.get("concepts")
    if not isinstance(concepts, list):
        return []
    return [c for c in concepts if isinstance(c, dict) and isinstance(c.get("id"), str)]


def notebooks_of(data: dict) -> list[str]:
    notebooks = data.get("notebooks")
    if not isinstance(notebooks, list):
        return []
    return [notebook for notebook in notebooks if isinstance(notebook, str)]


def citations_of(concept: dict) -> list[dict]:
    citations = concept.get("citations")
    if not isinstance(citations, list):
        return []
    return [c for c in citations if isinstance(c, dict) and isinstance(c.get("notebook"), str)]


def prerequisites_of(concept: dict) -> list[str]:
    prerequisites = concept.get("prerequisites")
    if not isinstance(prerequisites, list):
        return []
    return [value for value in prerequisites if isinstance(value, str)]


def matches_of(concept: dict) -> list[tuple[str, str]]:
    """Alignements déclarés par un concept : couples (concept visé, kind)."""
    matches = concept.get("matches")
    if not isinstance(matches, list):
        return []
    return [
        (match["concept"], match["kind"]) for match in matches
        if isinstance(match, dict) and isinstance(match.get("concept"), str)
        and match.get("kind") in MATCH_KINDS
    ]


def owners(corpus: Corpus) -> tuple[dict[str, str], dict[str, str]]:
    """Taxonomie qui déclare chaque concept et chaque carnet (première déclaration lue)."""
    concept_owner: dict[str, str] = {}
    notebook_owner: dict[str, str] = {}
    for name, data in corpus.items():
        for concept in concepts_of(data):
            concept_owner.setdefault(concept["id"], name)
        for notebook in notebooks_of(data):
            notebook_owner.setdefault(notebook, name)
    return concept_owner, notebook_owner


def alignments(corpus: Corpus) -> dict[frozenset[str], str]:
    """Alignements déclarés, une entrée par paire non ordonnée.

    `skos:exactMatch` et `skos:closeMatch` sont symétriques : une déclaration
    d'un seul côté suffit, et deux déclarations réciproques comptent pour un
    alignement. En cas de kinds contradictoires, la première lue est gardée ;
    c'est le validateur qui refuse la contradiction.
    """
    declared: dict[frozenset[str], str] = {}
    for data in corpus.values():
        for concept in concepts_of(data):
            for target, kind in matches_of(concept):
                if target != concept["id"]:
                    declared.setdefault(frozenset((concept["id"], target)), kind)
    return declared


def exact_classes(corpus: Corpus) -> list[list[str]]:
    """Classes d'équivalence des alignements exacts (fermeture symétrique et transitive)."""
    parent: dict[str, str] = {}

    def find(node: str) -> str:
        parent.setdefault(node, node)
        while parent[node] != node:
            parent[node] = parent[parent[node]]
            node = parent[node]
        return node

    for pair, kind in alignments(corpus).items():
        if kind == "exact":
            first, second = sorted(pair)
            parent[find(second)] = find(first)
    classes: dict[str, list[str]] = defaultdict(list)
    for node in parent:
        classes[find(node)].append(node)
    return sorted(sorted(members) for members in classes.values() if len(members) > 1)


def normalize(text: object) -> str:
    """Forme de comparaison d'un libellé ou d'une définition.

    Sans accents, sans casse, ponctuation et espaces réduits à un espace :
    « Fonction d'utilité » et « fonction d’utilite » donnent la même clé.
    """
    if not isinstance(text, str):
        return ""
    decomposed = unicodedata.normalize("NFKD", text)
    stripped = "".join(ch for ch in decomposed if not unicodedata.combining(ch)).casefold()
    return " ".join(re.sub(r"[\W_]+", " ", stripped).split())


def _distribution(values: list[int]) -> dict[str, float | int | None]:
    if not values:
        return {"min": None, "median": None, "max": None}
    return {"min": min(values), "median": statistics.median(values), "max": max(values)}


def density(corpus: Corpus) -> dict:
    """Densité par taxonomie : concepts par carnet déclaré, carnets à zéro, concepts mono-citation.

    Le nombre de concepts d'un carnet compte les concepts distincts qui le
    citent, quelle que soit la taxonomie qui les déclare : un carnet cité par
    le concept d'une autre série enseigne bien ce concept.
    """
    cited_by: dict[str, set[str]] = defaultdict(set)
    for data in corpus.values():
        for concept in concepts_of(data):
            for citation in citations_of(concept):
                cited_by[citation["notebook"]].add(concept["id"])

    rows: list[dict] = []
    every_count: list[int] = []
    for name, data in corpus.items():
        concepts = concepts_of(data)
        per_notebook = {notebook: len(cited_by.get(notebook, ())) for notebook in notebooks_of(data)}
        citation_counts = [len(citations_of(concept)) for concept in concepts]
        notebook_spans = [
            len({citation["notebook"] for citation in citations_of(concept)}) for concept in concepts
        ]
        rows.append({
            "taxonomy": name,
            "series": data.get("series"),
            "notebooks": len(per_notebook),
            "concepts": len(concepts),
            "citations": sum(citation_counts),
            "concepts_per_notebook": _distribution(list(per_notebook.values())),
            "zero_notebooks": sorted(nb for nb, count in per_notebook.items() if count == 0),
            "single_citation_concepts": citation_counts.count(1),
            "single_notebook_concepts": notebook_spans.count(1),
            "per_notebook": per_notebook,
        })
        every_count.extend(per_notebook.values())
    total = {
        "taxonomies": len(rows),
        "notebooks": sum(row["notebooks"] for row in rows),
        "concepts": sum(row["concepts"] for row in rows),
        "citations": sum(row["citations"] for row in rows),
        "concepts_per_notebook": _distribution(every_count),
        "zero_notebooks": sum(len(row["zero_notebooks"]) for row in rows),
        "single_citation_concepts": sum(row["single_citation_concepts"] for row in rows),
        "single_notebook_concepts": sum(row["single_notebook_concepts"] for row in rows),
    }
    return {"taxonomies": rows, "total": total}


def bridges(corpus: Corpus) -> dict:
    """Ponts entre taxonomies : déclarés (trois familles) et candidats.

    Déclarés : concept cité par des carnets de deux taxonomies ou plus,
    prérequis qui vise le concept d'une autre taxonomie, alignement
    `exact` ou `close`. Candidats : deux identifiants de taxonomies différentes
    qui portent le même libellé normalisé ou la même définition normalisée et
    qu'aucun alignement ne relie encore.
    """
    concept_owner, notebook_owner = owners(corpus)
    by_id: dict[str, dict] = {}
    for data in corpus.values():
        for concept in concepts_of(data):
            by_id.setdefault(concept["id"], concept)

    def ref(concept_id: str) -> dict:
        return {
            "concept": concept_id,
            "label_fr": by_id.get(concept_id, {}).get("label_fr"),
            "taxonomy": concept_owner.get(concept_id),
        }

    pairs: dict[str, dict[str, int]] = {}

    def bump(names: list[str | None], family: str) -> None:
        known = sorted({name for name in names if name is not None})
        for first, second in combinations(known, 2):
            counts = pairs.setdefault(f"{first} <-> {second}", {
                "shared_concepts": 0, "cross_prerequisites": 0, "exact": 0, "close": 0, "candidates": 0,
            })
            counts[family] += 1

    shared: list[dict] = []
    cross: list[dict] = []
    for name, data in corpus.items():
        for concept in concepts_of(data):
            cited = sorted({c["notebook"] for c in citations_of(concept)})
            cited_taxonomies = sorted({notebook_owner[nb] for nb in cited if nb in notebook_owner})
            if len(cited_taxonomies) >= 2:
                shared.append({**ref(concept["id"]), "taxonomies": cited_taxonomies, "notebooks": cited})
                bump(list(cited_taxonomies), "shared_concepts")
            for prerequisite in prerequisites_of(concept):
                target = concept_owner.get(prerequisite)
                if target is not None and target != name:
                    cross.append({**ref(concept["id"]), "requires": ref(prerequisite)})
                    bump([name, target], "cross_prerequisites")

    declared = alignments(corpus)
    aligned: list[dict] = []
    for pair in sorted(declared, key=sorted):
        members = [ref(concept_id) for concept_id in sorted(pair)]
        aligned.append({"kind": declared[pair], "concepts": members})
        bump([member["taxonomy"] for member in members], declared[pair])

    classes = exact_classes(corpus)
    class_of = {member: index for index, members in enumerate(classes) for member in members}
    groups: dict[tuple[str, str], set[str]] = defaultdict(set)
    for concept_id, concept in by_id.items():
        for reason, fields in (("label", ("label_fr", "label_en")),
                               ("definition", ("definition_fr", "definition_en"))):
            for field in fields:
                key = normalize(concept.get(field))
                if key:
                    groups[(reason, key)].add(concept_id)
    reasons: dict[frozenset[str], set[str]] = defaultdict(set)
    for (reason, _key), concept_ids in groups.items():
        for pair in combinations(sorted(concept_ids), 2):
            reasons[frozenset(pair)].add(reason)
    candidates: list[dict] = []
    duplicates: list[dict] = []
    for pair in sorted(reasons, key=sorted):
        first, second = sorted(pair)
        if pair in declared or (first in class_of and class_of[first] == class_of.get(second)):
            continue
        entry = {"reasons": sorted(reasons[pair]), "concepts": [ref(first), ref(second)]}
        if concept_owner[first] == concept_owner[second]:
            duplicates.append(entry)
        else:
            candidates.append(entry)
            bump([concept_owner[first], concept_owner[second]], "candidates")

    return {
        "shared_concepts": shared,
        "cross_prerequisites": cross,
        "alignments": aligned,
        "exact_classes": [[ref(member) for member in members] for members in classes],
        "candidates": candidates,
        "duplicates_in_taxonomy": duplicates,
        "pairs": dict(sorted(pairs.items())),
        "summary": {
            "taxonomies": len(corpus),
            "shared_concepts": len(shared),
            "cross_prerequisites": len(cross),
            "exact": sum(entry["kind"] == "exact" for entry in aligned),
            "close": sum(entry["kind"] == "close" for entry in aligned),
            "candidates": len(candidates),
            "duplicates_in_taxonomy": len(duplicates),
        },
    }


def _number(value: float | int | None) -> str:
    if value is None:
        return "-"
    if isinstance(value, float) and not value.is_integer():
        return f"{value:.1f}".replace(".", ",")
    return str(int(value))


REASON_LABELS = {"label": "libellé", "definition": "définition"}


def _reasons(entry: dict) -> str:
    return " + ".join(REASON_LABELS[reason] for reason in entry["reasons"])


def _named(reference: dict) -> str:
    label = reference.get("label_fr") or "(concept hors du dossier)"
    return f"{label} [{reference.get('taxonomy') or '?'}] {reference['concept']}"


def render_density(report: dict) -> str:
    """Tableau texte du relevé de densité, une ligne par taxonomie."""
    header = ("taxonomie", "série", "carnets", "concepts", "citations",
              "min", "médiane", "max", "à zéro", "1 citation", "1 carnet")
    table = [header]
    for row in [*report["taxonomies"], {**report["total"], "taxonomy": "TOTAL", "series": ""}]:
        spread = row["concepts_per_notebook"]
        zero = row["zero_notebooks"]
        table.append((
            row["taxonomy"], str(row.get("series") or ""), str(row["notebooks"]), str(row["concepts"]),
            str(row["citations"]), _number(spread["min"]), _number(spread["median"]),
            _number(spread["max"]), str(zero if isinstance(zero, int) else len(zero)),
            str(row["single_citation_concepts"]), str(row["single_notebook_concepts"]),
        ))
    widths = [max(len(line[column]) for line in table) for column in range(len(header))]
    lines = [
        "Densité des taxonomies (min, médiane, max : concepts par carnet déclaré)",
        "à zéro : carnets qu'aucun concept ne cite ; 1 citation : concepts cités une seule fois ; "
        "1 carnet : concepts cités dans un seul carnet",
    ]
    for line in table:
        cells = [line[0].ljust(widths[0]), line[1].ljust(widths[1])]
        cells += [cell.rjust(width) for cell, width in zip(line[2:], widths[2:])]
        lines.append("  ".join(cells).rstrip())
    zero_notebooks = [(row["taxonomy"], nb) for row in report["taxonomies"] for nb in row["zero_notebooks"]]
    if zero_notebooks:
        lines.append("Carnets déclarés sans aucun concept :")
        lines.extend(f"  {taxonomy} : {notebook}" for taxonomy, notebook in zero_notebooks)
    else:
        lines.append("Carnets déclarés sans aucun concept : aucun")
    return "\n".join(lines)


def render_bridges(report: dict) -> str:
    """Liste texte des ponts, puis décompte par paire de taxonomies."""
    summary = report["summary"]
    lines = [f"Ponts entre taxonomies ({summary['taxonomies']} taxonomies lues)"]
    lines.append(f"Concepts cités par des carnets de deux taxonomies ou plus : {summary['shared_concepts']}")
    lines.extend(f"  {_named(entry)} -- carnets de {', '.join(entry['taxonomies'])}"
                 for entry in report["shared_concepts"])
    lines.append(f"Prérequis franchissant une frontière de taxonomie : {summary['cross_prerequisites']}")
    lines.extend(f"  {_named(entry)} requiert {_named(entry['requires'])}"
                 for entry in report["cross_prerequisites"])
    lines.append(f"Alignements déclarés : {summary['exact']} exact, {summary['close']} close")
    lines.extend(f"  {entry['kind']} : {_named(entry['concepts'][0])} = {_named(entry['concepts'][1])}"
                 for entry in report["alignments"])
    lines.append("Ponts candidats (même libellé normalisé ou même définition sous deux identifiants, "
                 f"non alignés) : {summary['candidates']}")
    lines.extend(f"  {_reasons(entry)} : {_named(entry['concepts'][0])} / {_named(entry['concepts'][1])}"
                 for entry in report["candidates"])
    lines.append("Doublons à l'intérieur d'une même taxonomie (même libellé ou même définition) : "
                 f"{summary['duplicates_in_taxonomy']}")
    lines.extend(f"  {_reasons(entry)} : {_named(entry['concepts'][0])} / {_named(entry['concepts'][1])}"
                 for entry in report["duplicates_in_taxonomy"])
    if report["pairs"]:
        lines.append("Par paire de taxonomies :")
        for pair, counts in report["pairs"].items():
            lines.append(
                f"  {pair} : partagés {counts['shared_concepts']}, prérequis {counts['cross_prerequisites']}, "
                f"exact {counts['exact']}, close {counts['close']}, candidats {counts['candidates']}"
            )
    else:
        lines.append("Par paire de taxonomies : aucun pont, déclaré ou candidat")
    return "\n".join(lines)
