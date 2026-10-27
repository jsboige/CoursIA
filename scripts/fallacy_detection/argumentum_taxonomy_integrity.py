#!/usr/bin/env python3
"""Integrite structurelle de la taxonomie Argumentum vendorisee dans CoursIA.

POURQUOI CE SCRIPT EXISTE
-------------------------
La taxonomie des sophismes vendoree
(`MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/data/argumentum_fallacies_taxonomy.csv`)
est consommee par plusieurs carnets de la serie `Argument_Analysis` : la
construction des traces SFT (`argumentum_taxonomy_explorer.py`), les liens
croises du carnet `Argumentation-Onto-02-CrossLinks-CSV-Python.ipynb`, le
constructeur du dataset cartesien (`cartesian_dataset_builder.py`).

La garde existante (`tests/test_argumentum_snapshot_integrity.py`) certifie
l'**octet** : SHA1 de blob, nombre de lignes et de colonnes, familles
Virtues, assertions OWL. Elle certifie que la copie est celle du pin
declare -- mais elle ne certifie pas que la copie est **coherente avec
elle-meme**. Deux proprietes structurelles restent donc non verifiees :

1. **l'integrite referentielle** -- chaque cible d'une relation `crossLink_*`
   doit designer un noeud existant de l'arbre (un `path`), sinon le lien
   est muet dans tous les carnets qui le consomment ;
2. **la fermeture de l'arbre** -- chaque `path` non racine doit avoir un
   parent present dans le CSV, sinon une branche de la taxonomie est
   orpheline et le parcours de la hierarchie la perd.

Ce module etablit ces deux proprietes, les **mesure**, et les refute quand
elles cessent de tenir. Il ne reecrit rien : il mesure ce que le CSV
contient.

CE QUE LE MODULE MESURE
-----------------------
- le graphe des liens croises : nombre d'aretes, noeuds sources, couverture
  du corpus, degre sortant maximal et moyen ;
- la **reciprocite** par relation : une relation `Opposes` ou `Inverts` est
  censee etre bilateral, `IsRelatedTo` ne l'est pas par construction --
  le module mesure l'ecart plutot que de le supposer ;
- la coherence de la colonne `depth` avec le nombre de segments du `path`.

CONVENTIONS DE LECTURE
----------------------
- Le CSV est encode en UTF-8 **avec BOM** : il se lit en `utf-8-sig`.
- Une cellule `crossLink_*` peut porter **plusieurs cibles**, separees par
  `;` (40 cellules de la copie courante). Une cellule = une ou plusieurs
  aretes.
- La racine de la taxonomie porte le `path` `0` et un `depth` de `0` : elle
  est la seule exception legitime a la regle `depth == nombre de segments`.
- La coherence `depth == nombre de segments` est **exacte** : les ecarts
  admis sont **nommes** (`DEPTH_DEVIATION_ALLOWED`), tout ecart hors table
  est une anomalie. Une colonne `depth` vide vaut -1 et compte comme un
  ecart.

Point d'entree :

    python scripts/fallacy_detection/argumentum_taxonomy_integrity.py
    python scripts/fallacy_detection/argumentum_taxonomy_integrity.py --json

Hermetique : stdlib only, aucun acces reseau, aucun appel a git.
"""

from __future__ import annotations

import argparse
import csv
import json
import sys
from collections import Counter, defaultdict
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable, Sequence

HERE = Path(__file__).resolve().parent
# Recherche du repo root par les ancres plutot que par comptage de parents :
# le script peut vivre dans un clone (CoursIA) ou un worktree (CoursIA-<suffix>).
REPO = next(
    (p for p in HERE.parents if (p / "MyIA.AI.Notebooks").is_dir()),
    HERE.parent.parent.parent,
)
DATA_DIR = REPO / "MyIA.AI.Notebooks" / "SymbolicAI" / "Argument_Analysis" / "data"

#: Copie locale de la taxonomie des sophismes (verifie par le pin du manifeste).
FALLACIES_CSV = DATA_DIR / "argumentum_fallacies_taxonomy.csv"

#: Prefixe des colonnes de relations du graphe crossLink.
CROSSLINK_PREFIX = "crossLink_"

#: Separateur de cibles multiples dans une cellule `crossLink_*`.
TARGET_SEPARATOR = ";"

#: `path` de la racine de la taxonomie (seule exception a la regle de profondeur).
ROOT_PATH = "0"

#: Ecarts `depth` / nombre de segments **admis et nommes**, par cle primaire.
#: La copie amont porte une deviation documentee (PK 824, `path` a 6 segments
#: et `depth` a 7) : elle est nommee ici, donc toleree explicitement.
#:
#: La table remplace une tolerance en pourcentage : un taux admettrait une
#: corruption **localisee** -- une famille entiere decalee d'un niveau, le
#: cas realiste d'une resynchronisation amont -- que seule la corruption de
#: masse (des centaines de lignes) franchissait. Ici, tout ecart **hors
#: table** est une anomalie : la coherence doit etre exacte, pas statistique.
#: La valeur est le `depth` **attendu** : si l'amont corrige l'ecart, la
#: deviation disparait et l'exception devient sans effet ; s'il la modifie,
#: l'ecart ne correspond plus a l'attendu et rougit.
DEPTH_DEVIATION_ALLOWED: dict[str, int] = {"824": 7}


# ---------------------------------------------------------------------------
# Modele
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class Edge:
    """Une arete du graphe crossLink, de la source vers la cible.

    Attributes:
        source_pk: cle primaire de la source.
        source_path: `path` de la source (identifiant d'arete).
        relation: nom de la relation, sans le prefixe `crossLink_`.
        target_path: `path` de la cible.
    """

    source_pk: str
    source_path: str
    relation: str
    target_path: str


@dataclass(frozen=True)
class Invariant:
    """Un invariant structurel et son etat mesure.

    Attributes:
        name: identifiant court de l'invariant.
        ok: vrai si l'invariant tient sur les donnees mesurees.
        detail: mesure brute, en clair.
    """

    name: str
    ok: bool
    detail: str


# ---------------------------------------------------------------------------
# Lecture
# ---------------------------------------------------------------------------

def load_rows(path: Path | str = FALLACIES_CSV) -> list[dict[str, str]]:
    """Lit la taxonomie et rend ses lignes.

    Args:
        path: chemin du CSV (UTF-8 avec BOM).

    Returns:
        La liste des lignes, chaque ligne etant un dict `colonne -> valeur`.
    """
    source = Path(path)
    with source.open(encoding="utf-8-sig", newline="") as handle:
        return list(csv.DictReader(handle))


def relation_columns(rows: Sequence[dict[str, str]]) -> list[str]:
    """Liste les colonnes de relations, dans l'ordre du CSV.

    L'union est prise sur toutes les lignes : une colonne de relation
    presente sur une seule ligne serait sinon invisible.

    Args:
        rows: lignes de la taxonomie.

    Returns:
        Les noms de colonnes commencant par `crossLink_`.
    """
    columns: list[str] = []
    for row in rows:
        for column in row:
            if column.startswith(CROSSLINK_PREFIX) and column not in columns:
                columns.append(column)
    return columns


def parse_edges(rows: Sequence[dict[str, str]]) -> list[Edge]:
    """Extrait les aretes crossLink de la taxonomie.

    Une cellule peut porter plusieurs cibles separees par `;` : chacune
    devient une arete.

    Args:
        rows: lignes de la taxonomie.

    Returns:
        La liste des aretes, dans l'ordre de lecture du CSV.
    """
    edges: list[Edge] = []
    columns = relation_columns(rows)
    for row in rows:
        for column in columns:
            raw = (row.get(column) or "").strip()
            if not raw:
                continue
            for target in raw.split(TARGET_SEPARATOR):
                target = target.strip()
                if not target:
                    continue
                edges.append(
                    Edge(
                        source_pk=(row.get("PK") or "").strip(),
                        source_path=(row.get("path") or "").strip(),
                        relation=column[len(CROSSLINK_PREFIX):],
                        target_path=target,
                    )
                )
    return edges


# ---------------------------------------------------------------------------
# Mesure
# ---------------------------------------------------------------------------

def _parent_path(path: str) -> str:
    """Rend le `path` du parent d'un noeud de la taxonomie.

    Les sept familles de premier niveau portent un `path` d'un seul segment
    (`1` a `7`) : leur parent est la **racine** (`0`), pas une chaine vide.
    C'est la convention de l'explorateur de la serie, qui reparente les
    noeuds de profondeur 1 sous `0`.

    Args:
        path: `path` d'un noeud.

    Returns:
        Le `path` du parent.
    """
    parts = path.split(".")
    if len(parts) == 1:
        return ROOT_PATH
    return ".".join(parts[:-1])


def structural_profile(
    rows: Sequence[dict[str, str]],
    edges: Sequence[Edge] | None = None,
) -> dict[str, Any]:
    """Mesure la structure de la taxonomie et de son graphe crossLink.

    Args:
        rows: lignes de la taxonomie.
        edges: aretes deja extraites ; recalculees si absentes.

    Returns:
        Un dictionnaire de mesures : compte de noeuds, compte d'aretes,
        couverture, degre sortant, reciprocite par relation, et les
        anomalies structurelles (cibles non resolues, chemins orphelins,
        boucles directes, ecarts de profondeur).
    """
    edges = list(edges) if edges is not None else parse_edges(rows)
    paths = [(row.get("path") or "").strip() for row in rows]
    path_set = set(paths)

    pk_counts = Counter((row.get("PK") or "").strip() for row in rows)
    path_counts = Counter(paths)
    duplicate_pks = sorted(pk for pk, count in pk_counts.items() if count > 1)
    duplicate_paths = sorted(path for path, count in path_counts.items() if count > 1)

    dangling = sorted(
        {
            (edge.source_path, edge.relation, edge.target_path)
            for edge in edges
            if edge.target_path not in path_set
        }
    )
    orphans = sorted(
        {
            path
            for path in paths
            if path
            and path != ROOT_PATH
            and _parent_path(path) not in path_set
        }
    )
    self_loops = sorted(
        {
            (edge.source_path, edge.relation)
            for edge in edges
            if edge.target_path == edge.source_path
        }
    )

    depth_deviations: list[dict[str, Any]] = []
    for row in rows:
        path = (row.get("path") or "").strip()
        raw_depth = (row.get("depth") or "").strip()
        if not path or path == ROOT_PATH:
            continue
        segments = len(path.split("."))
        if not raw_depth:
            # Une colonne `depth` vide n'est pas une absence de donnee, c'est
            # une deviation : elle vaut -1 et elle est comptee comme les
            # autres. Ignorer la ligne laisserait passer, en vert, une
            # resynchronisation qui perd la colonne.
            depth = -1
        else:
            try:
                depth = int(raw_depth)
            except ValueError:
                depth = -1
        if depth != segments:
            depth_deviations.append(
                {"PK": (row.get("PK") or "").strip(), "path": path, "depth": depth, "segments": segments}
            )

    # Reciprocite : pour chaque relation, combien d'aretes (source, cible)
    # ont l'arete inverse (cible, source) **dans la meme relation**.
    by_source: dict[tuple[str, str], set[str]] = defaultdict(set)
    for edge in edges:
        by_source[(edge.source_path, edge.relation)].add(edge.target_path)

    relations: dict[str, dict[str, int]] = {}
    for column in relation_columns(rows):
        relation = column[len(CROSSLINK_PREFIX):]
        relation_edges = [edge for edge in edges if edge.relation == relation]
        sources = {edge.source_path for edge in relation_edges}
        reciprocal = sum(
            1
            for edge in relation_edges
            if edge.source_path in by_source.get((edge.target_path, relation), ())
        )
        relations[relation] = {
            "edges": len(relation_edges),
            "sources": len(sources),
            "reciprocal": reciprocal,
        }

    out_degree = Counter(edge.source_path for edge in edges)
    nodes_with_edges = len(out_degree)

    return {
        "nodes": len(rows),
        "columns": len(rows[0]) if rows else 0,
        "edges": len(edges),
        "nodes_with_edges": nodes_with_edges,
        "coverage": (nodes_with_edges / len(rows)) if rows else 0.0,
        "max_out_degree": max(out_degree.values(), default=0),
        "mean_out_degree": (len(edges) / nodes_with_edges) if nodes_with_edges else 0.0,
        "duplicate_pks": duplicate_pks,
        "duplicate_paths": duplicate_paths,
        "dangling_targets": dangling,
        "orphan_paths": orphans,
        "self_loops": self_loops,
        "depth_deviations": depth_deviations,
        "relations": relations,
    }


def check_invariants(profile: dict[str, Any]) -> list[Invariant]:
    """Confronte le profil mesure aux invariants structurels.

    Les invariants sont **independants du contenu** : ils portent sur la
    coherence interne du CSV, pas sur ses valeurs. Un CSV amont resynchronise
    les respecte tant que sa structure reste saine ; une copie abimee les
    viole.

    Args:
        profile: sortie de `structural_profile`.

    Returns:
        La liste des invariants et leur etat mesure.
    """
    unexpected_depth = [
        deviation
        for deviation in profile["depth_deviations"]
        if DEPTH_DEVIATION_ALLOWED.get(deviation["PK"]) != deviation["depth"]
    ]
    return [
        Invariant(
            "cles_primaires_uniques",
            not profile["duplicate_pks"],
            f"{len(profile['duplicate_pks'])} PK duplique(s)",
        ),
        Invariant(
            "chemins_uniques",
            not profile["duplicate_paths"],
            f"{len(profile['duplicate_paths'])} path duplique(s)",
        ),
        Invariant(
            "cibles_resolues",
            not profile["dangling_targets"],
            f"{len(profile['dangling_targets'])} cible(s) crossLink sans noeud",
        ),
        Invariant(
            "arbre_ferme",
            not profile["orphan_paths"],
            f"{len(profile['orphan_paths'])} path sans parent",
        ),
        Invariant(
            "absence_boucle_directe",
            not profile["self_loops"],
            f"{len(profile['self_loops'])} boucle(s) directe(s)",
        ),
        Invariant(
            "profondeur_coherente",
            not unexpected_depth,
            f"{len(unexpected_depth)} ecart(s) depth/segments hors table nommee "
            f"({len(profile['depth_deviations'])} ecart(s) au total, "
            f"{len(DEPTH_DEVIATION_ALLOWED)} admis)",
        ),
    ]


# ---------------------------------------------------------------------------
# Rendu
# ---------------------------------------------------------------------------

def format_report(profile: dict[str, Any]) -> str:
    """Met en forme le profil et les invariants sous forme de tableau texte.

    Args:
        profile: sortie de `structural_profile`.

    Returns:
        Le rapport, en texte.
    """
    lines = [
        "Taxonomie Argumentum -- profil structurel",
        "=" * 46,
        f"noeuds (sophismes)      : {profile['nodes']}",
        f"colonnes                : {profile['columns']}",
        f"aretes crossLink        : {profile['edges']}",
        f"noeuds portant un lien  : {profile['nodes_with_edges']} "
        f"({100 * profile['coverage']:.1f} % du corpus)",
        f"degre sortant maximal   : {profile['max_out_degree']}",
        f"degre sortant moyen     : {profile['mean_out_degree']:.2f}",
        "",
        f"{'relation':<14}{'aretes':>8}{'sources':>10}{'reciproques':>14}{'taux':>8}",
        "-" * 54,
    ]
    for relation, stats in profile["relations"].items():
        rate = 100 * stats["reciprocal"] / stats["edges"] if stats["edges"] else 0.0
        lines.append(
            f"{relation:<14}{stats['edges']:>8}{stats['sources']:>10}"
            f"{stats['reciprocal']:>14}{rate:>7.0f} %"
        )
    lines += [
        "",
        "Anomalies",
        "---------",
        f"cibles non resolues   : {len(profile['dangling_targets'])}",
        f"chemins orphelins      : {len(profile['orphan_paths'])}",
        f"boucles directes       : {len(profile['self_loops'])}",
        f"ecarts depth/segments  : {len(profile['depth_deviations'])} "
        f"({len(DEPTH_DEVIATION_ALLOWED)} admis par la table nommee)",
    ]
    for deviation in profile["depth_deviations"]:
        admitted = DEPTH_DEVIATION_ALLOWED.get(deviation["PK"]) == deviation["depth"]
        status = "admis" if admitted else "HORS TABLE"
        lines.append(
            f"    PK {deviation['PK']:<6} path {deviation['path']:<16} "
            f"depth {deviation['depth']} / {deviation['segments']} segments  [{status}]"
        )
    lines += ["", "Invariants", "----------"]
    for invariant in check_invariants(profile):
        lines.append(
            f"[{'OK ' if invariant.ok else 'ROUGE'}] {invariant.name:<26} {invariant.detail}"
        )
    return "\n".join(lines)


def main(argv: Iterable[str] | None = None) -> int:
    """Point d'entree : mesure la taxonomie et affiche le profil.

    Args:
        argv: arguments de la ligne de commande.

    Returns:
        0 si tous les invariants tiennent, 1 sinon.
    """
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument(
        "--csv",
        default=str(FALLACIES_CSV),
        help="chemin de la taxonomie des sophismes (defaut : copie locale du depot)",
    )
    parser.add_argument("--json", action="store_true", help="sortie machine")
    args = list(sys.argv[1:] if argv is None else argv)
    parsed = parser.parse_args(args)

    rows = load_rows(parsed.csv)
    profile = structural_profile(rows)
    invariants = check_invariants(profile)

    if parsed.json:
        printable = dict(profile)
        printable["invariants"] = [
            {"name": inv.name, "ok": inv.ok, "detail": inv.detail} for inv in invariants
        ]
        print(json.dumps(printable, indent=2, ensure_ascii=False))
    else:
        print(format_report(profile))

    return 0 if all(inv.ok for inv in invariants) else 1


if __name__ == "__main__":  # pragma: no cover - point d'entree CLI
    raise SystemExit(main())
