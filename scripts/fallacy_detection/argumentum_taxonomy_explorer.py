#!/usr/bin/env python3
"""Native Argumentum taxonomy explorer + SFT trace generator (EPIC #10355, Phase 2).

This module replicates, in native CoursIA code, the **method** of the 6
``@kernel_function`` exposed by the EPITA ``argumentation_lib`` plugin (the
``InformalAnalysisPlugin`` tree-descent over the Argumentum fallacy taxonomy).

Why a native replica (and not "make the plugin importable")
-----------------------------------------------------------
The plugin lives under
``MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/argumentation_lib/`` as a
**verbatim vendored copy** of the EPITA ``2025-Epita-Intelligence-Symbolique``
project (see ``NOTICE-EPITA``).  Every file carries the covenant::

    Verbatim integrity: byte-for-byte identical to the upstream source.
    No CoursIA modification.

Firsthand reproduction (po-2025, origin/main 9afa66abd) shows the plugin is
**NOT runtime-importable** today, for two distinct reasons -- neither fixable
in-repo without breaking the verbatim covenant:

1. ``_taxonomy_sophism_detector.py`` line 40 does
   ``from .informal_definitions import InformalAnalysisPlugin``.  Upstream the
   sibling module is ``informal_definitions.py``; the CoursIA vendoring renamed
   it to ``_informal_definitions.py`` (private convention) but cannot update the
   cross-reference inside the byte-for-byte copy.  The file header documents
   this: *"NOT standalone-importable today; use the lazy accessor"*.
2. ``_informal_definitions.py`` internally imports the upstream package path
   ``argumentation_analysis.core.utils.file_loaders``, which is not vendored in
   this tranche ("wait for Volet B etape 4").

The owner's framing of the EPIC resolves the tension cleanly:
*« le plugin est la cible de comportement, pas une dependance d'execution »*
(the plugin is the **behaviour target**, not an execution dependency) and the
PT goal is *« que le modele fasse le travail que le plugin fait actuellement
fait, tout seul, dans son thinking »*.  The **method** to internalise is the
hierarchical tree-descent: *« on part du general, et on descend dans l'arbre »*.

This module therefore reproduces that method natively, operating directly on the
repo-local taxonomy CSV (``argumentum_fallacies_taxonomy.csv``, 1408 nodes),
with **zero edits to vendored files**.  It produces the SFT seed traces the
EPIC needs ("sans generateur de traces, pas de seed SFT") by exercising the 6
operations on the real 1408-node tree.

The 6 operations (mirroring the ``@kernel_function`` names/signatures):
    list_fallacy_categories  -> unique families
    list_fallacies_in_category(category) -> leaves of a family
    explore_fallacy_hierarchy(pk, max_children) -> children of a node
    find_fallacy_definition(name) -> lookup by FR/Latin name
    get_fallacy_details(pk) -> full record by PK
    get_fallacy_example(name) -> worked example by name

Usage::

    python -m fallacy_detection.argumentum_taxonomy_explorer --report
    python -m fallacy_detection.argumentum_taxonomy_explorer --list-categories
    python -m fallacy_detection.argumentum_taxonomy_explorer --out-traces traces.jsonl
"""
from __future__ import annotations

import argparse
import csv
import json
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Optional

_REPO_ROOT = Path(__file__).resolve().parents[2]
_DEFAULT_TAXO = _REPO_ROOT / (
    "MyIA.AI.Notebooks/SymbolicAI/Argument_Analysis/"
    "data/argumentum_fallacies_taxonomy.csv"
)

# The root node (PK 0, "Argument fallacieux") is the whole-tree anchor, not a
# fallacy family.  The plugin's list_fallacy_categories returns the unique
# ``Famille`` values; we keep the root out of the SFT-exploration targets but
# preserve it for hierarchy ascent.
_ROOT_PK = 0
_ROOT_NAME = "Argument fallacieux"


@dataclass
class TaxonomyNode:
    """One row of the Argumentum taxonomy."""

    pk: int
    path: str
    depth: int
    famille: str
    nom_vulgarise: str
    latin: str
    text_fr: str
    desc_fr: str
    example_fr: str
    text_en: str
    simple_name_en: str
    desc_en: str
    example_en: str

    @classmethod
    def from_row(cls, row: dict) -> "TaxonomyNode":
        def g(k: str) -> str:
            return (row.get(k) or "").strip()

        pk_raw = g("PK")
        depth_raw = g("depth")
        return cls(
            pk=int(pk_raw) if pk_raw.isdigit() else -1,
            path=g("path"),
            depth=int(depth_raw) if depth_raw.isdigit() else -1,
            famille=g("Famille"),
            nom_vulgarise=g("nom_vulgarisé") or g("text_fr"),
            latin=g("Latin"),
            text_fr=g("text_fr"),
            desc_fr=g("desc_fr"),
            example_fr=g("example_fr"),
            text_en=g("text_en"),
            simple_name_en=g("Simple_name_en"),
            desc_en=g("desc_en"),
            example_en=g("example_en"),
        )

    @property
    def display_name(self) -> str:
        """The name shown in traces -- vulgarised FR, fallback to text_fr."""
        return self.nom_vulgarise or self.text_fr

    @property
    def is_root(self) -> bool:
        return self.pk == _ROOT_PK


def _load_nodes(csv_path: Path) -> list[TaxonomyNode]:
    """Load the taxonomy CSV (BOM-tolerant) into TaxonomyNode list."""
    # utf-8-sig strips a leading BOM if present.
    with open(csv_path, encoding="utf-8-sig", newline="") as f:
        return [TaxonomyNode.from_row(r) for r in csv.DictReader(f)]


class ArgumentumTaxonomy:
    """Native replica of the plugin's hierarchical fallacy-exploration method.

    The tree is encoded by the dotted ``path`` column (e.g. ``1.2.3``); a node's
    children are the rows whose ``path`` equals ``<parent.path>.<segment>`` at
    depth ``parent.depth + 1``.  This mirrors the plugin's
    ``_internal_explore_hierarchy`` semantics (general -> leaf descent).
    """

    def __init__(self, nodes: list[TaxonomyNode]):
        self._nodes = nodes
        self._by_pk: dict[int, TaxonomyNode] = {n.pk: n for n in nodes if n.pk >= 0}
        # children indexed by parent path for O(1) descent.
        self._children_by_parent_path: dict[str, list[TaxonomyNode]] = {}
        for n in nodes:
            if "." in n.path:
                parent_path = n.path.rsplit(".", 1)[0]
                self._children_by_parent_path.setdefault(parent_path, []).append(n)
            elif n.path and n.pk != _ROOT_PK:
                # depth-1 nodes have the root as parent.
                self._children_by_parent_path.setdefault("0", []).append(n)
        # keep children deterministic (CSV order, which is pre-ordered).
        for v in self._children_by_parent_path.values():
            v.sort(key=lambda n: n.pk)

    # -- factory --

    @classmethod
    def from_csv(cls, csv_path: Path) -> "ArgumentumTaxonomy":
        return cls(_load_nodes(csv_path))

    # -- the 6 @kernel_function replicas -----------------------------

    def list_fallacy_categories(self) -> list[str]:
        """Replica of ``list_fallacy_categories``: unique families, root excluded.

        The plugin returns ``df["Famille"].dropna().unique()`` which includes the
        root "Argument fallacieux"; for the SFT-exploration *method* (general ->
        leaf) the meaningful top-level targets are the 8 real families, so we
        exclude the root anchor here and expose it via ``root``.
        """
        seen: list[str] = []
        for n in self._nodes:
            if n.is_root or not n.famille:
                continue
            if n.famille not in seen:
                seen.append(n.famille)
        return seen

    def list_fallacies_in_category(self, category: str) -> list[dict]:
        """Replica of ``list_fallacies_in_category``: members of a family.

        Returns ``[{"pk": int, "nom_vulgarise": str}, ...]`` -- the plugin's
        projection (pk + vulgarised name), for the family's *leaves* (nodes with
        no children), which are the identifiable fallacies.
        """
        out: list[dict] = []
        for n in self._nodes:
            if n.famille == category and not self._children_by_parent_path.get(
                n.path
            ):
                out.append({"pk": n.pk, "nom_vulgarise": n.display_name})
        return out

    def explore_fallacy_hierarchy(
        self, current_pk: int, max_children: int = 15
    ) -> dict:
        """Replica of ``explore_fallacy_hierarchy``: children of a node.

        Returns ``{"current": {...}, "children": [...]}`` truncated to
        ``max_children`` (the plugin's default).  This is the core of the
        tree-descent *method*: from a general node, reveal its sub-nodes.
        """
        node = self._by_pk.get(current_pk)
        if node is None:
            return {"error": f"PK inconnu: {current_pk}"}
        children = self._children_by_parent_path.get(node.path, [])
        return {
            "current": {
                "pk": node.pk,
                "path": node.path,
                "nom_vulgarise": node.display_name,
                "desc_fr": node.desc_fr,
            },
            "children": [
                {"pk": c.pk, "path": c.path, "nom_vulgarise": c.display_name}
                for c in children[:max_children]
            ],
            "children_total": len(children),
        }

    def find_fallacy_definition(self, fallacy_name: str) -> dict:
        """Replica of ``find_fallacy_definition``: match on FR name or Latin.

        The plugin matches ``nom_vulgarisé | text_fr | latin`` (case-insensitive,
        substring).  We replicate that triple-channel lookup and return the
        definition (``desc_fr``).
        """
        needle = fallacy_name.strip().lower()
        if not needle:
            return {"error": "Nom vide."}
        for n in self._nodes:
            haystacks = (n.nom_vulgarise, n.text_fr, n.latin)
            if any(needle in (h or "").lower() for h in haystacks):
                return {
                    "pk": n.pk,
                    "nom_vulgarise": n.display_name,
                    "desc_fr": n.desc_fr or "Définition non disponible.",
                    "matched_in": next(
                        field
                        for field, h in zip(
                            ("nom_vulgarisé", "text_fr", "Latin"), haystacks
                        )
                        if needle in (h or "").lower()
                    ),
                }
        return {"error": f"Aucun sophisme trouvé pour '{fallacy_name}'."}

    def get_fallacy_details(self, fallacy_pk: int) -> dict:
        """Replica of ``get_fallacy_details``: full record by PK."""
        node = self._by_pk.get(fallacy_pk)
        if node is None:
            return {"error": f"PK inconnu: {fallacy_pk}"}
        return {
            "pk": node.pk,
            "path": node.path,
            "famille": node.famille,
            "nom_vulgarise": node.display_name,
            "latin": node.latin,
            "desc_fr": node.desc_fr,
            "simple_name_en": node.simple_name_en,
            "desc_en": node.desc_en,
        }

    def get_fallacy_example(self, fallacy_name: str) -> dict:
        """Replica of ``get_fallacy_example``: worked example by name."""
        needle = fallacy_name.strip().lower()
        if not needle:
            return {"error": "Nom vide."}
        for n in self._nodes:
            if needle in (n.nom_vulgarise or "").lower() or needle in (
                n.text_fr or ""
            ).lower():
                return {
                    "pk": n.pk,
                    "nom_vulgarise": n.display_name,
                    "example_fr": n.example_fr or "Exemple non disponible.",
                }
        return {"error": f"Aucun exemple trouvé pour '{fallacy_name}'."}

    # -- SFT trace generation ----------------------------------------

    @dataclass
    class SFTTrace:
        """One supervised-fine-tuning trace (prompt -> response)."""

        prompt: str
        response: str
        operation: str
        node_pk: Optional[int] = None

    def generate_sft_traces(
        self, per_family_leaves: int = 3, hierarchy_depth: int = 3
    ) -> list["ArgumentumTaxonomy.SFTTrace"]:
        """Generate SFT seed traces exercising the tree-descent *method*.

        The traces teach the model the behaviour the plugin currently performs:
        (1) list the top-level families, (2) descend a family, (3) drill a
        hierarchy path general->leaf, (4) look up a definition, (5) retrieve an
        example.  Each trace is a (natural-language prompt, structured JSON
        response) pair grounded in the **real** 1408-node taxonomy -- the
        falsifiable artefact the EPIC's seed SFT needs.

        ``per_family_leaves`` caps the leaf-level traces per family (keeps the
        seed set balanced across the 8 families rather than dominated by
        ``Influence``/``Tricherie``); ``hierarchy_depth`` caps the depth of the
        descent traces.
        """
        traces: list[ArgumentumTaxonomy.SFTTrace] = []

        # (1) Top-level: list categories.
        cats = self.list_fallacy_categories()
        traces.append(
            self.SFTTrace(
                operation="list_fallacy_categories",
                prompt="Quelles sont les grandes familles de sophismes de la taxonomie Argumentum ?",
                response=json.dumps({"categories": cats}, ensure_ascii=False),
            )
        )

        # (2)+(3)+(4)+(5): per family, descend + sample leaves + definition +
        # example.
        for cat in cats:
            members = self.list_fallacies_in_category(cat)
            if not members:
                continue
            # (2) list the family's fallacies.
            traces.append(
                self.SFTTrace(
                    operation="list_fallacies_in_category",
                    node_pk=members[0]["pk"],
                    prompt=(
                        f"Liste les sophismes appartenant à la famille « {cat} »."
                    ),
                    response=json.dumps(
                        {"category": cat, "fallacies": members}, ensure_ascii=False
                    ),
                )
            )
            # (3) hierarchy descent on the family root (first node of the family).
            family_root = next(
                (n for n in self._nodes if n.famille == cat and not n.is_root), None
            )
            if family_root is not None:
                descent = self._descent_chain(family_root.pk, hierarchy_depth)
                for step in descent:
                    traces.append(
                        self.SFTTrace(
                            operation="explore_fallacy_hierarchy",
                            node_pk=step["current"]["pk"],
                            prompt=(
                                f"Explore la hiérarchie des sophismes depuis le nœud "
                                f"« {step['current']['nom_vulgarise']} » (PK {step['current']['pk']})."
                            ),
                            response=json.dumps(step, ensure_ascii=False),
                        )
                    )
            # (4)+(5) definition + example on a sample of leaves.
            for m in members[:per_family_leaves]:
                node = self._by_pk.get(m["pk"])
                if node is None:
                    continue
                name = node.display_name
                traces.append(
                    self.SFTTrace(
                        operation="find_fallacy_definition",
                        node_pk=node.pk,
                        prompt=f"Donne la définition du sophisme « {name} ».",
                        response=json.dumps(
                            {
                                "pk": node.pk,
                                "nom_vulgarise": name,
                                "desc_fr": node.desc_fr
                                or "Définition non disponible.",
                            },
                            ensure_ascii=False,
                        ),
                    )
                )
                traces.append(
                    self.SFTTrace(
                        operation="get_fallacy_example",
                        node_pk=node.pk,
                        prompt=f"Donne un exemple illustrant le sophisme « {name} ».",
                        response=json.dumps(
                            {
                                "pk": node.pk,
                                "nom_vulgarise": name,
                                "example_fr": node.example_fr
                                or "Exemple non disponible.",
                            },
                            ensure_ascii=False,
                        ),
                    )
                )
        return traces

    def _descent_chain(self, root_pk: int, max_depth: int) -> list[dict]:
        """Walk a single general->leaf path, returning the explore_* payload per step."""
        chain: list[dict] = []
        pk = root_pk
        for _ in range(max_depth):
            step = self.explore_fallacy_hierarchy(pk)
            if "error" in step or not step.get("children"):
                break
            chain.append(step)
            pk = step["children"][0]["pk"]  # descend the first child.
        return chain

    # -- reporting ---------------------------------------------------

    def coverage_report(self) -> dict:
        leaves = [
            n
            for n in self._nodes
            if not self._children_by_parent_path.get(n.path) and not n.is_root
        ]
        families = self.list_fallacy_categories()
        per_family = {
            f: len(self.list_fallacies_in_category(f)) for f in families
        }
        return {
            "total_nodes": len(self._nodes),
            "families": families,
            "family_count": len(families),
            "leaves": len(leaves),
            "leaves_per_family": per_family,
        }


def main(argv: Optional[list[str]] = None) -> int:
    p = argparse.ArgumentParser(
        description="Native Argumentum taxonomy explorer (EPIC #10355 Phase 2)."
    )
    p.add_argument(
        "--taxonomy",
        type=Path,
        default=_DEFAULT_TAXO,
        help="Path to argumentum_fallacies_taxonomy.csv",
    )
    p.add_argument("--list-categories", action="store_true")
    p.add_argument("--explore-pk", type=int, metavar="PK", help="Explore hierarchy at PK.")
    p.add_argument("--report", action="store_true", help="Print coverage report.")
    p.add_argument(
        "--out-traces",
        type=Path,
        metavar="PATH",
        help="Write SFT traces as JSONL to PATH.",
    )
    p.add_argument(
        "--per-family-leaves",
        type=int,
        default=3,
        help="Leaves sampled per family for traces (default 3).",
    )
    args = p.parse_args(argv)

    if not args.taxonomy.is_file():
        print(f"ERREUR: taxonomie introuvable: {args.taxonomy}", file=sys.stderr)
        return 2

    taxo = ArgumentumTaxonomy.from_csv(args.taxonomy)

    if args.list_categories:
        for c in taxo.list_fallacy_categories():
            print(c)
        return 0

    if args.explore_pk is not None:
        print(
            json.dumps(
                taxo.explore_fallacy_hierarchy(args.explore_pk),
                ensure_ascii=False,
                indent=2,
            )
        )
        return 0

    if args.report:
        rep = taxo.coverage_report()
        print("=== Couverture taxonomie Argumentum ===")
        print(f"  noeuds total : {rep['total_nodes']}")
        print(f"  familles     : {rep['family_count']} -> {rep['families']}")
        print(f"  feuilles     : {rep['leaves']}")
        print("  par famille  :")
        for fam, n in rep["leaves_per_family"].items():
            print(f"    {fam:<28} {n}")

    if args.out_traces:
        traces = taxo.generate_sft_traces(
            per_family_leaves=args.per_family_leaves
        )
        args.out_traces.parent.mkdir(parents=True, exist_ok=True)
        with open(args.out_traces, "w", encoding="utf-8") as f:
            for t in traces:
                f.write(
                    json.dumps(
                        {
                            "operation": t.operation,
                            "node_pk": t.node_pk,
                            "prompt": t.prompt,
                            "response": t.response,
                        },
                        ensure_ascii=False,
                    )
                    + "\n"
                )
        by_op: dict[str, int] = {}
        for t in traces:
            by_op[t.operation] = by_op.get(t.operation, 0) + 1
        print(f"\n=== Traces SFT generees : {len(traces)} ===")
        for op, n in sorted(by_op.items()):
            print(f"  {op:<28} {n}")
        print(f"  ecrites dans : {args.out_traces}")

    if not any(
        (args.list_categories, args.explore_pk is not None, args.report, args.out_traces)
    ):
        # default: print the coverage report.
        rep = taxo.coverage_report()
        print(
            f"Taxonomie: {rep['total_nodes']} noeuds, {rep['family_count']} familles, "
            f"{rep['leaves']} feuilles.  Utilisez --report / --list-categories / "
            f"--explore-pk PK / --out-traces PATH."
        )
    return 0


if __name__ == "__main__":
    sys.exit(main())
