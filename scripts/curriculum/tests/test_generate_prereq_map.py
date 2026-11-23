#!/usr/bin/env python3
"""Temoins des fonctions pures du generateur de carte des prerequis (#27657).

`derive_edges`, `dec_key` et `flowchart_direction` sont pures : les tests les
exercent sur une taxonomie MINIATURE construite a la main, dans la forme exacte
que `load_series` produit (dicts simples, cles identiques) -- aucune lecture
disque, aucun reseau, aucune dependance a l'etat de `main`.

Ce que chaque temoin protege :
- **derive_edges** : le sens de l'arete (A -> B = A enseigne un prerequis de
  B), le poids, les references non resolues (comptees, pas jetees), les aretes
  inter-series, et l'absence d'arete quand les deux notions vivent dans le
  meme carnet ;
- **dec_key** : le tri NUMERQUE des chemis decimaux (1.10 apres 1.2), la
  robustesse au vide ;
- **flowchart_direction** : l'orientation choisie selon la largeur du rang le
  plus large (LR au-dela de 3, TB sinon -- frontiere incluse).

Run: python -m pytest scripts/curriculum/tests/test_generate_prereq_map.py -q
"""
from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "scripts" / "curriculum"))

import generate_prereq_map as gpm  # noqa: E402


def _concept(cid: str, prereqs: list[str], nbs: list[str]) -> dict:
    """Concept miniature : id, prerequisites, citations de carnets."""
    return {
        "id": cid,
        "path": f"mini.{cid}",
        "label_fr": f"Concept {cid}",
        "prerequisites": prereqs,
        "citations": [{"notebook": nb} for nb in nbs],
    }


def _series(key: str, concepts: list[dict]) -> dict:
    """Serie miniature dans la forme EXACTE de load_series (memes cles)."""
    series = {
        "key": key,
        "name": key,
        "notebooks": [],
        "tree": [],
        "concepts": concepts,
        "taught": {},
        "concepts_in_nb": {},
    }
    for concept in concepts:
        seen: set[str] = set()
        for citation in concept.get("citations") or []:
            nb = citation.get("notebook")
            if not nb:
                continue
            nb = nb.replace("\\", "/")
            series["taught"].setdefault(concept["id"], {})[nb] = True
            if nb not in seen:
                seen.add(nb)
                series["concepts_in_nb"].setdefault(nb, []).append(concept["label_fr"])
    return series


def _index(series_list: list[dict]) -> tuple[dict, dict]:
    """Index by_id / by_path, meme construction que load_series."""
    by_id: dict = {}
    by_path: dict = {}
    for series in series_list:
        for concept in series["concepts"]:
            if concept.get("id"):
                by_id[concept["id"]] = (series, concept)
            if concept.get("path"):
                by_path[concept["path"]] = (series, concept)
    return by_id, by_path


class TestDeriveEdges:
    def test_arete_sens_prequis_vers_consommateur(self):
        """A -> B : A enseigne un prerequis requis par B, jamais l'inverse."""
        concepts = [
            _concept("sat", [], ["serie/nb01-Sat.ipynb"]),
            _concept("dpll", ["sat"], ["serie/nb02-Dpll.ipynb"]),
        ]
        series = _series("mini", concepts)
        by_id, by_path = _index([series])
        edges, cross, unresolved, total_refs = gpm.derive_edges([series], by_id, by_path)
        assert edges == {("serie/nb01-Sat.ipynb", "serie/nb02-Dpll.ipynb"): 1}
        assert cross == []
        assert unresolved == 0
        assert total_refs == 1

    def test_reference_non_resolue_comptee_pas_jetee(self):
        """Une prerequis d'id inconnu augmente unresolved SANS creer d'arete."""
        concepts = [
            _concept("dpll", ["concept-fantome"], ["serie/nb02-Dpll.ipynb"]),
        ]
        series = _series("mini", concepts)
        by_id, by_path = _index([series])
        edges, cross, unresolved, total_refs = gpm.derive_edges([series], by_id, by_path)
        assert edges == {}
        assert unresolved == 1
        assert total_refs == 1

    def test_resolution_par_chemin_quand_id_absent(self):
        """Un prerequis cite par `path` resout via by_path (repli de load_series)."""
        concepts = [
            _concept("sat", [], ["serie/nb01-Sat.ipynb"]),
            _concept("dpll", ["mini.sat"], ["serie/nb02-Dpll.ipynb"]),
        ]
        series = _series("mini", concepts)
        by_id, by_path = _index([series])
        # by_id est vide : l'identifiant "sat" n'est pas indexe, seul le chemin l'est.
        edges, _cross, unresolved, _total = gpm.derive_edges([series], {}, by_path)
        assert edges == {("serie/nb01-Sat.ipynb", "serie/nb02-Dpll.ipynb"): 1}
        assert unresolved == 0

    def test_meme_carnet_pas_d_arete(self):
        """Deux notions co-enseignees dans un meme carnet ne font pas de boucle."""
        concepts = [
            _concept("sat", [], ["serie/nb01.ipynb"]),
            _concept("dpll", ["sat"], ["serie/nb01.ipynb"]),
        ]
        series = _series("mini", concepts)
        by_id, by_path = _index([series])
        edges, _cross, _unresolved, _total = gpm.derive_edges([series], by_id, by_path)
        assert edges == {}

    def test_poids_cumule_et_arete_inter_series(self):
        """Deux prerequis partages cumulent le poids ; cross-series est nomme."""
        serie_a = _series("alpha", [
            _concept("sat", [], ["alpha/nb01.ipynb"]),
            _concept("cnf", [], ["alpha/nb01.ipynb"]),
        ])
        serie_b = _series("beta", [
            _concept("dpll", ["sat", "cnf"], ["beta/nb05.ipynb"]),
        ])
        by_id, by_path = _index([serie_a, serie_b])
        edges, cross, unresolved, total_refs = gpm.derive_edges([serie_a, serie_b], by_id, by_path)
        assert edges == {("alpha/nb01.ipynb", "beta/nb05.ipynb"): 2}
        assert len(cross) == 2
        assert all(c["from"] == "alpha/nb01.ipynb" and c["to"] == "beta/nb05.ipynb" for c in cross)
        assert unresolved == 0
        assert total_refs == 2


class TestDecKey:
    def test_tri_numerique_1_10_apres_1_2(self):
        """Le piege du tri de chaines : 1.10 doit ranger apres 1.2."""
        chemins = ["1.10", "1.2", "1.9"]
        assert sorted(chemins, key=gpm.dec_key) == ["1.2", "1.9", "1.10"]

    def test_chemin_vide_est_neutre(self):
        assert gpm.dec_key("") == ()
        assert gpm.dec_key(None) == ()

    def test_profondeurs_distinctes(self):
        assert gpm.dec_key("2") == (2,)
        assert gpm.dec_key("2.1.3") == (2, 1, 3)


class TestFlowchartDirection:
    def test_chaine_verticale_tb(self):
        """Une chaine (rangs de largeur 1) se lit en TB."""
        nodes = ["a", "b", "c"]
        edges = [("a", "b"), ("b", "c")]
        assert gpm.flowchart_direction(nodes, edges) == "TB"

    def test_rang_large_lr(self):
        """Quatre noeuds au meme rang : LR les empile, TB les aligne."""
        nodes = ["a", "b", "c", "d"]
        assert gpm.flowchart_direction(nodes, []) == "LR"

    def test_frontiere_inclusive_trois_rangs_tb(self):
        """Trois noeuds au meme rang restent lisibles en TB (strictement > 3 -> LR)."""
        nodes = ["a", "b", "c"]
        assert gpm.flowchart_direction(nodes, []) == "TB"
        assert gpm.flowchart_direction(nodes + ["d"], []) == "LR"

    def test_graphe_vide_ne_plante_pas(self):
        assert gpm.flowchart_direction([], []) == "TB"
