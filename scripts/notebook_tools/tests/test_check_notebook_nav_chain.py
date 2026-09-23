"""Tests for scripts/notebook_tools/check_notebook_nav_chain.py — nav-chain reachability guard.

Why this test file exists
-------------------------
`check_notebook_navlinks.py` verifie que chaque cible de lien **existe** (404).
Il ne verifie pas que la chaine de navigation **atteint** chaque notebook : les
deux proprietes divergent exactement sur un notebook **insere** dont les voisins
pointent encore l'un vers l'autre. `12b` n'a alors aucun lien entrant, tous les
liens resolvent, le garde 404 est vert, et le notebook est inatteignable. C'est
la classe qui a laisse passer `QC-Py-12b`/`QC-Py-23c` (#17093), et qui est
**vivante** ailleurs dans le depot (`Sudoku-12b`, mesure du 2026-09-21).

Sept clusters :
  1. TestLooksNav — les TROIS portees du marqueur (lien / ligne / cellule) et
     les NON-aretes volontaires (prose, « voir aussi », parite de jumeaux).
     Chaque cas porte la mesure qui l'a fait adopter (cf le module).
  2. TestNavEdges — extraction : .ipynb seuls, cible existante seule, dedup,
     markdown seulement.
  3. TestBuildGraph — inbound/outbound/series + arete hors du set ignoree.
  4. TestAnalyse — les quatre jugements : chaine saine, notebook insere (la
     classe fondeuse), ilot detache, chaine bouclee, dossier non navigable.
  5. TestBaselineIO — ecriture/lecture deterministe, absent, JSON corrompu.
  6. TestMainModes — exit codes, --check NEW, --baseline.
  7. TestSeriesFilterRegression — l'epingle du bug « Path compare a une chaine »,
     qui rendait `--family` **silencieusement vide** (0 serie jugee, rc=0).
"""
import json
import sys
from pathlib import Path

import pytest

# import du module sous test (depuis le dossier parent)
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import check_notebook_nav_chain as cnc  # noqa: E402


def _nb(cells):
    """Notebook synthetique minimal (type, source) par cellule."""
    return {
        "cells": [{"cell_type": t, "source": s, "metadata": {}} for (t, s) in cells],
        "metadata": {}, "nbformat": 4, "nbformat_minor": 5,
    }


def _write(path: Path, cells):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(_nb(cells)), encoding="utf-8")
    return path


@pytest.fixture(autouse=True)
def _isolate_baseline(tmp_path, monkeypatch):
    """REPO_ROOT et BASELINE_PATH rediriges : jamais le depot reel en test.

    `_rel()` lit `REPO_ROOT` au moment de l'appel, donc le monkeypatch suffit et
    permet des chemins synthetiques sous tmp_path.
    """
    monkeypatch.setattr(cnc, "REPO_ROOT", tmp_path)
    # NOTEBOOKS_ROOT est calcule a l'import : `--family` fait un
    # `relative_to(NOTEBOOKS_ROOT)` sur les chemins du tmp_path, donc le
    # rederiger aussi, sinon ValueError au lieu d'un test.
    monkeypatch.setattr(cnc, "NOTEBOOKS_ROOT", tmp_path / "MyIA.AI.Notebooks")
    monkeypatch.setattr(cnc, "BASELINE_PATH", tmp_path / "baseline.json")
    return tmp_path


# ---------------------------------------------------------------- 1. portees

class TestLooksNav:
    """Les trois portees, et les non-aretes. Chaque cas vient d'une mesure."""

    def test_keyword_in_link_text(self):
        # Cas majoritaire : [Suivant >>](13-foo.ipynb)
        assert cnc._looks_nav("Suivant >>", "13-foo.ipynb", "x", False)

    def test_keyword_in_link_text_accented(self):
        assert cnc._looks_nav("Précédent", "12-foo.ipynb", "", False)

    def test_arrow_in_link_text(self):
        # MGS-07c : `[← MGS-7b LandscapeMultidim](...) · [MGS-8 ... →](...)`
        assert cnc._looks_nav("← MGS-7b LandscapeMultidim", "x.ipynb", "", False)
        assert cnc._looks_nav("MGS-8 LandscapeExplorer →", "y.ipynb", "", False)

    def test_marker_on_the_LINE_outside_the_link(self):
        # MGS-10 : `**Série MGS** | Précédent : [MGS-9 - Relief Everest](...)`
        # Le mot est hors du lien, et le texte du lien est le TITRE du voisin.
        line = "**Série MetaGeneticSharp** | Précédent : [MGS-9 - Relief Everest](MGS-09-x.ipynb) | [↑ Série MGS](README.md)"
        assert cnc._looks_nav("MGS-9 - Relief Everest", "MGS-09-x.ipynb", line, False)

    def test_marker_in_the_CELL_not_the_line(self):
        # Sudoku-06 : le bloc est une TABLE sous un titre, donc marqueur et liens
        # sont sur DEUX lignes. Portee ligne = faux orphelin mesure.
        assert cnc._looks_nav("Sudoku-05-PSO", "Sudoku-05-PSO-Csharp.ipynb", "table row", True)

    def test_prose_filename_in_backticks_is_not_an_edge(self):
        # GameTheory-24b : `Suite du banc toy \`GameTheory-24-Humour-Banc.ipynb\``
        assert not cnc._looks_nav("GameTheory-24-Humour-Banc.ipynb",
                                  "GameTheory-24-Humour-Banc.ipynb",
                                  "Suite du banc toy `GameTheory-24-Humour-Banc.ipynb`", False)

    def test_see_also_bullet_is_not_an_edge(self):
        # GameTheory-15 : liste « voir aussi » titree.
        line = "- [GameTheory-16 (Choix social / Mechanism Design)](GameTheory-16-MechanismDesign-Csharp.ipynb) : agregation"
        assert not cnc._looks_nav("GameTheory-16 (Choix social / Mechanism Design)",
                                  "GameTheory-16-MechanismDesign-Csharp.ipynb", line, False)

    def test_twin_parity_link_is_not_an_edge(self):
        # Search-03c : `| ↔ Python | [Search-03c — LDS (Python)](...) |` — parite
        # de jumeaux, pas chaine de navigation.
        line = "| ↔ Python | [Search-03c — LDS (Python)](Search-03c-LimitedDiscrepancySearch.ipynb) | jumeau |"
        assert not cnc._looks_nav("Search-03c — LDS (Python)",
                                  "Search-03c-LimitedDiscrepancySearch.ipynb", line, False)

    def test_weak_words_are_not_line_markers(self):
        # `index`/`prec`/`préc` sont exclus du scan de LIGNE (trop frequents en
        # prose) meme s'ils restent valides dans le texte du lien.
        assert not cnc._looks_nav("X", "x.ipynb", "l'index de la liste", False)
        assert not cnc._looks_nav("X", "x.ipynb", "plus precisement", False)


# ------------------------------------------------------------- 2. extraction

class TestNavEdges:
    def test_extracts_only_ipynb_targets(self, tmp_path):
        a = _write(tmp_path / "s" / "a.ipynb", [("markdown", "[Suivant](b.ipynb)\n[Index](R.md)")])
        _write(tmp_path / "s" / "b.ipynb", [("markdown", "x")])
        _write(tmp_path / "s" / "R.md", [("markdown", "x")])
        assert cnc.nav_edges(a) == [(tmp_path / "s" / "b.ipynb").resolve()]

    def test_missing_target_is_not_a_node(self, tmp_path):
        # Un 404 est le metier de check_notebook_navlinks.py, pas une arete.
        a = _write(tmp_path / "s" / "a.ipynb", [("markdown", "[Suivant](absent.ipynb)")])
        assert cnc.nav_edges(a) == []

    def test_code_cells_are_ignored(self, tmp_path):
        a = _write(tmp_path / "s" / "a.ipynb", [("code", "[Suivant](b.ipynb)")])
        _write(tmp_path / "s" / "b.ipynb", [("markdown", "x")])
        assert cnc.nav_edges(a) == []

    def test_dedup_and_source_as_string(self, tmp_path):
        a = _write(tmp_path / "s" / "a.ipynb",
                   [("markdown", "[Suivant](b.ipynb) [Suivant](b.ipynb)")])
        _write(tmp_path / "s" / "b.ipynb", [("markdown", "x")])
        assert len(cnc.nav_edges(a)) == 1

    def test_unreadable_notebook_yields_no_edge(self, tmp_path):
        p = tmp_path / "s" / "bad.ipynb"
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text("{ not json", encoding="utf-8")
        assert cnc.nav_edges(p) == []


# ---------------------------------------------------------------- 3. graphe

class TestBuildGraph:
    def test_inbound_outbound_and_series(self, tmp_path):
        a = _write(tmp_path / "s" / "a.ipynb", [("markdown", "[Suivant](b.ipynb)")])
        b = _write(tmp_path / "s" / "b.ipynb", [("markdown", "rien")])
        inbound, outbound, series = cnc.build_graph([a, b])
        assert outbound[a] == [b.resolve()]
        assert inbound[b.resolve()] == {a.resolve()}
        assert a.resolve() not in inbound
        assert len(series[a.parent]) == 2

    def test_edge_outside_the_node_set_is_ignored(self, tmp_path):
        a = _write(tmp_path / "s" / "a.ipynb", [("markdown", "[Suivant](b.ipynb)")])
        _write(tmp_path / "s" / "b.ipynb", [("markdown", "x")])
        inbound, outbound, _ = cnc.build_graph([a])  # b hors du set
        assert outbound[a] == []
        assert inbound == {}


# --------------------------------------------------------------- 4. analyse

def _chain(tmp_path, ids, links):
    """Cree une serie : `ids` = noms, `links` = {src: [dst, ...]}."""
    base = tmp_path / "MyIA.AI.Notebooks" / "Serie"
    paths = {}
    for i in ids:
        cells = [("markdown", "\n".join(f"[Suivant]({d}.ipynb)" for d in links.get(i, [])))]
        paths[i] = _write(base / f"{i}.ipynb", cells)
    return base, paths


class TestAnalyse:
    def test_healthy_single_entry_chain(self, tmp_path):
        # 01 -> 02 -> 03 : une seule entree, tout atteignable -> aucun finding.
        _, p = _chain(tmp_path, ["01", "02", "03"], {"01": ["02"], "02": ["03"]})
        inbound, outbound, series = cnc.build_graph(list(p.values()))
        r = cnc.analyse(inbound, outbound, series)
        assert r["findings"] == []
        assert r["series"][0]["entries"] == ["MyIA.AI.Notebooks/Serie/01.ipynb"]

    def test_inserted_notebook_is_flagged(self, tmp_path):
        # LA CLASSE FONDATRICE (#17093 / QC-Py-12b) : 02b insere entre 02 et 03,
        # mais 02 pointe encore 03 et 03 pointe encore 02 -> 02b sans lien entrant.
        _, p = _chain(tmp_path, ["01", "02", "02b", "03"],
                      {"01": ["02"], "02": ["03"], "03": ["02"]})
        inbound, outbound, series = cnc.build_graph(list(p.values()))
        r = cnc.analyse(inbound, outbound, series)
        flagged = [f["notebook"] for f in r["findings"] if f["kind"] == "orphan_entry"]
        assert "MyIA.AI.Notebooks/Serie/02b.ipynb" in flagged
        assert "MyIA.AI.Notebooks/Serie/01.ipynb" in flagged  # 2 entrees -> les deux

    def test_inserted_notebook_absent_once_linked_in(self, tmp_path):
        # L'ETAT CIBLE (le fix de #17277) : 02 -> 02b -> 03. Plus aucun finding.
        _, p = _chain(tmp_path, ["01", "02", "02b", "03"],
                      {"01": ["02"], "02": ["02b"], "02b": ["03"]})
        inbound, outbound, series = cnc.build_graph(list(p.values()))
        assert cnc.analyse(inbound, outbound, series)["findings"] == []

    def test_detached_island_head_is_an_orphan_entry(self, tmp_path):
        # 01 -> 02, et 07 -> 08 : 07 est une 2e entree (rien ne mene a lui).
        # 08, lui, est ATTEIGNABLE depuis l'entree 07 : il ne doit PAS etre
        # classe `unreachable`. Seule la tete de l'ilot est orpheline.
        _, p = _chain(tmp_path, ["01", "02", "07", "08"], {"01": ["02"], "07": ["08"]})
        inbound, outbound, series = cnc.build_graph(list(p.values()))
        r = cnc.analyse(inbound, outbound, series)
        kinds = {(f["kind"], f["notebook"].split("/")[-1]) for f in r["findings"]}
        assert ("orphan_entry", "07.ipynb") in kinds
        assert not any(k == "unreachable" for k, _ in kinds)

    def test_detached_cycle_is_unreachable(self, tmp_path):
        # 01 -> 02, et un cycle detache 07 <-> 08 : les deux ont un lien entrant
        # (donc aucune entree), et aucune entree ne les atteint -> inatteignables.
        _, p = _chain(tmp_path, ["01", "02", "07", "08"],
                      {"01": ["02"], "07": ["08"], "08": ["07"]})
        inbound, outbound, series = cnc.build_graph(list(p.values()))
        r = cnc.analyse(inbound, outbound, series)
        kinds = {(f["kind"], f["notebook"].split("/")[-1]) for f in r["findings"]}
        assert ("unreachable", "07.ipynb") in kinds
        assert ("unreachable", "08.ipynb") in kinds
        assert not any(k == "orphan_entry" for k, _ in kinds)

    def test_wrapped_chain_is_judged_not_excluded(self, tmp_path):
        # 01 -> 02 -> 03 -> 01 : AUCUNE entree. Convention legitime (le « suivant »
        # du dernier pointe le premier) : la serie est jugee, pas ecartee.
        _, p = _chain(tmp_path, ["01", "02", "03"],
                      {"01": ["02"], "02": ["03"], "03": ["01"]})
        inbound, outbound, series = cnc.build_graph(list(p.values()))
        r = cnc.analyse(inbound, outbound, series)
        assert r["findings"] == []
        assert len(r["wrapped"]) == 1
        assert r["series"][0]["wrapped"] is True

    def test_directory_without_internal_edge_is_not_judged(self, tmp_path):
        # Dossier de recherche : aucun lien de nav interne -> hors scope, COMPTE.
        _, p = _chain(tmp_path, ["r1", "r2"], {})
        inbound, outbound, series = cnc.build_graph(list(p.values()))
        r = cnc.analyse(inbound, outbound, series)
        assert r["findings"] == []
        assert r["not_judged"][0]["reason"] == "no_internal_nav_edge"

    def test_single_notebook_series_is_not_judged(self, tmp_path):
        _, p = _chain(tmp_path, ["solo"], {})
        inbound, outbound, series = cnc.build_graph(list(p.values()))
        r = cnc.analyse(inbound, outbound, series)
        assert r["findings"] == []
        assert r["not_judged"][0]["reason"] == "series_single_notebook"

    def test_findings_are_sorted_for_baseline_stability(self, tmp_path):
        _, p = _chain(tmp_path, ["01", "02", "02b", "03"],
                      {"01": ["02"], "02": ["03"], "03": ["02"]})
        inbound, outbound, series = cnc.build_graph(list(p.values()))
        f = cnc.analyse(inbound, outbound, series)["findings"]
        assert f == sorted(f, key=lambda x: (x["kind"], x["notebook"]))


# -------------------------------------------------------------- 5. baseline

class TestBaselineIO:
    def test_write_then_load_roundtrip(self, tmp_path):
        _, p = _chain(tmp_path, ["01", "02", "02b", "03"],
                      {"01": ["02"], "02": ["03"], "03": ["02"]})
        inbound, outbound, series = cnc.build_graph(list(p.values()))
        r = cnc.analyse(inbound, outbound, series)
        cnc._write_baseline(r)
        assert cnc._load_baseline() == cnc._finding_keys(r)

    def test_write_is_deterministic(self, tmp_path):
        _, p = _chain(tmp_path, ["01", "02", "02b", "03"],
                      {"01": ["02"], "02": ["03"], "03": ["02"]})
        inbound, outbound, series = cnc.build_graph(list(p.values()))
        r = cnc.analyse(inbound, outbound, series)
        cnc._write_baseline(r)
        first = cnc.BASELINE_PATH.read_bytes()
        cnc._write_baseline(r)
        assert cnc.BASELINE_PATH.read_bytes() == first

    def test_missing_baseline_is_empty(self):
        assert cnc._load_baseline() == set()

    def test_corrupted_baseline_is_empty(self):
        cnc.BASELINE_PATH.parent.mkdir(parents=True, exist_ok=True)
        cnc.BASELINE_PATH.write_text("{ pas du json", encoding="utf-8")
        assert cnc._load_baseline() == set()


# ------------------------------------------------------------------ 6. main

class TestMainModes:
    def _patch_iter(self, monkeypatch, paths):
        monkeypatch.setattr(cnc, "_iter_notebooks", lambda *a, **k: list(paths))

    def test_exit_1_on_findings_exit_0_when_healthy(self, tmp_path, monkeypatch):
        _, p = _chain(tmp_path, ["01", "02", "02b", "03"],
                      {"01": ["02"], "02": ["03"], "03": ["02"]})
        self._patch_iter(monkeypatch, p.values())
        assert cnc.main([]) == 1
        _, p2 = _chain(tmp_path / "h", ["01", "02"], {"01": ["02"]})
        self._patch_iter(monkeypatch, p2.values())
        assert cnc.main(["--quiet"]) == 0

    def test_check_flags_only_new_findings(self, tmp_path, monkeypatch):
        _, p = _chain(tmp_path, ["01", "02", "02b", "03"],
                      {"01": ["02"], "02": ["03"], "03": ["02"]})
        self._patch_iter(monkeypatch, p.values())
        assert cnc.main(["--baseline", "--quiet"]) == 0
        assert cnc.main(["--check", "--quiet"]) == 0
        # on casse une arete de plus -> un finding NEW
        _write(tmp_path / "MyIA.AI.Notebooks" / "Serie" / "04.ipynb",
               [("markdown", "rien")])
        self._patch_iter(monkeypatch, list(p.values()) +
                         [tmp_path / "MyIA.AI.Notebooks" / "Serie" / "04.ipynb"])
        assert cnc.main(["--check", "--quiet"]) == 1

    def test_unknown_notebook_is_exit_2(self, tmp_path, monkeypatch):
        self._patch_iter(monkeypatch, [])
        assert cnc.main([str(tmp_path / "nope.ipynb")]) == 2

    def test_json_output_shape(self, tmp_path, monkeypatch, capsys):
        _, p = _chain(tmp_path, ["01", "02", "02b", "03"],
                      {"01": ["02"], "02": ["03"], "03": ["02"]})
        self._patch_iter(monkeypatch, p.values())
        cnc.main(["--json"])
        out = json.loads(capsys.readouterr().out)
        assert out["total_findings"] == len(out["findings"]) > 0
        assert set(out) >= {"findings", "wrapped", "not_judged", "series", "scanned"}


# ------------------------------------------------- 7. epingle de regression

class TestSeriesFilterRegression:
    """Le filtre de serie comparait des `Path` a des chaines repo-relatives.

    Consequence mesuree : `--family Sudoku` rendait « 0 serie jugee », **rc=0** —
    un vert silencieux, le pire des verts, sur un rapport vide. Pin : le filtre
    doit selectionner la serie ET le rapport doit rester non vide.
    """

    def test_family_filter_selects_the_series(self, tmp_path, monkeypatch):
        _, p = _chain(tmp_path, ["01", "02", "02b", "03"],
                      {"01": ["02"], "02": ["03"], "03": ["02"]})
        monkeypatch.setattr(cnc, "_iter_notebooks", lambda *a, **k: list(p.values()))
        out = json.loads(_capture(cnc.main, ["--family", "Serie", "--json"]))
        assert out["total_findings"] > 0
        assert len(out["series"]) == 1

    def test_unknown_family_is_exit_2(self, tmp_path, monkeypatch):
        _, p = _chain(tmp_path, ["01", "02"], {"01": ["02"]})
        monkeypatch.setattr(cnc, "_iter_notebooks", lambda *a, **k: list(p.values()))
        assert cnc.main(["--family", "Inexistante", "--quiet"]) == 2


def _capture(fn, argv):
    """Capture stdout de `fn(argv)` (les tests de filtre en ont besoin)."""
    import io
    from contextlib import redirect_stdout
    buf = io.StringIO()
    with redirect_stdout(buf):
        fn(argv)
    return buf.getvalue()
