"""Tests du graphe de dependances d'un lake (#21641, pli 6 Origami Wolfram)."""

from __future__ import annotations

import sys
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "lean" / "lemma_dependency_graph.py"


def _load():
    sys.path.insert(0, str(SCRIPT.parent))
    import lemma_dependency_graph as mod  # noqa: WPS433
    return mod


def test_parse_imports_extracts_module_names() -> None:
    """Chaque ligne `import X.Y` rend son nom ; le reste est ignore."""
    mod = _load()
    source = (
        "import Conway.Life.Basic\n"
        "/- commentaire -/\n"
        "import Mathlib.Data.Nat.Basic\n"
        "  import Conway.Life.MacroCell  \n"
        "theorem foo := by sorry  -- pas un import\n"
    )
    assert mod.parse_imports(source) == [
        "Conway.Life.Basic",
        "Mathlib.Data.Nat.Basic",
        "Conway.Life.MacroCell",
    ]


def test_build_graph_splits_internal_and_external(tmp_path) -> None:
    """Les imports internes deviennent des arcs ; les externes, la frontiere."""
    mod = _load()
    (tmp_path / "Conway").mkdir()
    (tmp_path / "Conway" / "Basic.lean").write_text(
        "import Mathlib.Data.Nat.Basic\n", encoding="utf-8")
    (tmp_path / "Conway" / "Life.lean").write_text(
        "import Conway.Basic\nimport Mathlib.Order.Basic\n", encoding="utf-8")
    data = mod.build_graph(tmp_path)
    assert data["nodes"] == ["Conway.Basic", "Conway.Life"]
    assert data["graph"]["Conway.Life"] == ["Conway.Basic"]
    assert data["graph"]["Conway.Basic"] == []
    assert data["external"] == {"Mathlib": 2}


def test_build_graph_excludes_lake_build_dirs(tmp_path) -> None:
    """.lake/ (deps vendorisees) et build/ ne sont pas des modules du lake."""
    mod = _load()
    (tmp_path / ".lake" / "packages" / "mathlib").mkdir(parents=True)
    (tmp_path / ".lake" / "packages" / "mathlib" / "Order.lean").write_text(
        "", encoding="utf-8")
    (tmp_path / "Real.lean").write_text("import Order\n", encoding="utf-8")
    data = mod.build_graph(tmp_path)
    assert data["nodes"] == ["Real"]
    # Order n'est pas un noeud : il passe par la frontiere externe.
    assert data["graph"]["Real"] == []


def test_compute_metrics_on_synthetic_dag() -> None:
    """Profondeur, degres et composantes sur un DAG de forme connue."""
    mod = _load()
    # a -> b -> c -> d ; a -> c ; e (isole)
    data = {
        "nodes": ["a", "b", "c", "d", "e"],
        "graph": {"a": ["b", "c"], "b": ["c"], "c": ["d"], "d": [], "e": []},
        "external": {"Mathlib": 2},
    }
    metrics = mod.compute_metrics(data, top=2)
    assert metrics["modules"] == 5
    assert metrics["internal_edges"] == 4
    assert metrics["max_depth"] == 3  # a(3) -> b(2) -> c(1) -> d(0)
    assert metrics["mean_depth"] == round((3 + 2 + 1 + 0 + 0) / 5, 3)
    assert metrics["leaf_modules"] == 2  # d et e n'importent rien
    assert metrics["weak_components"] == 2
    assert metrics["cyclic"] is False
    assert metrics["top_referenced"] == {"c": 2, "b": 1}


def test_compute_metrics_flags_defensive_cycle() -> None:
    """Un cycle d'imports est anormal : signale, jamais boucle infinie."""
    mod = _load()
    data = {
        "nodes": ["x", "y"],
        "graph": {"x": ["y"], "y": ["x"]},
        "external": {},
    }
    metrics = mod.compute_metrics(data)
    assert metrics["cyclic"] is True


def test_main_rejects_missing_lake(tmp_path, capsys) -> None:
    """Un lake introuvable est un defaut d'instrument (exit 2), jamais un 0."""
    mod = _load()
    rc = mod.main(["--lake", str(tmp_path / "absent")])
    assert rc == mod.EXIT_INSTRUMENT
    assert "introuvable" in capsys.readouterr().err