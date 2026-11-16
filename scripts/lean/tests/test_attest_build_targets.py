"""Tests for scripts/lean/attest_build_targets.py — resolution des cibles de `lake build`.

Couvre la resolution pure (aucun `lake`, aucun reseau, aucune machine) :
- lecture du lakefile (lib, globs, srcDir) ;
- enumeration des modules **du lac** (les globs font foi, pas la presence du fichier) ;
- resolution d'un fichier touche -> module Lean ;
- jumeau `_en` (deux fichiers, deux modules) ;
- dependants **transitifs** ;
- agregateur ecarte **et nomme** (une borne invisible surdeclare la portee) ;
- repli explicite quand un fichier `.lean` touche n'est pas un module du lac.

Fixtures synthetiques sous ``tmp_path``. Zero dependance externe.
"""

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from attest_build_targets import (  # noqa: E402
    dependents_of,
    enumerate_modules,
    import_graph,
    is_aggregator,
    libraries,
    module_name_of,
    resolve_targets,
    sibling_en_module,
    source_root,
)


# ---------------------------------------------------------------------------
# helpers
# ---------------------------------------------------------------------------

LAKEFILE = """import Lake
open Lake DSL

package «demo» where
  require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.33.0"

@[default_target]
lean_lib «Demo» where
  globs := #[.submodules `Demo, `Demo_en]
"""


def _write(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def _make_lake(root: Path) -> Path:
    """Un lake de demonstration : un agregateur racine, un module de contenu,
    son jumeau `_en`, un dependant, un agregateur intermediaire et un
    dependant de cet aggregateur."""
    lake = root / "demo"
    _write(lake / "lakefile.lean", LAKEFILE)
    _write(lake / "lean-toolchain", "leanprover/lean4:v4.33.0\n")
    # Agregateur racine : des imports, aucune declaration.
    _write(lake / "Demo.lean", "import Demo.Alpha\nimport Demo.Beta\n")
    # Agregateur racine `_en` (deux declarations : ce n'est PAS un agregateur).
    _write(lake / "Demo_en.lean", "import Demo.Alpha_en\n\ndef demoHelper : Nat := 0\n")
    # Module de contenu, avec son jumeau `_en`.
    _write(lake / "Demo" / "Alpha.lean", "import Demo.Beta\n\ntheorem alpha_ok : True := trivial\n")
    _write(lake / "Demo" / "Alpha_en.lean", "import Demo.Beta_en\n\ntheorem alpha_ok : True := trivial\n")
    _write(lake / "Demo" / "Beta.lean", "theorem beta_ok : True := trivial\n")
    _write(lake / "Demo" / "Beta_en.lean", "theorem beta_ok : True := trivial\n")
    # Agregateur intermediaire : il importe Alpha, sans declarer.
    _write(lake / "Demo" / "Gamma.lean", "import Demo.Alpha\n")
    # Dependant NON-agregateur de l'agregateur : il doit etre construit.
    _write(lake / "Demo" / "Delta.lean", "import Demo.Gamma\n\ntheorem delta_ok : True := trivial\n")
    return lake


# ---------------------------------------------------------------------------
# lakefile
# ---------------------------------------------------------------------------

def test_le_globs_sont_lus(tmp_path):
    lake = _make_lake(tmp_path)
    libs = libraries(lake)
    assert len(libs) == 1
    assert libs[0]["name"] == "Demo"
    assert {"kind": "submodules", "name": "Demo"} in libs[0]["globs"]
    assert {"kind": "one", "name": "Demo_en"} in libs[0]["globs"]


def test_une_lib_sans_globs_constructit_seulement_son_module_racine(tmp_path):
    lake = tmp_path / "plain"
    _write(lake / "lakefile.lean", "import Lake\n@[default_target]\nlean_lib «Plain» where\n")
    _write(lake / "Plain.lean", "theorem ok : True := trivial\n")
    _write(lake / "Plain" / "Sub.lean", "theorem sub : True := trivial\n")
    libs = libraries(lake)
    assert libs[0]["globs"] == [{"kind": "one", "name": "Plain"}]
    modules = enumerate_modules(lake)
    # `Plain.Sub` n'est pas dans les globs : il n'est pas constructible.
    assert set(modules) == {"Plain"}


def test_le_srcdir_est_honore(tmp_path):
    lake = tmp_path / "s"
    _write(lake / "lakefile.lean", "import Lake\n@[default_target]\nlean_lib «S» where\n  srcDir := \"src\"\n  globs := #[.submodules `S]\n")
    _write(lake / "src" / "S.lean", "theorem ok : True := trivial\n")
    assert source_root(lake) == (lake / "src").resolve()
    assert set(enumerate_modules(lake)) == {"S"}


def test_un_lakefile_illisible_ne_devine_pas(tmp_path):
    lake = tmp_path / "vide"
    lake.mkdir()
    assert libraries(lake) == []
    assert enumerate_modules(lake) == {}


# ---------------------------------------------------------------------------
# modules
# ---------------------------------------------------------------------------

def test_les_modules_suivent_les_globs(tmp_path):
    lake = _make_lake(tmp_path)
    modules = enumerate_modules(lake)
    assert set(modules) == {
        "Demo",
        "Demo_en",
        "Demo.Alpha",
        "Demo.Alpha_en",
        "Demo.Beta",
        "Demo.Beta_en",
        "Demo.Gamma",
        "Demo.Delta",
    }


def test_module_name_of():
    assert module_name_of("Demo/Life/JumpCapture.lean") == "Demo.Life.JumpCapture"
    assert module_name_of("Demo.lean") == "Demo"
    assert module_name_of("Demo.lean.bak") is None


def test_le_graphe_ne_garde_que_les_imports_internes(tmp_path):
    lake = _make_lake(tmp_path)
    modules = enumerate_modules(lake)
    graph = import_graph(lake, modules)
    assert graph["Demo.Alpha"] == {"Demo.Beta"}
    assert graph["Demo.Gamma"] == {"Demo.Alpha"}
    assert graph["Demo.Beta"] == set()


def test_dependants_transitifs(tmp_path):
    lake = _make_lake(tmp_path)
    modules = enumerate_modules(lake)
    graph = import_graph(lake, modules)
    dependents = dependents_of(graph, {"Demo.Alpha"})
    # Gamma importe Alpha ; Delta importe Gamma (fermeture, pas voisinage).
    assert {"Demo.Gamma", "Demo.Delta"} <= dependents


# ---------------------------------------------------------------------------
# agregateurs
# ---------------------------------------------------------------------------

def test_un_fichier_sans_declaration_est_un_agregateur():
    assert is_aggregator("import Demo.Alpha\n")
    assert is_aggregator("/-- un commentaire --/\nimport Demo.Alpha\n")
    assert not is_aggregator("theorem ok : True := trivial\n")
    assert not is_aggregator("def helper : Nat := 0\n")


# ---------------------------------------------------------------------------
# resolution
# ---------------------------------------------------------------------------

def test_la_resolution_nomme_les_cibles_les_dependants_et_les_agregateurs_ecartes(tmp_path):
    lake = _make_lake(tmp_path)
    verdict = resolve_targets(lake, ["demo/Demo/Alpha.lean"], lake_prefix="demo/")
    assert verdict["ok"], verdict["reason"]
    # La racine : le module touche + son jumeau `_en`.
    assert set(verdict["roots"]) == {"Demo.Alpha", "Demo.Alpha_en"}
    # Le dependent non-agregateur (Delta) est construit ; l'agregateur
    # (Gamma) ne l'est pas -- et il est NOMME.
    assert "Demo.Delta" in verdict["targets"]
    assert "Demo.Gamma" not in verdict["targets"]
    assert "Demo.Gamma" in verdict["skipped_aggregators"]
    # La racine elle-meme n'est jamais un "dependant" d'elle-meme.
    assert "Demo.Alpha" not in verdict["dependents"]


def test_un_fichier_lean_touche_hors_module_force_le_repli(tmp_path):
    lake = _make_lake(tmp_path)
    verdict = resolve_targets(lake, ["demo/Demo/Alpha.lean", "demo/Note.lean"], lake_prefix="demo/")
    assert not verdict["ok"]
    assert "Note.lean" in verdict["reason"]
    assert verdict["targets"] == []


def test_un_diff_sans_lean_ne_resout_rien(tmp_path):
    lake = _make_lake(tmp_path)
    verdict = resolve_targets(lake, ["demo/README.md"], lake_prefix="demo/")
    assert not verdict["ok"]
    assert verdict["targets"] == []


def test_le_prefixe_du_lake_est_deduit_du_depot(tmp_path):
    repo = tmp_path / "repo"
    lake = _make_lake(repo)
    # Les chemins du diff sont relatifs au depot : `demo/...`, pas `repo/...`.
    verdict = resolve_targets(
        lake, ["demo/Demo/Beta.lean"], repo_root=repo
    )
    assert verdict["ok"], verdict["reason"]
    # Le module touche et son jumeau `_en` (deux fichiers, deux modules).
    assert verdict["roots"] == ["Demo.Beta", "Demo.Beta_en"]


def test_le_jumeau_en_est_resolu_dans_les_deux_sens(tmp_path):
    lake = _make_lake(tmp_path)
    modules = enumerate_modules(lake)
    assert sibling_en_module(lake, modules, "Demo.Alpha") == "Demo.Alpha_en"
    assert sibling_en_module(lake, modules, "Demo.Alpha_en") == "Demo.Alpha"
    # `Demo.Beta` a un jumeau `_en` ; `Demo.Delta` n'en a pas.
    assert sibling_en_module(lake, modules, "Demo.Beta") == "Demo.Beta_en"
    assert sibling_en_module(lake, modules, "Demo.Delta") is None


# ---------------------------------------------------------------------------
# payload
# ---------------------------------------------------------------------------
# Le payload de build n'est PAS construit ici : ce module est pur, et une
# liste de commande posee hors de la main de l'organe est une voie directe
# (refusee par `scripts/lean/check_lake_direct_invocation.py`). Le contrat
# du payload est verifie la ou il est remis a l'organe :
# `tests/test_attest_local_build_payload.py`.


if __name__ == "__main__":  # pragma: no cover
    raise SystemExit(pytest.main([__file__, "-v"]))
