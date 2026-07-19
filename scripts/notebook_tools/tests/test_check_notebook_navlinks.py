"""Tests for scripts/notebook_tools/check_notebook_navlinks.py — notebook-cell navlink guard.

Why this test file exists
--------------------------
`check_notebook_navlinks.py` (axe-3 sibling of `check_docs_links.py`) parse
chaque cellule markdown d'un notebook .ipynb, extrait les liens relatifs
`[text](target)` (meme regex que `check_docs_links.py`), resout la cible
RELATIVEMENT au dossier parent du notebook, et signale les cibles absentes
(404). C'est le filet de securite des renumerotations de notebooks (EPIC
#5081) : un agent qui deplace un notebook casse inevitablement 1 ou 2
navlinks precedents/suivants dans les notebooks voisins.

Sept clusters :
  1. TestShouldSkip — filtre SKIP_DIRS (_archives, .lake, vendored, ...)
  2. TestIsCheckableTarget — FP filters : template/URL/absolu/anchor/empty-text/
     no-extension/self-ref/URL-encoded/GitHub paths
  3. TestResolveTarget — strip ancre + unquote + './' + parent-relative
  4. TestIsInSubmodule — submodule match / no-match / no-submodules
  5. TestScanNotebook — parse notebook + kind=nav|link + cell_type filter +
     source-as-string/list + illisible + line_no + submodule deep-link skip
  6. TestBaselineIO — write+load deterministe + missing + corrupted JSON
  7. TestMainModes — argparse + --baseline/--check/--json/--quiet/--family +
     exit codes 0/1/2
  8. TestConstants — REPO_ROOT, NOTEBOOKS_ROOT, SKIP_DIRS, BASELINE_PATH,
     LINK_PATTERN
"""
import json
import sys
from pathlib import Path

import pytest

# import du module sous test (depuis le dossier parent)
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
import check_notebook_navlinks as cnn  # noqa: E402


def _nb(cells):
    """Notebook synthetique minimal avec une liste de cellules (type, source)."""
    return {
        "cells": [{"cell_type": t, "source": s, "metadata": {}} for (t, s) in cells],
        "metadata": {},
        "nbformat": 4,
        "nbformat_minor": 5,
    }


@pytest.fixture(autouse=True)
def _patch_repo(monkeypatch, tmp_path):
    """Fixture autouse : re-implante REPO_ROOT sur tmp_path et NOTEBOOKS_ROOT
    sur tmp_path/MyIA.AI.Notebooks pour que `_should_skip` + `scan_notebook`
    fonctionnent depuis tmp_path (`relative_to(REPO_ROOT)` ne leve plus ValueError)."""
    fake_repo = tmp_path.resolve()
    monkeypatch.setattr(cnn, "REPO_ROOT", fake_repo)
    monkeypatch.setattr(cnn, "NOTEBOOKS_ROOT", fake_repo / "MyIA.AI.Notebooks")
    # creer le sous-dossier MyIA.AI.Notebooks pour les tests d'iteration
    (fake_repo / "MyIA.AI.Notebooks").mkdir(exist_ok=True)
    return tmp_path


def _write_nb(tmp_path, cells, name="nb.ipynb"):
    """Ecrit un notebook synthetique sur disque sous tmp_path.

    On mock REPO_ROOT = tmp_path.parent pour que scan_notebook puisse faire
    nb_path.relative_to(REPO_ROOT). A utiliser avec `monkeypatch` :
        _write_nb_with_repo(monkeypatch, tmp_path, ...)
    ou appliquer via `_patch_repo_root(monkeypatch, tmp_path)` dans la fixture.
    """
    p = tmp_path / name
    p.write_text(json.dumps(_nb(cells)), encoding="utf-8")
    return p


def _patch_repo_root(monkeypatch, tmp_path):
    """Re-implante REPO_ROOT sur tmp_path (et NOTEBOOKS_ROOT = tmp_path) pour
    que `_should_skip` + `scan_notebook` (qui font `relative_to(REPO_ROOT)`)
    fonctionnent depuis tmp_path.
    """
    monkeypatch.setattr(cnn, "REPO_ROOT", tmp_path.resolve())
    monkeypatch.setattr(cnn, "NOTEBOOKS_ROOT", tmp_path.resolve())


# ---------------------------------------------------------------------------
# 1. _should_skip — filtre SKIP_DIRS
# ---------------------------------------------------------------------------
class TestShouldSkip:
    def test_archive_dir_is_skipped(self, tmp_path):
        nb = tmp_path / "_archives" / "old.ipynb"
        nb.parent.mkdir()
        assert cnn._should_skip(nb) is True

    def test_lake_dir_is_skipped(self, tmp_path):
        nb = tmp_path / ".lake" / "foo.lean"
        nb.parent.mkdir()
        assert cnn._should_skip(nb) is True

    def test_checkpoints_dir_is_skipped(self, tmp_path):
        nb = tmp_path / ".ipynb_checkpoints" / "nb-checkpoint.ipynb"
        nb.parent.mkdir()
        assert cnn._should_skip(nb) is True

    def test_output_dir_is_skipped(self, tmp_path):
        nb = tmp_path / "_output" / "nb_output.ipynb"
        nb.parent.mkdir()
        assert cnn._should_skip(nb) is True

    def test_pycache_is_skipped(self, tmp_path):
        nb = tmp_path / "__pycache__" / "nb.ipynb"
        nb.parent.mkdir()
        assert cnn._should_skip(nb) is True

    def test_vendored_foundry_lib_is_skipped(self, tmp_path):
        nb = tmp_path / "foundry-lib" / "lib" / "foo.ipynb"
        nb.parent.mkdir(parents=True)
        assert cnn._should_skip(nb) is True

    def test_normal_dir_is_not_skipped(self, tmp_path):
        # NB : la fixture _patch_repo a REPO_ROOT=tmp_path. On cree un sous-dossier
        # "Search" qui n'est PAS dans SKIP_DIRS -> doit retourner False.
        nb = tmp_path / "Search" / "01-Foundations" / "nb.ipynb"
        nb.parent.mkdir(parents=True)
        assert cnn._should_skip(nb) is False

    def test_path_outside_repo_is_skipped(self, monkeypatch, tmp_path):
        # Cas path-outside-repo : on mock REPO_ROOT ailleurs puis on passe un
        # chemin en dehors. `_should_skip` doit retourner True (catch ValueError).
        other_root = tmp_path / "elsewhere_repo"
        other_root.mkdir()
        monkeypatch.setattr(cnn, "REPO_ROOT", other_root)
        outside = tmp_path / "foo.ipynb"
        assert cnn._should_skip(outside) is True


# ---------------------------------------------------------------------------
# 2. _is_checkable_target — FP filters
# ---------------------------------------------------------------------------
class TestIsCheckableTarget:
    def test_empty_target_rejected(self):
        assert cnn._is_checkable_target("", "txt") is False

    def test_template_var_rejected(self):
        # {var} n'est pas un fichier
        assert cnn._is_checkable_target("{filename}", "txt") is False

    def test_http_url_rejected(self):
        assert cnn._is_checkable_target("https://example.com/x.ipynb", "txt") is False

    def test_absolute_path_rejected(self):
        assert cnn._is_checkable_target("/abs/path/nb.ipynb", "txt") is False

    def test_anchor_only_rejected(self):
        assert cnn._is_checkable_target("#section", "txt") is False

    def test_trailing_slash_rejected(self):
        # dossier nu, pas un fichier
        assert cnn._is_checkable_target("subdir/", "txt") is False

    def test_empty_text_rejected_katex_fp(self):
        # operator modal / KaTeX `[](phi)` -> texte vide
        assert cnn._is_checkable_target("phi", "") is False

    def test_no_extension_no_slash_rejected(self):
        # RollingWindow[T](taille) -> target "taille", pas un fichier
        assert cnn._is_checkable_target("taille", "RollingWindow[T]") is False

    def test_self_reference_rejected(self):
        # `[`Theorem.cs`](Theorem.cs)` -> text==target, code-as-doc pas un navlink
        assert cnn._is_checkable_target("Theorem.cs", "Theorem.cs") is False

    def test_url_encoded_rejected(self):
        # %2F = /, lien web encode pas working-tree
        assert cnn._is_checkable_target("foo%2Fbar.ipynb", "txt") is False

    def test_github_issues_path_rejected(self):
        # chemin vers /issues/ = lien GitHub, pas fichier local
        assert cnn._is_checkable_target("../../../issues/123", "txt") is False

    def test_github_blob_path_rejected(self):
        assert cnn._is_checkable_target("../../../blob/main/README.md", "txt") is False

    def test_valid_relative_ipynb_accepted(self):
        assert cnn._is_checkable_target("next.ipynb", "Suivant") is True

    def test_valid_relative_md_accepted(self):
        assert cnn._is_checkable_target("../README.md", "Index") is True

    def test_valid_image_png_accepted(self):
        assert cnn._is_checkable_target("assets/fig.png", "Figure") is True

    def test_valid_anchor_with_file_accepted(self):
        # `foo.ipynb#section` -> on depouille l'ancre, on garde `foo.ipynb`
        assert cnn._is_checkable_target("foo.ipynb#section", "link") is True


# ---------------------------------------------------------------------------
# 3. _resolve_target — strip + unquote + parent-relative
# ---------------------------------------------------------------------------
class TestResolveTarget:
    def test_strips_anchor_before_resolve(self, tmp_path):
        nb = _write_nb(tmp_path, [], "nb.ipynb")
        target = "sibling.ipynb#section"
        resolved = cnn._resolve_target(nb, target)
        assert resolved == nb.parent / "sibling.ipynb"
        assert "#section" not in str(resolved)

    def test_unquotes_url_encoded_path(self, tmp_path):
        nb = _write_nb(tmp_path, [], "nb.ipynb")
        # NB : unquote transforme %20 -> espace, etc.
        target = "foo%20bar.ipynb"
        resolved = cnn._resolve_target(nb, target)
        assert "foo bar.ipynb" in str(resolved)

    def test_strips_dot_slash_prefix_only(self, tmp_path):
        # './' (relatif-courant) est strippe, mais '../' (parent-dir) preserve
        nb = _write_nb(tmp_path, [], "nb.ipynb")
        target_dot = "./sibling.ipynb"
        target_dotdot = "../sibling.ipynb"
        assert cnn._resolve_target(nb, target_dot) == cnn._resolve_target(nb, "sibling.ipynb")
        # '../' est preserve dans la resolution
        resolved_parent = cnn._resolve_target(nb, target_dotdot)
        assert resolved_parent.parent == nb.parent.parent

    def test_anchor_only_returns_notebook_path(self, tmp_path):
        nb = _write_nb(tmp_path, [], "nb.ipynb")
        resolved = cnn._resolve_target(nb, "#section")
        # ancre seule = on retourne le notebook lui-meme (existe)
        assert resolved == nb

    def test_resolved_is_absolute_path(self, tmp_path):
        nb = _write_nb(tmp_path, [], "nb.ipynb")
        resolved = cnn._resolve_target(nb, "missing.ipynb")
        assert resolved.is_absolute()


# ---------------------------------------------------------------------------
# 4. _is_in_submodule
# ---------------------------------------------------------------------------
class TestIsInSubmodule:
    def test_path_inside_submodule_detected(self, tmp_path, monkeypatch):
        sm_root = tmp_path / "Z3.Linq"
        sm_root.mkdir()
        monkeypatch.setattr(cnn, "SUBMODULE_PATHS", [sm_root.resolve()])
        inside = sm_root / "solutions" / "Theorem.cs"
        assert cnn._is_in_submodule(inside) is True

    def test_path_outside_submodule_not_detected(self, tmp_path, monkeypatch):
        sm_root = tmp_path / "Z3.Linq"
        sm_root.mkdir()
        monkeypatch.setattr(cnn, "SUBMODULE_PATHS", [sm_root.resolve()])
        outside = tmp_path / "Search" / "nb.ipynb"
        assert cnn._is_in_submodule(outside) is False

    def test_no_submodule_paths_returns_false(self, monkeypatch):
        monkeypatch.setattr(cnn, "SUBMODULE_PATHS", [])
        assert cnn._is_in_submodule(Path("/some/path")) is False


# ---------------------------------------------------------------------------
# 5. scan_notebook — parse + broken detection
# ---------------------------------------------------------------------------
class TestScanNotebook:
    def test_no_broken_returns_empty_list(self, tmp_path):
        nb = _write_nb(tmp_path, [("markdown", "Texte sans lien.")])
        assert cnn.scan_notebook(nb) == []

    def test_valid_link_not_flagged(self, tmp_path):
        # creer un fichier sibling que le lien peut resoudre
        sibling = tmp_path / "sibling.ipynb"
        sibling.write_text("{}", encoding="utf-8")
        nb = _write_nb(tmp_path, [("markdown", "[next](sibling.ipynb)")])
        assert cnn.scan_notebook(nb) == []

    def test_broken_navlink_flagged_as_nav(self, tmp_path):
        nb = _write_nb(tmp_path, [("markdown", "[next](missing.ipynb)")])
        broken = cnn.scan_notebook(nb)
        assert len(broken) == 1
        assert broken[0]["kind"] == "nav"  # "next" est dans le vocabulaire nav
        assert broken[0]["target"] == "missing.ipynb"
        assert broken[0]["cell_idx"] == 0
        assert broken[0]["line_no"] == 1
        assert "notebook" in broken[0]
        assert broken[0]["text"] == "next"

    def test_broken_non_navlink_flagged_as_link(self, tmp_path):
        # cible cassee mais texte sans mot-cle nav -> kind=link
        nb = _write_nb(tmp_path, [("markdown", "[figure](missing.png)")])
        broken = cnn.scan_notebook(nb)
        assert len(broken) == 1
        assert broken[0]["kind"] == "link"

    def test_code_cell_links_ignored(self, tmp_path):
        # les liens dans les cellules code ne sont PAS des navlinks
        nb = _write_nb(tmp_path, [("code", "[next](missing.ipynb)")])
        assert cnn.scan_notebook(nb) == []

    def test_source_as_string_list_handled(self, tmp_path):
        # nbformat peut stocker source comme str OU list[str]
        nb_dict = {
            "cells": [
                {"cell_type": "markdown",
                 "source": ["ligne 1\n", "ligne 2 [next](missing.ipynb)\n"],
                 "metadata": {}}
            ],
            "metadata": {}, "nbformat": 4, "nbformat_minor": 5,
        }
        nb_path = tmp_path / "nb.ipynb"
        nb_path.write_text(json.dumps(nb_dict), encoding="utf-8")
        broken = cnn.scan_notebook(nb_path)
        assert len(broken) == 1
        assert broken[0]["line_no"] == 2  # deuxieme ligne (1-indexed)

    def test_unreadable_notebook_returns_none(self, tmp_path):
        # fichier corrompu -> scan_notebook retourne None
        nb = tmp_path / "corrupt.ipynb"
        nb.write_text("{not valid json", encoding="utf-8")
        assert cnn.scan_notebook(nb) is None

    def test_submodule_deep_link_skipped(self, tmp_path, monkeypatch):
        # un lien vers un fichier DANS un submodule = valide GitHub, pas un 404 local
        sm_root = tmp_path / "MySubmodule"
        sm_root.mkdir()
        deep_target = sm_root / "Theorem.cs"
        monkeypatch.setattr(cnn, "SUBMODULE_PATHS", [sm_root.resolve()])
        nb = _write_nb(tmp_path, [("markdown", f"[deep]({deep_target.name})")])
        # le lien pointe vers un fichier inexistant en dehors du submodule
        # mais on simule le cas submodule en mockant _is_in_submodule
        monkeypatch.setattr(cnn, "_is_in_submodule", lambda p: True)
        broken = cnn.scan_notebook(nb)
        assert broken == []

    def test_multiple_broken_in_one_cell(self, tmp_path):
        nb = _write_nb(tmp_path, [("markdown",
                                   "[next](missing1.ipynb)\n[prev](missing2.ipynb)")])
        broken = cnn.scan_notebook(nb)
        assert len(broken) == 2
        assert {b["line_no"] for b in broken} == {1, 2}

    def test_multiple_cells_broken_indexed(self, tmp_path):
        nb = _write_nb(tmp_path, [
            ("markdown", "[next](missing1.ipynb)"),
            ("markdown", "[prev](missing2.ipynb)"),
        ])
        broken = cnn.scan_notebook(nb)
        assert len(broken) == 2
        assert {b["cell_idx"] for b in broken} == {0, 1}

    def test_existing_file_not_flagged(self, tmp_path):
        sibling = tmp_path / "sibling.ipynb"
        sibling.write_text("{}", encoding="utf-8")
        nb = _write_nb(tmp_path, [("markdown", "[next](sibling.ipynb)")])
        assert cnn.scan_notebook(nb) == []

    def test_fp_targets_not_flagged(self, tmp_path):
        # KaTeX operator, self-ref, URL-encoded : ne doivent PAS etre signales
        nb = _write_nb(tmp_path, [("markdown",
                                   "[](phi)\n[`Theorem.cs`](Theorem.cs)\n"
                                   "[link](foo%2Fbar.ipynb)")])
        assert cnn.scan_notebook(nb) == []


# ---------------------------------------------------------------------------
# 6. _write_baseline / _load_baseline — JSON I/O
# ---------------------------------------------------------------------------
class TestBaselineIO:
    def test_write_then_load_deterministe(self, tmp_path, monkeypatch):
        # Mock BASELINE_PATH pour pointer dans tmp_path
        baseline_file = tmp_path / "baseline.json"
        monkeypatch.setattr(cnn, "BASELINE_PATH", baseline_file)

        broken = [
            {"notebook": "a.ipynb", "cell_idx": 1, "line_no": 2,
             "text": "next", "target": "b.ipynb", "kind": "nav",
             "line": "[next](b.ipynb)"},
            {"notebook": "a.ipynb", "cell_idx": 3, "line_no": 1,
             "text": "prev", "target": "c.ipynb", "kind": "nav",
             "line": "[prev](c.ipynb)"},
        ]
        cnn._write_baseline(broken)
        assert baseline_file.exists()

        loaded = cnn._load_baseline()
        # cle = (notebook, cell_idx, line_no, target)
        assert ("a.ipynb", 1, 2, "b.ipynb") in loaded
        assert ("a.ipynb", 3, 1, "c.ipynb") in loaded
        assert len(loaded) == 2

    def test_write_baseline_is_sorted_deterministe(self, tmp_path, monkeypatch):
        baseline_file = tmp_path / "baseline.json"
        monkeypatch.setattr(cnn, "BASELINE_PATH", baseline_file)

        # deux entrees en ordre inverse : le fichier doit etre trie
        broken = [
            {"notebook": "b.ipynb", "cell_idx": 0, "line_no": 1,
             "text": "x", "target": "y.ipynb", "kind": "link", "line": "[x](y.ipynb)"},
            {"notebook": "a.ipynb", "cell_idx": 0, "line_no": 1,
             "text": "x", "target": "y.ipynb", "kind": "link", "line": "[x](y.ipynb)"},
        ]
        cnn._write_baseline(broken)
        data = json.loads(baseline_file.read_text(encoding="utf-8"))
        # Premiere entree doit etre "a.ipynb" (cle inferieure)
        assert data["broken_links"][0]["notebook"] == "a.ipynb"
        assert data["broken_links"][1]["notebook"] == "b.ipynb"

    def test_load_baseline_missing_returns_empty(self, tmp_path, monkeypatch):
        # BASELINE_PATH pointe vers un fichier inexistant
        monkeypatch.setattr(cnn, "BASELINE_PATH", tmp_path / "ghost.json")
        assert cnn._load_baseline() == set()

    def test_load_baseline_corrupted_returns_empty(self, tmp_path, monkeypatch):
        bad = tmp_path / "bad.json"
        bad.write_text("{not valid", encoding="utf-8")
        monkeypatch.setattr(cnn, "BASELINE_PATH", bad)
        assert cnn._load_baseline() == set()

    def test_write_baseline_creates_parent_dir(self, tmp_path, monkeypatch):
        deep = tmp_path / "scripts" / "tests" / "baseline.json"
        monkeypatch.setattr(cnn, "BASELINE_PATH", deep)
        cnn._write_baseline([])
        assert deep.parent.is_dir()


# ---------------------------------------------------------------------------
# 7. main() — argparse + exit codes + modes
# ---------------------------------------------------------------------------
class TestMainModes:
    def _setup_tracked(self, monkeypatch, nb_paths):
        """Mock _git_tracked_notebooks pour retourner la liste passee.

        Accepte soit une liste de Path soit un set de strings posix (relatifs
        a REPO_ROOT).
        """
        rels = set()
        for p in nb_paths:
            try:
                rels.add(p.relative_to(cnn.REPO_ROOT).as_posix())
            except ValueError:
                rels.add(p.as_posix())
        monkeypatch.setattr(cnn, "_git_tracked_notebooks", lambda: rels)

    def test_main_returns_2_if_notebook_arg_missing(self, tmp_path):
        rc = cnn.main(["nonexistent_xyz.ipynb"])
        assert rc == 2

    def test_main_returns_0_when_no_broken(self, tmp_path, monkeypatch):
        nb = _write_nb(tmp_path, [("markdown", "[link](https://example.com)")], name="ok.ipynb")
        # mode notebook cible : pas de filtre tracked, on laisse passer
        rc = cnn.main([str(nb)])
        assert rc == 0

    def test_main_returns_1_when_broken_found(self, tmp_path):
        nb = _write_nb(tmp_path, [("markdown", "[next](missing.ipynb)")], name="bad.ipynb")
        rc = cnn.main([str(nb)])
        assert rc == 1

    def test_main_json_outputs_machine_readable(self, tmp_path, capsys):
        nb = _write_nb(tmp_path, [("markdown", "[next](missing.ipynb)")], name="bad.ipynb")
        rc = cnn.main([str(nb), "--json"])
        assert rc == 1
        out = capsys.readouterr().out
        data = json.loads(out)
        assert "total_broken" in data
        assert data["total_broken"] == 1
        assert isinstance(data["broken"], list)

    def test_main_baseline_writes_file(self, tmp_path, monkeypatch):
        nb = _write_nb(tmp_path, [("markdown", "[next](missing.ipynb)")], name="bad.ipynb")
        baseline = tmp_path / "baseline.json"
        monkeypatch.setattr(cnn, "BASELINE_PATH", baseline)
        rc = cnn.main([str(nb), "--baseline"])
        assert rc == 0
        assert baseline.exists()
        data = json.loads(baseline.read_text(encoding="utf-8"))
        assert "broken_links" in data

    def test_main_check_passes_when_no_new_broken(self, tmp_path, monkeypatch):
        nb = _write_nb(tmp_path, [("markdown", "[next](missing.ipynb)")], name="bad.ipynb")
        # baseline pre-enregistre contenant EXACTEMENT ce broken
        baseline = tmp_path / "baseline.json"
        baseline.write_text(json.dumps({
            "broken_links": [{
                "notebook": str(nb.relative_to(cnn.REPO_ROOT)).replace("\\", "/"),
                "cell_idx": 0, "line_no": 1,
                "text": "next", "target": "missing.ipynb", "kind": "nav"
            }]
        }), encoding="utf-8")
        monkeypatch.setattr(cnn, "BASELINE_PATH", baseline)
        rc = cnn.main([str(nb), "--check"])
        assert rc == 0

    def test_main_check_fails_when_new_broken(self, tmp_path, monkeypatch):
        nb = _write_nb(tmp_path, [("markdown", "[next](missing.ipynb)"), ("markdown", "[prev](missing2.ipynb)")], name="bad.ipynb")
        # baseline vide -> les 2 broken sont NEW
        baseline = tmp_path / "baseline.json"
        baseline.write_text(json.dumps({"broken_links": []}), encoding="utf-8")
        monkeypatch.setattr(cnn, "BASELINE_PATH", baseline)
        rc = cnn.main([str(nb), "--check"])
        assert rc == 1

    def test_main_check_quiet_suppresses_output(self, tmp_path, monkeypatch, capsys):
        nb = _write_nb(tmp_path, [("markdown", "[next](missing.ipynb)")], name="bad.ipynb")
        baseline = tmp_path / "baseline.json"
        baseline.write_text(json.dumps({"broken_links": []}), encoding="utf-8")
        monkeypatch.setattr(cnn, "BASELINE_PATH", baseline)
        rc = cnn.main([str(nb), "--check", "--quiet"])
        assert rc == 1
        out = capsys.readouterr().out
        assert "FAIL" not in out  # quiet : pas de detaille par lien

    def test_main_family_filter_limits_scan(self, tmp_path, monkeypatch):
        # deux notebooks dans des familles differentes
        nb_a = _write_nb(tmp_path, [("markdown", "[next](missing.ipynb)")], name="a.ipynb")
        nb_b = _write_nb(tmp_path, [("markdown", "[next](missing.ipynb)")], name="b.ipynb")
        # les notebook temp_path ne sont pas sous NOTEBOOKS_ROOT -> on passe
        # par le mode notebook cible. Ici on teste --family : on mock
        # _iter_notebooks pour retourner un seul des deux.
        monkeypatch.setattr(cnn, "_iter_notebooks",
                            lambda family, tracked_only: iter([nb_a]) if family == "Search" else iter([nb_a, nb_b]))
        rc = cnn.main(["--family", "Search"])
        # 1 notebook casse -> rc=1
        assert rc == 1

    def test_main_include_untracked_disables_filter(self, tmp_path, monkeypatch, capsys):
        # mock _iter_notebooks pour renvoyer un notebook casse quoi qu'il arrive
        nb = _write_nb(tmp_path, [("markdown", "[next](missing.ipynb)")], name="x.ipynb")
        monkeypatch.setattr(cnn, "_iter_notebooks",
                            lambda family, tracked_only: iter([nb]))
        rc = cnn.main(["--include-untracked", "--json"])
        assert rc == 1

    def test_main_no_notebooks_found_returns_2(self, tmp_path, monkeypatch):
        monkeypatch.setattr(cnn, "_iter_notebooks", lambda family, tracked_only: iter([]))
        rc = cnn.main([])
        assert rc == 2


# ---------------------------------------------------------------------------
# 8. Constantes + LINK_PATTERN
# ---------------------------------------------------------------------------
class TestConstants:
    def test_repo_root_exists(self):
        # REPO_ROOT = parent.parent.parent du module
        assert cnn.REPO_ROOT.is_dir()

    def test_notebooks_root_under_repo(self):
        assert cnn.NOTEBOOKS_ROOT.parent == cnn.REPO_ROOT

    def test_skip_dirs_is_set_of_strings(self):
        assert isinstance(cnn.SKIP_DIRS, set)
        assert all(isinstance(d, str) for d in cnn.SKIP_DIRS)
        # sanity : contient les cles historiques
        for key in (".lake", "_archives", "__pycache__", "foundry-lib"):
            assert key in cnn.SKIP_DIRS

    def test_baseline_path_is_absolute(self):
        assert cnn.BASELINE_PATH.is_absolute()

    def test_link_pattern_matches_basic_markdown_link(self):
        m = cnn.LINK_PATTERN.search("[txt](path.ipynb)")
        assert m is not None
        assert m.group(1) == "txt"
        assert m.group(2) == "path.ipynb"

    def test_link_pattern_skips_http(self):
        assert cnn.LINK_PATTERN.search("[txt](https://example.com)") is None

    def test_link_pattern_skips_mailto(self):
        assert cnn.LINK_PATTERN.search("[txt](mailto:foo@bar)") is None

    def test_link_pattern_skips_anchor_only(self):
        assert cnn.LINK_PATTERN.search("[txt](#section)") is None

    def test_link_pattern_strips_anchor_after_capture(self):
        # group(2) inclut l'ancre (on depouille apres dans _resolve_target)
        m = cnn.LINK_PATTERN.search("[txt](path.ipynb#section)")
        assert m is not None
        assert m.group(2) == "path.ipynb#section"


# ---------------------------------------------------------------------------
# 9. Classification kind=nav vs link (vocabulaire navigation)
# ---------------------------------------------------------------------------
class TestNavKindClassification:
    def test_precedent_keyword_marks_nav(self, tmp_path):
        nb = _write_nb(tmp_path, [("markdown", "[precedent](missing.ipynb)")])
        broken = cnn.scan_notebook(nb)
        assert len(broken) == 1
        assert broken[0]["kind"] == "nav"

    def test_suivant_keyword_marks_nav(self, tmp_path):
        nb = _write_nb(tmp_path, [("markdown", "[suivant](missing.ipynb)")])
        broken = cnn.scan_notebook(nb)
        assert len(broken) == 1
        assert broken[0]["kind"] == "nav"

    def test_index_keyword_marks_nav(self, tmp_path):
        nb = _write_nb(tmp_path, [("markdown", "[Index](missing.ipynb)")])
        broken = cnn.scan_notebook(nb)
        assert len(broken) == 1
        assert broken[0]["kind"] == "nav"

    def test_navigation_keyword_marks_nav(self, tmp_path):
        nb = _write_nb(tmp_path, [("markdown", "[navigation](missing.ipynb)")])
        broken = cnn.scan_notebook(nb)
        assert len(broken) == 1
        assert broken[0]["kind"] == "nav"

    def test_arrows_marks_nav(self, tmp_path):
        nb = _write_nb(tmp_path, [("markdown", "[>>](missing.ipynb)")])
        broken = cnn.scan_notebook(nb)
        assert len(broken) == 1
        assert broken[0]["kind"] == "nav"

    def test_random_word_marks_link(self, tmp_path):
        # aucun mot-cle nav dans le texte -> kind=link
        nb = _write_nb(tmp_path, [("markdown", "[figure explicative](missing.png)")])
        broken = cnn.scan_notebook(nb)
        assert len(broken) == 1
        assert broken[0]["kind"] == "link"
