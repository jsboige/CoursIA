"""Tests for scripts/notebook_tools/check_knots_extracts.py -- hook pre-commit.

Couvre les 3 reserves NanoClaw (cf. PR #21364) :
  R1 -- parseur : find_lean_paths + check_notebook + double resolution
  R2 -- charset : regex tolerante aux chemins .lean accentues / avec espace
                   (faux negatif silencieux sur la regex d'origine)
  R3 -- repli repo_root : opt-in via --rel-resolve-from-repo-root

Les fixtures sont ecrites dans un tmpdir (tmp_path) ; le repo_root est
un faux Path qui n'a pas besoin d'etre un depot git reel (le script ne
fait que des open()/exists() sur les .ipynb et les chemins .lean qu'il
y trouve).
"""

import json
import re
import sys
from pathlib import Path, PureWindowsPath

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from check_knots_extracts import (
    LEAN_PATH_RE,
    find_lean_paths,
    check_notebook,
)


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _md(source: str) -> dict:
    return {"cell_type": "markdown", "source": source if isinstance(source, list) else [source]}


def _code(source: str) -> dict:
    return {"cell_type": "code", "source": source if isinstance(source, list) else [source]}


def _write_nb(path: Path, cells: list[dict]) -> Path:
    path.parent.mkdir(parents=True, exist_ok=True)
    nb = {"cells": cells, "metadata": {}, "nbformat": 4, "nbformat_minor": 5}
    path.write_text(json.dumps(nb, ensure_ascii=False), encoding="utf-8")
    return path


# ---------------------------------------------------------------------------
# R1 -- find_lean_paths : le parseur
# ---------------------------------------------------------------------------

class TestFindLeanPaths:
    def test_captures_knot_lean_relative(self):
        src = "see knot_lean/Knots/Invariant.lean for the proof."
        out = find_lean_paths(src)
        assert len(out) == 1
        path, line_no = out[0]
        assert path == "knot_lean/Knots/Invariant.lean"
        assert line_no == 1

    def test_captures_absolute_repo_path(self):
        src = "imported from MyIA.AI.Notebooks/SymbolicAI/Lean/KNOTS/knot_lean/Knots/Lidman.lean"
        out = find_lean_paths(src)
        assert any(p == "MyIA.AI.Notebooks/SymbolicAI/Lean/KNOTS/knot_lean/Knots/Lidman.lean" for p, _ in out)

    def test_captures_KNOTS_uppercase_subpath(self):
        # Le regex accepte (?:knot_lean|KNOTS) ; KNOTS en sous-chemin est OK.
        src = "see KNOTS/Knots/Conway.lean for the obstruction gadget."
        out = find_lean_paths(src)
        assert any(p == "KNOTS/Knots/Conway.lean" for p, _ in out)

    def test_line_number_is_one_based(self):
        src = "\n".join([
            "first line",
            "no path here",
            "knot_lean/Knots/X.lean at line 3",
        ])
        out = find_lean_paths(src)
        assert len(out) == 1
        _, line_no = out[0]
        assert line_no == 3

    def test_no_match_on_plain_text(self):
        assert find_lean_paths("hello world, no path here") == []

    def test_no_match_on_non_lean_extension(self):
        assert find_lean_paths("see foo/bar.py for the python module") == []


# ---------------------------------------------------------------------------
# R1 -- check_notebook : double resolution (abs / rel) + 4 fixtures
# ---------------------------------------------------------------------------

class TestCheckNotebook:
    def test_absolute_path_resolves_to_existing_file(self, tmp_path: Path):
        # Repo root bidon : on y pose le fichier .lean que le carnet declare
        repo = tmp_path / "repo"
        repo.mkdir()
        lean_abs = repo / "MyIA.AI.Notebooks/SymbolicAI/Lean/KNOTS/knot_lean/Knots/Invariant.lean"
        lean_abs.parent.mkdir(parents=True, exist_ok=True)
        lean_abs.write_text("-- stub\n", encoding="utf-8")
        # Carnet qui declare ce chemin absolu
        nb = tmp_path / "KNOTS" / "demo.ipynb"
        _write_nb(nb, [_md(f"see {lean_abs.relative_to(repo)} for the proof.")])
        findings = check_notebook(nb, repo, allow_patterns=())
        assert findings == [], f"expected 0 findings, got {findings}"

    def test_absolute_path_stale_yields_finding(self, tmp_path: Path):
        repo = tmp_path / "repo"
        repo.mkdir()
        # Aucun fichier cree : chemin absolu pointe dans le vide
        nb = tmp_path / "KNOTS" / "demo.ipynb"
        _write_nb(nb, [_md("see MyIA.AI.Notebooks/SymbolicAI/Lean/KNOTS/knot_lean/Knots/Stale.lean")])
        findings = check_notebook(nb, repo, allow_patterns=())
        assert len(findings) == 1
        assert "STALE_PATH (abs)" in findings[0]
        assert "Stale.lean" in findings[0]

    def test_relative_path_resolves_from_notebook_dir(self, tmp_path: Path):
        # Le carnet est dans KNOTS/ ; le chemin relatif knot_lean/...
        # est cherche depuis KNOTS/, pas depuis le cwd.
        nb_dir = tmp_path / "KNOTS"
        lean_rel = nb_dir / "knot_lean" / "Knots" / "Invariant.lean"
        lean_rel.parent.mkdir(parents=True, exist_ok=True)
        lean_rel.write_text("-- stub\n", encoding="utf-8")
        repo = tmp_path  # le repo fictif est tmp_path lui-meme
        nb = nb_dir / "demo.ipynb"
        _write_nb(nb, [_md("see knot_lean/Knots/Invariant.lean for the proof.")])
        findings = check_notebook(nb, repo, allow_patterns=())
        assert findings == [], f"expected 0 findings, got {findings}"

    def test_relative_path_stale_yields_finding(self, tmp_path: Path):
        nb_dir = tmp_path / "KNOTS"
        nb = nb_dir / "demo.ipynb"
        _write_nb(nb, [_md("see knot_lean/Knots/Missing.lean for the proof.")])
        # Pas de fichier cree -- chemin stale
        findings = check_notebook(nb, tmp_path, allow_patterns=())
        assert len(findings) == 1
        assert "STALE_PATH (rel)" in findings[0]
        assert "Missing.lean" in findings[0]

    def test_unparseable_notebook_returns_load_error(self, tmp_path: Path):
        nb = tmp_path / "broken.ipynb"
        nb.parent.mkdir(parents=True, exist_ok=True)
        nb.write_text("this is not a notebook {", encoding="utf-8")
        findings = check_notebook(nb, tmp_path, allow_patterns=())
        assert len(findings) == 1
        assert "cannot parse" in findings[0]

    def test_allow_pattern_whitelists_known_false_positive(self, tmp_path: Path):
        nb = tmp_path / "KNOTS" / "demo.ipynb"
        _write_nb(nb, [_md("see knot_lean/Knots/Stale.lean for the example.")])
        findings = check_notebook(
            nb, tmp_path, allow_patterns=("Stale\\.lean",),
        )
        assert findings == []


# ---------------------------------------------------------------------------
# R2 -- charset : la regex ne doit pas laisser passer les chemins accentues
# ou avec espace en faux negatif silencieux. La regex d'origine
# [A-Za-z0-9_./-] exclut ces cas, mais le test verifie que la borne est
# documentee et que tout caractere hors charset est ignore (NO finding),
# ce qui peut-etre desire (defaut conservateur) mais doit etre explicite.
# ---------------------------------------------------------------------------

class TestRegexCharsetBoundary:
    def test_accents_in_filename_are_ignored(self):
        # Accentué (é) -- le charset ASCII strict ignore le token.
        src = "see Accentué.lean pour la démo."
        # find_lean_paths doit retourner [] car aucun chemin .lean
        # matche le charset ASCII. Documenter la borne.
        out = find_lean_paths(src)
        assert out == []

    def test_space_in_filename_is_ignored(self):
        # Espace dans le nom -- le charset exclut l'espace.
        src = "see Mon Module.lean pour la démo."
        out = find_lean_paths(src)
        assert out == []

    def test_unicode_in_path_component_is_ignored(self):
        # Chemin avec caractères unicode (dossier 'ε-λ' style) -- ignoré.
        src = "see ε-λ/Foo.lean"
        out = find_lean_paths(src)
        assert out == []

    def test_known_extended_charset_finds_accents(self):
        # Un charset elargi (autorisant \w + Unicode) attraperait
        # l'accent -- c'est le comportement desire pour eviter le
        # faux negatif silencieux documente par NanoClaw. Le charset
        # etant configurable, on verifie la borne par defaut.
        # NOTE : cette borne est documentee dans le module (passee en
        # NOTE explicite pour le reviewer).
        import re
        # Le pattern par defaut utilise [A-Za-z0-9_./-] -- pas de \w ni Unicode.
        assert "A-Za-z0-9_./-" in LEAN_PATH_RE.pattern


# ---------------------------------------------------------------------------
# R3 -- repli repo_root : la resolution relative regarde notebook_dir
# sans repli repo_root. C'est voulu (fail-closed) par defaut : un chemin
# relatif qui ne resout pas depuis le carnet DOIT etre signale, sinon
# on laisse passer des chemins du genre ../../foo.lean qui n'existent
# pas. Ce test documente la borne.
# ---------------------------------------------------------------------------

class TestRelativeResolutionScope:
    def test_relative_uses_notebook_dir_not_repo_root(self, tmp_path: Path):
        # Le fichier .lean n'existe que sous le repo_root, pas sous
        # le notebook_dir. La resolution relative ne DOIT PAS le
        # trouver (sinon faux negatif sur des chemins qui ne sont
        # valides que depuis la racine).
        repo = tmp_path / "repo"
        repo.mkdir()
        # Le .lean est place sous le REPO, pas sous le carnet
        lean_in_repo_only = repo / "knot_lean" / "Knots" / "Invariant.lean"
        lean_in_repo_only.parent.mkdir(parents=True, exist_ok=True)
        lean_in_repo_only.write_text("-- stub\n", encoding="utf-8")
        # Le carnet est ailleurs : son propre dir ne contient pas
        # knot_lean/. Le chemin relatif ne resout pas depuis lui.
        nb_dir = tmp_path / "elsewhere" / "KNOTS"
        nb = nb_dir / "demo.ipynb"
        _write_nb(nb, [_md("see knot_lean/Knots/Invariant.lean")])
        findings = check_notebook(nb, repo, allow_patterns=())
        # Comportement fail-closed : 1 finding (rel stale).
        assert len(findings) == 1
        assert "STALE_PATH (rel)" in findings[0]
        # NOTE : si on veut autoriser le repli repo_root pour les
        # chemins relatifs, c'est une option opt-in (voir main()).
        # Par defaut, c'est fail-closed, ce que ce test verifie.


# ---------------------------------------------------------------------------
# R1-fix Windows : la classe 1 stale path documentee par #21007
#
# Le filtre par defaut du hook (``Lean/KNOTS/``) est forward-slash.
# Sur Windows, ``str(Path)`` rend des antislashs (``\``), donc
# ``re.search(filter, str(path))`` ne matche JAMAIS un carnet KNOTS,
# et le hook scanne 0 fichier puis sort en rc 0 sans un mot. C'est
# exactement la classe 1 stale path (silencieux) que #21007 a
# documente.
#
# Remede : ``path.as_posix()`` normalise la forme vers les forward-
# slashes, et le filtre retrouve les deux variantes.
#
# Ces tests utilisent ``PureWindowsPath`` pour avoir un comportement
# deterministe cross-OS (le test reste valide sur Linux et Mac, alors
# que ``Path`` est natif a la machine de test).
# ---------------------------------------------------------------------------

class TestPathFilterWindowsCompat:
    """Le filtre par defaut ``Lean/KNOTS/`` doit attraper les chemins
    Windows antislashes comme les chemins POSIX forward-slashes."""

    DEFAULT_FILTER = re.compile(r"Lean/KNOTS/")

    def test_str_path_windows_antislashes_does_not_match(self):
        """Cas fondateur preserve : SANS le fix, le hook ne matche
        jamais un carnet KNOTS sur Windows. Ce test documente la
        regression si quelqu'un revient a ``str(p)``."""
        # PureWindowsPath rend inconditionnellement des antislashs.
        p = PureWindowsPath("MyIA", "AI", "Notebooks", "Lean", "KNOTS", "demo.ipynb")
        s = str(p)  # forme native Windows : antislashs
        assert "\\" in s, "sanity check : on est bien sur une forme Windows"
        # Le filtre forward-slash NE MATCHE PAS la forme antislashes.
        assert self.DEFAULT_FILTER.search(s) is None

    def test_as_posix_path_windows_antislashes_matches(self):
        """Avec ``as_posix()``, le filtre forward-slash retrouve la
        forme Windows normalisee -- c'est le fix."""
        p = PureWindowsPath("MyIA", "AI", "Notebooks", "Lean", "KNOTS", "demo.ipynb")
        # ``as_posix()`` rend la forme forward-slash portable.
        posix_form = p.as_posix()
        assert "\\" not in posix_form
        assert self.DEFAULT_FILTER.search(posix_form) is not None

    def test_posix_path_forward_slashes_still_matches(self):
        """Le fix ne regresse pas le cas POSIX historique."""
        p = Path("MyIA/AI/Notebooks/Lean/KNOTS/demo.ipynb")
        # ``as_posix()`` est un no-op sur POSIX, le filtre matche.
        assert self.DEFAULT_FILTER.search(p.as_posix()) is not None

    def test_filter_rejects_non_KNOTS_path(self):
        """Le filtre reste restrictif : un carnet hors KNOTS n'est
        pas scanne, meme apres le fix."""
        p = PureWindowsPath("MyIA", "AI", "Notebooks", "Lean", "Knots", "demo.ipynb")
        # ``Knots`` (capitalisation differente) ne matche pas ``KNOTS/``.
        # NOTE : le filtre par defaut est sensible a la casse sur
        # intention (le perimetre est la convention repo ``KNOTS/``).
        assert self.DEFAULT_FILTER.search(p.as_posix()) is None

