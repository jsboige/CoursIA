#!/usr/bin/env python3
"""Tests pour fix_ipynb_links.py (#18911, geste 2 -- doctrine inversee).

Couvre :
- conversion HTML_404 (sibling `.ipynb` suivi) `.html` -> `.ipynb`
- preservation d'un `.html` sans sibling notebook (page autonome)
- preservation liens absolus / anchor / mailto
- preservation fence ``` ``` ` ` ``` (code blocks)
- idempotence : re-run ne modifie plus rien
- byte-preservation : fins de ligne, encodage UTF-8

Témoins négatifs discriminants :
- un `.html` dont le sibling n'est PAS un notebook suivi reste intact (pas de
  faux positif sur les pages HTML autonomes)
- un `.html` dans une fence n'est PAS converti
- un `.ipynb` (forme correcte depuis l'inversion) n'est jamais touche
"""
from __future__ import annotations

import sys
from pathlib import Path

# Permet l'import du module testé depuis le repertoire parent
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from fix_ipynb_links import (  # noqa: E402
    _HTML_LINK_RE,
    _is_inside_fence,
    count_html_404_links,
    fix_readme_links,
)


def _tmp_readme(tmp_path: Path, content: str, name: str = "README.md") -> Path:
    p = tmp_path / name
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_bytes(content.encode("utf-8"))
    return p


# --- Regex helpers ---

def test_html_link_regex_matches_only_html_suffix():
    """Le regex ne capture que les `.html`, pas les `.ipynb` ou autres."""
    text = "[L](./foo.html) [L](./foo.ipynb) [L](./bar.py)"
    matches = _HTML_LINK_RE.findall(text)
    assert matches == ["./foo.html"], f"unexpected matches: {matches}"


def test_is_inside_fence_no_fence():
    """Sans fence, _is_inside_fence rend False."""
    text = "Hello\nWorld"
    assert _is_inside_fence(text, 5) is False


def test_is_inside_fence_inside_opened_fence():
    """Si une fence ``` ``` ` ` ``` est ouverte au-dessus, la position est dedans."""
    text = "```python\nprint('hello')\n```"
    # position 15 est dans le contenu du bloc
    assert _is_inside_fence(text, 15) is True


def test_is_inside_fence_after_close():
    """Apres fermeture d'une fence, _is_inside_fence rend False."""
    text = "```python\nprint('hello')\n```\nafter"
    # position 32 = apres le ``` de fermeture
    pos_after = text.index("after")
    assert _is_inside_fence(text, pos_after) is False


# --- count_html_404_links ---

def test_count_html_404_links_empty(tmp_path):
    """Un README vide rend 0 violation."""
    p = _tmp_readme(tmp_path, "")
    assert count_html_404_links(p, notebooks=set()) == 0


def test_count_html_404_links_without_sibling_notebook(tmp_path):
    """Un `.html` sans sibling notebook suivi n'est PAS une violation."""
    p = _tmp_readme(tmp_path, "[L](./page.html)\n")
    # notebooks vide -> aucun sibling n'est un notebook suivi
    assert count_html_404_links(p, notebooks=set()) == 0


def _norm(readme: Path, href: str) -> str:
    """Reproduit la normalisation _normalise_readme_target pour les tests."""
    import posixpath
    base = Path(readme).parent
    return posixpath.normpath((base / href).as_posix())


def test_count_html_404_links_with_sibling_notebook(tmp_path):
    """Un `.html` dont le sibling `.ipynb` est suivi EST une violation."""
    p = _tmp_readme(tmp_path, "[L](./foo.html)\n")
    sibling = _norm(p, "./foo.ipynb")
    assert count_html_404_links(p, notebooks={sibling}) == 1


def test_count_html_404_links_absolute_link_ignored(tmp_path):
    """Les liens http(s)://, mailto: et # ne sont pas des cibles de violation."""
    p = _tmp_readme(
        tmp_path,
        "[L](https://example.com/foo.html) "
        "[L](#anchor.html) "
        "[L](mailto:a@b.com)\n",
    )
    assert count_html_404_links(p, notebooks={"https://example.com/foo.ipynb"}) == 0


def test_count_html_404_links_inside_fence_ignored(tmp_path):
    """Un `.html` dans un bloc de code fence n'est PAS une violation."""
    p = _tmp_readme(
        tmp_path,
        "```python\n[fake](./foo.html)\n```\n",
    )
    sibling = _norm(p, "./foo.ipynb")
    assert count_html_404_links(p, notebooks={sibling}) == 0


# --- fix_readme_links : substance ---

def test_fix_html_404(tmp_path):
    """Une violation HTML_404 est convertie en `.ipynb`."""
    p = _tmp_readme(tmp_path, "[L](./foo.html)\n")
    sibling = _norm(p, "./foo.ipynb")
    n, _ = fix_readme_links(p, notebooks={sibling})
    assert n == 1
    assert p.read_text(encoding="utf-8") == "[L](./foo.ipynb)\n"


def test_fix_preserves_html_without_sibling(tmp_path):
    """Un `.html` sans sibling notebook reste intact."""
    p = _tmp_readme(tmp_path, "[L](./page.html)\n")
    n, _ = fix_readme_links(p, notebooks=set())
    assert n == 0
    assert p.read_text(encoding="utf-8") == "[L](./page.html)\n"


def test_fix_preserves_fence(tmp_path):
    """Un `.html` dans un bloc fence reste intact."""
    p = _tmp_readme(
        tmp_path,
        "```python\n[fake](./foo.html)\n```\n",
    )
    sibling = _norm(p, "./foo.ipynb")
    n, _ = fix_readme_links(p, notebooks={sibling})
    assert n == 0
    assert p.read_text(encoding="utf-8") == "```python\n[fake](./foo.html)\n```\n"


def test_fix_idempotent(tmp_path):
    """Re-run sur un fichier deja converti : 0 conversion."""
    p = _tmp_readme(tmp_path, "[L](./foo.html)\n")
    sibling = _norm(p, "./foo.ipynb")
    fix_readme_links(p, notebooks={sibling})
    # 2e run
    n2, _ = fix_readme_links(p, notebooks={sibling})
    assert n2 == 0


def test_fix_preserves_ipynb_form(tmp_path):
    """Un lien `.ipynb` (forme correcte depuis #18911) n'est jamais converti."""
    p = _tmp_readme(tmp_path, "[L](./foo.ipynb)\n")
    sibling = _norm(p, "./foo.ipynb")
    n, _ = fix_readme_links(p, notebooks={sibling})
    assert n == 0
    assert p.read_text(encoding="utf-8") == "[L](./foo.ipynb)\n"


def test_fix_preserves_relative_paths(tmp_path):
    """Les chemins relatifs multi-niveaux sont preserves."""
    p = _tmp_readme(
        tmp_path,
        "[L](../../Other/foo.html)\n",
        name="sub/Inner/README.md",
    )
    sibling = _norm(p, "../../Other/foo.ipynb")
    n, _ = fix_readme_links(p, notebooks={sibling})
    assert n == 1
    assert p.read_text(encoding="utf-8") == "[L](../../Other/foo.ipynb)\n"


def test_fix_mixed_population(tmp_path):
    """Mix HTML_404 + page autonome : seul le HTML_404 est converti."""
    p = _tmp_readme(
        tmp_path,
        "[L1](./rendered.html) [L2](./page.html)\n",
    )
    sibling = _norm(p, "./rendered.ipynb")
    n, _ = fix_readme_links(p, notebooks={sibling})
    assert n == 1
    text = p.read_text(encoding="utf-8")
    assert "[L1](./rendered.ipynb)" in text
    assert "[L2](./page.html)" in text


def test_fix_byte_preserves_crlf(tmp_path):
    """Les fins de ligne CRLF sont preservees."""
    p = _tmp_readme(tmp_path, "[L](./foo.html)\r\n")
    sibling = _norm(p, "./foo.ipynb")
    n, _ = fix_readme_links(p, notebooks={sibling})
    assert n == 1
    # Binaire pour voir CRLF
    raw = p.read_bytes()
    assert b"[L](./foo.ipynb)\r\n" == raw


def test_fix_preserves_utf8_accents(tmp_path):
    """Les accents et caracteres UTF-8 sont preserves byte-a-byte."""
    p = _tmp_readme(
        tmp_path,
        "[L](./café.html) [T](./foo.html)\n",
    )
    sibling = _norm(p, "./foo.ipynb")
    n, _ = fix_readme_links(p, notebooks={sibling})
    assert n == 1
    raw = p.read_bytes()
    # `café.html` (avec e-acute) reste intact
    assert "[L](./café.html)" in raw.decode("utf-8")
    assert "[T](./foo.ipynb)" in raw.decode("utf-8")


def test_main_check_returns_zero_when_no_substance(tmp_path, capsys):
    """--check sur un repertoire sans violation rend exit 0."""
    import subprocess
    # Cible vide -> le test serait sur 0 fichier, return 0
    # On utilise plutot un repertoire sans README
    empty_dir = tmp_path / "empty"
    empty_dir.mkdir()
    result = subprocess.run(
        [sys.executable, str(Path(__file__).resolve().parent.parent / "fix_ipynb_links.py"),
         "--check", str(empty_dir)],
        capture_output=True, text=True, encoding="utf-8", errors="replace",
    )
    assert result.returncode == 0, f"got rc={result.returncode}: {result.stdout} / {result.stderr}"


if __name__ == "__main__":
    import pytest
    sys.exit(pytest.main([__file__, "-v"]))
