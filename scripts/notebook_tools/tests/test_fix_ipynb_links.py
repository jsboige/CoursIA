#!/usr/bin/env python3
"""Tests pour fix_ipynb_links.py (#18911).

Couvre :
- conversion STALE_LINK (cible dans render-list) `.ipynb` -> `.html`
- preservation UNRENDERED (cible hors render-list, garde #11451)
- preservation liens absolus / anchor / mailto
- preservation fence ``` ``` ` ` ``` (code blocks)
- idempotence : re-run ne modifie plus rien
- byte-preservation : fins de ligne, encodage UTF-8

Témoin négatif discriminant (Tell c.4 strict fondateur) :
- un run sans cible dans la render-list doit retourner 0 modification (pas de
  faux positif sur UNRENDERED)
- un run avec une fence englobant un `.ipynb` ne doit PAS convertir
- une cible `.ipynb` deja en `.html` doit etre intacte (idempotence)
"""
from __future__ import annotations

import sys
from pathlib import Path

# Permet l'import du module testé depuis le repertoire parent
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from fix_ipynb_links import (  # noqa: E402
    _IPYNB_LINK_RE,
    _is_inside_fence,
    count_stale_links,
    fix_readme_links,
)


def _tmp_readme(tmp_path: Path, content: str, name: str = "README.md") -> Path:
    p = tmp_path / name
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_bytes(content.encode("utf-8"))
    return p


# --- Regex helpers ---

def test_ipynb_link_regex_matches_only_ipynb_suffix():
    """Le regex ne capture que les `.ipynb`, pas les `.html` ou autres."""
    text = "[L](./foo.ipynb) [L](./foo.html) [L](./bar.py)"
    matches = _IPYNB_LINK_RE.findall(text)
    assert matches == ["./foo.ipynb"], f"unexpected matches: {matches}"


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


# --- count_stale_links ---

def test_count_stale_links_empty(tmp_path):
    """Un README vide rend 0 violation."""
    p = _tmp_readme(tmp_path, "")
    assert count_stale_links(p, rendered=set()) == 0


def test_count_stale_links_with_unrendered_target(tmp_path):
    """Une cible hors render-list n'est PAS une violation STALE_LINK."""
    p = _tmp_readme(tmp_path, "[L](./unrendered.ipynb)\n")
    # rendered set vide -> aucune cible n'est dans la render-list
    assert count_stale_links(p, rendered=set()) == 0


def _norm(readme: Path, href: str) -> str:
    """Reproduit la normalisation _normalise_readme_target pour les tests."""
    import posixpath
    base = Path(readme).parent
    return posixpath.normpath((base / href).as_posix())


def test_count_stale_links_with_rendered_target(tmp_path):
    """Une cible dans la render-list EST une violation STALE_LINK."""
    p = _tmp_readme(tmp_path, "[L](./foo.ipynb)\n")
    target = _norm(p, "./foo.ipynb")
    assert count_stale_links(p, rendered={target}) == 1


def test_count_stale_links_absolute_link_ignored(tmp_path):
    """Les liens http(s)://, mailto: et # ne sont pas des cibles de violation."""
    p = _tmp_readme(
        tmp_path,
        "[L](https://example.com/foo.ipynb) "
        "[L](#anchor.ipynb) "
        "[L](mailto:a@b.com)\n",
    )
    # rendered contient la clee normalisee de foo.ipynb MAIS le href est absolu -> ignore
    assert count_stale_links(p, rendered={"https://example.com/foo.ipynb"}) == 0


def test_count_stale_links_inside_fence_ignored(tmp_path):
    """Une cible `.ipynb` dans un bloc de code fence n'est PAS une violation."""
    p = _tmp_readme(
        tmp_path,
        "```python\n[fake](./foo.ipynb)\n```\n",
    )
    target = _norm(p, "./foo.ipynb")
    assert count_stale_links(p, rendered={target}) == 0


# --- fix_readme_links : substance ---

def test_fix_stale_link(tmp_path):
    """Une violation STALE_LINK est convertie en `.html`."""
    p = _tmp_readme(tmp_path, "[L](./foo.ipynb)\n")
    target = _norm(p, "./foo.ipynb")
    n, _ = fix_readme_links(p, rendered={target})
    assert n == 1
    assert p.read_text(encoding="utf-8") == "[L](./foo.html)\n"


def test_fix_preserves_unrendered(tmp_path):
    """Une cible hors render-list reste intacte."""
    p = _tmp_readme(tmp_path, "[L](./foo.ipynb)\n")
    n, _ = fix_readme_links(p, rendered=set())
    assert n == 0
    assert p.read_text(encoding="utf-8") == "[L](./foo.ipynb)\n"


def test_fix_preserves_fence(tmp_path):
    """Une cible dans un bloc fence reste intacte."""
    p = _tmp_readme(
        tmp_path,
        "```python\n[fake](./foo.ipynb)\n```\n",
    )
    target = _norm(p, "./foo.ipynb")
    n, _ = fix_readme_links(p, rendered={target})
    assert n == 0
    assert p.read_text(encoding="utf-8") == "```python\n[fake](./foo.ipynb)\n```\n"


def test_fix_idempotent(tmp_path):
    """Re-run sur un fichier deja converti : 0 conversion."""
    p = _tmp_readme(tmp_path, "[L](./foo.ipynb)\n")
    target = _norm(p, "./foo.ipynb")
    fix_readme_links(p, rendered={target})
    # 2e run
    n2, _ = fix_readme_links(p, rendered={target})
    assert n2 == 0


def test_fix_preserves_relative_paths(tmp_path):
    """Les chemins relatifs multi-niveaux sont preserves."""
    p = _tmp_readme(
        tmp_path,
        "[L](../../Other/foo.ipynb)\n",
        name="sub/Inner/README.md",
    )
    target = _norm(p, "../../Other/foo.ipynb")
    n, _ = fix_readme_links(p, rendered={target})
    assert n == 1
    assert p.read_text(encoding="utf-8") == "[L](../../Other/foo.html)\n"


def test_fix_mixed_population(tmp_path):
    """Mix STALE_LINK + UNRENDERED : seul le STALE_LINK est converti."""
    p = _tmp_readme(
        tmp_path,
        "[L1](./rendered.ipynb) [L2](./unrendered.ipynb)\n",
    )
    rendered_target = _norm(p, "./rendered.ipynb")
    n, _ = fix_readme_links(p, rendered={rendered_target})
    assert n == 1
    text = p.read_text(encoding="utf-8")
    assert "[L1](./rendered.html)" in text
    assert "[L2](./unrendered.ipynb)" in text


def test_fix_byte_preserves_crlf(tmp_path):
    """Les fins de ligne CRLF sont preservees."""
    p = _tmp_readme(tmp_path, "[L](./foo.ipynb)\r\n")
    target = _norm(p, "./foo.ipynb")
    n, _ = fix_readme_links(p, rendered={target})
    assert n == 1
    # Binaire pour voir CRLF
    raw = p.read_bytes()
    assert b"[L](./foo.html)\r\n" == raw


def test_fix_preserves_utf8_accents(tmp_path):
    """Les accents et caracteres UTF-8 sont preserves byte-a-byte."""
    p = _tmp_readme(
        tmp_path,
        "[L](./café.ipynb) [T](./foo.ipynb)\n",
    )
    target = _norm(p, "./foo.ipynb")
    n, _ = fix_readme_links(p, rendered={target})
    assert n == 1
    raw = p.read_bytes()
    # `café.ipynb` (avec e-acute) reste intact
    assert "[L](./café.ipynb)" in raw.decode("utf-8")
    assert "[T](./foo.html)" in raw.decode("utf-8")


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
        capture_output=True, text=True,
    )
    assert result.returncode == 0, f"got rc={result.returncode}: {result.stdout} / {result.stderr}"


if __name__ == "__main__":
    import pytest
    sys.exit(pytest.main([__file__, "-v"]))