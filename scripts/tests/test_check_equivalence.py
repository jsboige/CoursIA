# -*- coding: utf-8 -*-
"""Tests de check_equivalence.py (#19301, equivalence page/carnet).

Couvre :
- _normalize_line : prefixes Lean, espaces
- extract_outputs : outputs text/plain et stream, exclusion des lignes deja dans sources
- notebook_to_page_url : chemin -> URL
- fetch_page : mock 200, 404, reseau fail
- check_equivalence : EQUIVALENT, LOST_OUTPUTS, MISSING_PAGE, UNKNOWN, NOTEBOOK_ERROR

Le reseau est mocke pour eviter CI reseau (lecon : UNKNOWN = jamais un rouge).
"""

from __future__ import annotations

import importlib.util
import json
import sys
from pathlib import Path
from unittest import mock

import pytest

MODULE_PATH = (Path(__file__).resolve().parents[1] / "notebook_tools"
               / "check_equivalence.py")
spec = importlib.util.spec_from_file_location(
    "check_equivalence", MODULE_PATH)
mod = importlib.util.module_from_spec(spec)
sys.modules["check_equivalence"] = mod
spec.loader.exec_module(mod)


# -----------------------------------------------------------------------------
# _normalize_line
# -----------------------------------------------------------------------------

class TestNormalizeLine:
    def test_simple(self):
        assert mod._normalize_line("hello world") == "hello world"

    def test_lean_prefix_dashes(self):
        # ──────▶ foo -> foo
        assert mod._normalize_line("──────▶ foo") == "foo"

    def test_lean_prefix_dashes_variant(self):
        # ─────── > foo -> foo
        assert mod._normalize_line("───────── > bar") == "bar"

    def test_lean_prefix_double_dash(self):
        # --▶ foo -> foo
        assert mod._normalize_line("---▶ baz") == "baz"

    def test_lean_prefix_equals(self):
        # ===▶ foo -> foo
        assert mod._normalize_line("====▶ qux") == "qux"

    def test_whitespace_collapse(self):
        # "foo   bar" -> "foo bar"
        assert mod._normalize_line("foo   bar") == "foo bar"

    def test_strip(self):
        # "  hello  " -> "hello"
        assert mod._normalize_line("  hello  ") == "hello"

    def test_combined_lean_and_whitespace(self):
        # "──────▶   foo  bar  " -> "foo bar"
        assert mod._normalize_line("──────▶   foo  bar  ") == "foo bar"

    def test_no_prefix_unchanged(self):
        # Sans prefixe, on ne touche pas au contenu
        assert mod._normalize_line("just a normal line") == "just a normal line"

    def test_empty(self):
        # Ligne vide reste vide
        assert mod._normalize_line("") == ""


# -----------------------------------------------------------------------------
# extract_outputs
# -----------------------------------------------------------------------------

def _make_notebook_with_outputs(path: Path, sources: list[str], outputs: list[dict]) -> None:
    """Cree un .ipynb minimal avec sources et outputs specifies."""
    cells = []
    for src in sources:
        cells.append({
            "cell_type": "code",
            "metadata": {},
            "source": [f"{src}\n"],
            "outputs": [],
            "execution_count": 1,
        })
    for out in outputs:
        cells.append({
            "cell_type": "code",
            "metadata": {},
            "source": ["x = 1\n"],
            "outputs": [out],
            "execution_count": 2,
        })
    nb = {
        "cells": cells,
        "metadata": {"kernelspec": {"name": "python3"}},
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    path.write_text(json.dumps(nb, ensure_ascii=False), encoding="utf-8")


class TestExtractOutputs:
    def test_text_plain_output(self, tmp_path):
        nb = tmp_path / "test.ipynb"
        _make_notebook_with_outputs(
            nb,
            sources=["x = 1"],
            outputs=[{
                "output_type": "execute_result",
                "data": {"text/plain": "42"},
                "metadata": {},
            }],
        )
        result = mod.extract_outputs(str(nb))
        assert "42" in result
        assert "x = 1" not in result  # la source est exclue

    def test_stream_output(self, tmp_path):
        nb = tmp_path / "test.ipynb"
        _make_notebook_with_outputs(
            nb,
            sources=["print('hello')"],
            outputs=[{
                "output_type": "stream",
                "name": "stdout",
                "text": "world\n",
            }],
        )
        result = mod.extract_outputs(str(nb))
        assert "world" in result

    def test_display_data_output(self, tmp_path):
        nb = tmp_path / "test.ipynb"
        _make_notebook_with_outputs(
            nb,
            sources=["x = 1"],
            outputs=[{
                "output_type": "display_data",
                "data": {"text/plain": "rendered text"},
                "metadata": {},
            }],
        )
        result = mod.extract_outputs(str(nb))
        assert "rendered text" in result

    def test_excludes_lines_in_sources(self, tmp_path):
        nb = tmp_path / "test.ipynb"
        _make_notebook_with_outputs(
            nb,
            sources=["x = 1"],
            outputs=[{
                "output_type": "stream",
                "name": "stdout",
                "text": "x = 1\n",  # la sortie re-affiche le code source
            }],
        )
        result = mod.extract_outputs(str(nb))
        # La ligne "x = 1" doit etre filtree (deja dans sources)
        assert "x = 1" not in result

    def test_json_malformed_raises(self, tmp_path):
        """Un carnet au JSON invalide leve json.JSONDecodeError, ne rend pas [].

        Leçon revue coord 06/10, c.5994810325 : avant, extract_outputs
        avalsit l'exception et renvoyait [], ce qui faisait EQUIVALENT
        par accident sur un carnet corrompu. Le verdict NOTEBOOK_ERROR
        est dedie.
        """
        import json as _json
        nb = tmp_path / "bad.ipynb"
        nb.write_text("{ not json", encoding="utf-8")
        with pytest.raises(_json.JSONDecodeError):
            mod.extract_outputs(str(nb))

    def test_mime_rendu_text_html_dismiss_text_plain(self, tmp_path):
        """Un `display_data` qui porte `text/html` + `text/plain` ignore le text/plain.

        Leçon revue coord 06/10, c.5994810325 : Quarto rend `text/html`,
        pas `text/plain`. Le text/plain est un fallback que la page
        publiee n'utilise pas. La regle du MIME rendu : ne pas comparer
        le text/plain quand un MIME riche est present.
        """
        nb = tmp_path / "test.ipynb"
        _make_notebook_with_outputs(
            nb,
            sources=["x = 1"],
            outputs=[{
                "output_type": "display_data",
                "data": {
                    "text/html": "<div>42</div>",
                    "text/plain": "should_not_be_compared",
                },
                "metadata": {},
            }],
        )
        result = mod.extract_outputs(str(nb))
        # text/plain ignore (text/html present)
        assert "should_not_be_compared" not in result
        assert "42" not in result  # text/html n'est pas extrait par cet organe
        # Sortie vide : on n'a rien a comparer (le HTML est rendu par Quarto,
        # pas par le carnet).
        assert result == []

    def test_mime_rendu_image_png_dismiss_text_plain(self, tmp_path):
        """Un display_data matplotlib (image/png + text/plain) ignore le text/plain.

        Leçon revue coord 06/10, c.5994810325 : Search-02 et ML-1 ont 8
        lignes `<Figure ...>` qui sont les `text/plain` de figures dont
        le MIME rendu est `image/png`. Avant la regle, ces figures faisaient
        LOST_OUTPUTS. Apres, elles sont EQUIVALENT.
        """
        nb = tmp_path / "test.ipynb"
        _make_notebook_with_outputs(
            nb,
            sources=["plt.show()"],
            outputs=[{
                "output_type": "display_data",
                "data": {
                    "image/png": "iVBORw0KGgoAAAANSUhEUgAA",
                    "text/plain": "<Figure size 432x288 with 1 Axes>",
                },
                "metadata": {},
            }],
        )
        result = mod.extract_outputs(str(nb))
        # text/plain ignore (image/png present)
        assert "Figure" not in result
        assert result == []

    def test_mime_rendu_text_markdown_dismiss_text_plain(self, tmp_path):
        """`text/markdown` est un MIME riche : dismiss text/plain."""
        nb = tmp_path / "test.ipynb"
        _make_notebook_with_outputs(
            nb,
            sources=["md"],
            outputs=[{
                "output_type": "display_data",
                "data": {
                    "text/markdown": "# Title",
                    "text/plain": "should_be_ignored",
                },
                "metadata": {},
            }],
        )
        result = mod.extract_outputs(str(nb))
        assert "should_be_ignored" not in result
        assert result == []

    def test_mime_rendu_text_plain_only_kept(self, tmp_path):
        """Un `display_data` avec UNIQUEMENT text/plain garde le text/plain.

        C'est la regle inverse : sans MIME riche, text/plain est la
        seule sortie et doit etre comparee.
        """
        nb = tmp_path / "test.ipynb"
        _make_notebook_with_outputs(
            nb,
            sources=["x = 1"],
            outputs=[{
                "output_type": "display_data",
                "data": {"text/plain": "rendered value"},
                "metadata": {},
            }],
        )
        result = mod.extract_outputs(str(nb))
        assert "rendered value" in result

    def test_no_code_cells(self, tmp_path):
        nb = tmp_path / "test.ipynb"
        cells = [{
            "cell_type": "markdown",
            "metadata": {},
            "source": ["# Title\n"],
        }]
        (tmp_path / "test.ipynb").write_text(
            json.dumps({"cells": cells, "metadata": {}, "nbformat": 4, "nbformat_minor": 5}),
            encoding="utf-8",
        )
        result = mod.extract_outputs(str(nb))
        assert result == []


# -----------------------------------------------------------------------------
# notebook_to_page_url
# -----------------------------------------------------------------------------

class TestNotebookToPageUrl:
    def test_simple(self):
        """Le prefixe MyIA.AI.Notebooks/ est garde dans l'URL publiee.

        Leçon revue coord 05/10, c.5994810325 : le site gh-pages de jsboige/CoursIA
        garde `MyIA.AI.Notebooks/` dans le path publie. Un retrait causait
        MISSING_PAGE sur tout le corpus reel.
        """
        url = mod.notebook_to_page_url(
            "MyIA.AI.Notebooks/ML/ML.Net/ML-1-Python.ipynb",
            "https://jsboige.github.io/CoursIA",
        )
        assert url == "https://jsboige.github.io/CoursIA/MyIA.AI.Notebooks/ML/ML.Net/ML-1-Python.html"

    def test_with_trailing_slash(self):
        url = mod.notebook_to_page_url(
            "MyIA.AI.Notebooks/ML/ML.Net/ML-1-Python.ipynb",
            "https://jsboige.github.io/CoursIA/",
        )
        assert url == "https://jsboige.github.io/CoursIA/MyIA.AI.Notebooks/ML/ML.Net/ML-1-Python.html"

    def test_absolute_path(self):
        """Un path absolu Windows est normalise en chemin relatif gh-pages.

        L'URL doit oter le prefixe machine (ex. `D:/CoursIA-2/`) et ne
        conserver que la partie publiee a partir de `MyIA.AI.Notebooks/`,
        sinon le `D:/` se retrouve dans l'URL publiee (cf. MISSING_PAGE
        sur tout le corpus reel, docstring de la fonction).
        """
        url = mod.notebook_to_page_url(
            "D:/CoursIA-2/MyIA.AI.Notebooks/Search/Search-01.ipynb",
            "https://jsboige.github.io/CoursIA",
        )
        assert url == "https://jsboige.github.io/CoursIA/MyIA.AI.Notebooks/Search/Search-01.html"

    def test_windows_backslash_normalized(self):
        """Le path Windows avec backslash doit etre normalise en forward slash."""
        url = mod.notebook_to_page_url(
            "D:\\CoursIA-2\\MyIA.AI.Notebooks\\Search\\Search-01.ipynb",
            "https://jsboige.github.io/CoursIA",
        )
        assert "\\\\" not in url
        assert "/MyIA.AI.Notebooks/Search/Search-01.html" in url


# -----------------------------------------------------------------------------
# fetch_page (mock reseau)
# -----------------------------------------------------------------------------

class TestFetchPage:
    def test_200_ok(self):
        fake_resp = mock.MagicMock()
        fake_resp.status = 200
        fake_resp.read.return_value = b"<html><body>OK</body></html>"
        fake_resp.__enter__ = mock.MagicMock(return_value=fake_resp)
        fake_resp.__exit__ = mock.MagicMock(return_value=False)
        with mock.patch("urllib.request.urlopen", return_value=fake_resp):
            status, html, err = mod.fetch_page("https://example.com/page.html")
        assert status == 200
        assert html == "<html><body>OK</body></html>"
        assert err is None

    def test_404_returns_http_error(self):
        import urllib.error
        with mock.patch(
            "urllib.request.urlopen",
            side_effect=urllib.error.HTTPError(
                "https://example.com/missing.html", 404, "Not Found", {}, None
            ),
        ):
            status, html, err = mod.fetch_page("https://example.com/missing.html")
        assert status == 404
        assert html is None
        assert "404" in err

    def test_network_failure_returns_zero(self):
        import urllib.error
        with mock.patch(
            "urllib.request.urlopen",
            side_effect=urllib.error.URLError("DNS resolution failed"),
        ):
            status, html, err = mod.fetch_page("https://nonexistent.invalid/page.html")
        assert status == 0
        assert html is None
        assert "DNS" in err or "url_error" in err

    def test_unexpected_exception(self):
        with mock.patch("urllib.request.urlopen", side_effect=OSError("boom")):
            status, html, err = mod.fetch_page("https://example.com/page.html")
        assert status == 0
        assert html is None
        assert "boom" in err


# -----------------------------------------------------------------------------
# check_equivalence (integration)
# -----------------------------------------------------------------------------

class TestCheckEquivalence:
    def test_equivalent(self, tmp_path):
        nb = tmp_path / "test.ipynb"
        _make_notebook_with_outputs(
            nb,
            sources=["x = 1"],
            outputs=[{
                "output_type": "stream",
                "name": "stdout",
                "text": "42\n",
            }],
        )
        fake_resp = mock.MagicMock()
        fake_resp.status = 200
        fake_resp.read.return_value = b"<html><body>42</body></html>"
        fake_resp.__enter__ = mock.MagicMock(return_value=fake_resp)
        fake_resp.__exit__ = mock.MagicMock(return_value=False)
        with mock.patch("urllib.request.urlopen", return_value=fake_resp):
            verdict = mod.check_equivalence(str(nb))
        assert verdict["verdict"] == "EQUIVALENT"
        assert verdict["found_lines"] == 1
        assert verdict["total_lines"] == 1
        assert verdict["missing_lines"] == []

    def test_html_entities_desechappees(self, tmp_path):
        """Les entites HTML (&quot;, &amp;, etc.) doivent etre deshéchappées.

        Leçon revue coord 05/10 : 528 entités `&quot;` sur une page Search-02
        sans deshéchappage font manquer toutes les chaines text/plain du carnet.
        """
        nb = tmp_path / "test.ipynb"
        _make_notebook_with_outputs(
            nb,
            sources=["print('hello & world')"],
            outputs=[{
                "output_type": "stream",
                "name": "stdout",
                "text": "hello & world\n",
            }],
        )
        # Page avec entites HTML : &amp; -> &, &quot; -> ", &lt; -> <, &gt; -> >
        html_src = "<html>hello &amp; world</html>"
        fake_resp = mock.MagicMock()
        fake_resp.status = 200
        fake_resp.read.return_value = html_src.encode("utf-8")
        fake_resp.__enter__ = mock.MagicMock(return_value=fake_resp)
        fake_resp.__exit__ = mock.MagicMock(return_value=False)
        with mock.patch("urllib.request.urlopen", return_value=fake_resp):
            verdict = mod.check_equivalence(str(nb))
        assert verdict["verdict"] == "EQUIVALENT"
        assert verdict["found_lines"] == 1

    def test_raw_input_output_decorations(self, tmp_path):
        """'Raw input: <ligne>' et 'Raw output: <ligne>' sont des decorations HTML.

        Leçon revue coord 05/10 : Serre100/08 a 28 lignes qui apparaissent dans
        la page entourées de "Raw input: ..." / "Raw output: ...". La recherche
        substring (et non whole-word) doit les considerer comme trouvees.
        """
        nb = tmp_path / "test.ipynb"
        _make_notebook_with_outputs(
            nb,
            sources=["x = 1"],
            outputs=[{
                "output_type": "stream",
                "name": "stdout",
                "text": "42\n",
            }],
        )
        # Page avec decorations widgets Jupyter
        html_src = (
            "<html><body>"
            "<div class='prompt'>Raw input: 42</div>"
            "<div class='output'>Raw output: 42</div>"
            "</body></html>"
        )
        fake_resp = mock.MagicMock()
        fake_resp.status = 200
        fake_resp.read.return_value = html_src.encode("utf-8")
        fake_resp.__enter__ = mock.MagicMock(return_value=fake_resp)
        fake_resp.__exit__ = mock.MagicMock(return_value=False)
        with mock.patch("urllib.request.urlopen", return_value=fake_resp):
            verdict = mod.check_equivalence(str(nb))
        assert verdict["verdict"] == "EQUIVALENT"
        assert verdict["found_lines"] == 1

    def test_url_garde_prefixe(self, tmp_path):
        """L'URL doit garder MyIA.AI.Notebooks/ dans le rel (cf test_simple)."""
        # Le carnet doit inclure MyIA.AI.Notebooks/ dans son path pour
        # que le test reflemente l'usage reel.
        sub = tmp_path / "MyIA.AI.Notebooks" / "Search"
        sub.mkdir(parents=True)
        nb = sub / "Search-01.ipynb"
        _make_notebook_with_outputs(
            nb,
            sources=["x = 1"],
            outputs=[{
                "output_type": "stream",
                "name": "stdout",
                "text": "42\n",
            }],
        )
        fake_resp = mock.MagicMock()
        fake_resp.status = 200
        fake_resp.read.return_value = b"<html>42</html>"
        fake_resp.__enter__ = mock.MagicMock(return_value=fake_resp)
        fake_resp.__exit__ = mock.MagicMock(return_value=False)
        with mock.patch("urllib.request.urlopen", return_value=fake_resp):
            verdict = mod.check_equivalence(str(nb))
        # Le path complet inclut MyIA.AI.Notebooks/
        assert "MyIA.AI.Notebooks" in verdict["page_url"]
        assert verdict["page_url"].endswith(".html")

    def test_lost_outputs(self, tmp_path):
        nb = tmp_path / "test.ipynb"
        _make_notebook_with_outputs(
            nb,
            sources=["x = 1"],
            outputs=[{
                "output_type": "stream",
                "name": "stdout",
                "text": "secret_value_xyz\n",
            }],
        )
        fake_resp = mock.MagicMock()
        fake_resp.status = 200
        fake_resp.read.return_value = b"<html><body>autre chose</body></html>"
        fake_resp.__enter__ = mock.MagicMock(return_value=fake_resp)
        fake_resp.__exit__ = mock.MagicMock(return_value=False)
        with mock.patch("urllib.request.urlopen", return_value=fake_resp):
            verdict = mod.check_equivalence(str(nb))
        assert verdict["verdict"] == "LOST_OUTPUTS"
        assert verdict["found_lines"] == 0
        assert "secret_value_xyz" in verdict["missing_lines"]

    def test_missing_page(self, tmp_path):
        nb = tmp_path / "test.ipynb"
        _make_notebook_with_outputs(
            nb,
            sources=["x = 1"],
            outputs=[{"output_type": "stream", "name": "stdout", "text": "x\n"}],
        )
        import urllib.error
        with mock.patch(
            "urllib.request.urlopen",
            side_effect=urllib.error.HTTPError(
                "https://example.com/test.html", 404, "Not Found", {}, None
            ),
        ):
            verdict = mod.check_equivalence(str(nb))
        assert verdict["verdict"] == "MISSING_PAGE"
        assert verdict["status"] == 404

    def test_unknown_network(self, tmp_path):
        nb = tmp_path / "test.ipynb"
        _make_notebook_with_outputs(
            nb,
            sources=["x = 1"],
            outputs=[{"output_type": "stream", "name": "stdout", "text": "x\n"}],
        )
        import urllib.error
        with mock.patch(
            "urllib.request.urlopen",
            side_effect=urllib.error.URLError("timeout"),
        ):
            verdict = mod.check_equivalence(str(nb))
        assert verdict["verdict"] == "UNKNOWN"
        assert verdict["error"] is not None

    def test_notebook_not_found(self):
        verdict = mod.check_equivalence("/nonexistent/path/to/carnet.ipynb")
        assert verdict["verdict"] == "NOTEBOOK_ERROR"
        assert "not found" in verdict["error"]

    def test_notebook_corrupt_renders_notebook_error(self, tmp_path):
        """Un carnet JSON invalide rend NOTEBOOK_ERROR, pas EQUIVALENT.

        Leçon revue coord 06/10, c.5994810325 : avant, extract_outputs
        avalsit l'exception et renvoyait [], ce qui faisait passer un
        carnet corrompu en EQUIVALENT. Maintenant l'exception remonte
        et check_equivalence traduit en NOTEBOOK_ERROR.
        """
        nb = tmp_path / "test.ipynb"
        nb.write_text("{ not json", encoding="utf-8")
        fake_resp = mock.MagicMock()
        fake_resp.status = 200
        fake_resp.read.return_value = b"<html>anything</html>"
        fake_resp.__enter__ = mock.MagicMock(return_value=fake_resp)
        fake_resp.__exit__ = mock.MagicMock(return_value=False)
        with mock.patch("urllib.request.urlopen", return_value=fake_resp):
            verdict = mod.check_equivalence(str(nb))
        assert verdict["verdict"] == "NOTEBOOK_ERROR"
        assert "JSONDecodeError" in verdict["error"] or "json" in verdict["error"].lower()

    def test_matplotlib_figure_is_equivalent(self, tmp_path):
        """Une figure matplotlib (image/png + text/plain) ne fait plus LOST_OUTPUTS.

        Leçon revue coord 06/10, c.5994810325 : avec la regle du MIME
        rendu, un `display_data` qui porte `image/png` est ignore pour
        la comparaison (le text/plain n'est pas rendu par Quarto). La
        page peut etre EQUIVALENT, plus LOST_OUTPUTS.
        """
        nb = tmp_path / "test.ipynb"
        _make_notebook_with_outputs(
            nb,
            sources=["plt.show()"],
            outputs=[{
                "output_type": "display_data",
                "data": {
                    "image/png": "iVBORw0KGgoAAAANSUhEUgAA",
                    "text/plain": "<Figure size 432x288 with 1 Axes>",
                },
                "metadata": {},
            }],
        )
        # Page déployée : pas de mention du text/plain (Quarto rend le PNG).
        fake_resp = mock.MagicMock()
        fake_resp.status = 200
        fake_resp.read.return_value = b"<html><body><img src='figure.png'/></body></html>"
        fake_resp.__enter__ = mock.MagicMock(return_value=fake_resp)
        fake_resp.__exit__ = mock.MagicMock(return_value=False)
        with mock.patch("urllib.request.urlopen", return_value=fake_resp):
            verdict = mod.check_equivalence(str(nb))
        # Plus de text/plain a comparer (regle du MIME rendu) -> EQUIVALENT
        assert verdict["verdict"] == "EQUIVALENT"
        assert verdict["total_lines"] == 0
        assert verdict["found_lines"] == 0

    def test_lean_prefix_in_page(self, tmp_path):
        """Un prefixe Lean dans la page ne doit pas bloquer la detection."""
        nb = tmp_path / "test.ipynb"
        _make_notebook_with_outputs(
            nb,
            sources=["x = 1"],
            outputs=[{
                "output_type": "stream",
                "name": "stdout",
                "text": "alpha beta\n",
            }],
        )
        # Page avec prefixe Lean ──────▶
        fake_resp = mock.MagicMock()
        fake_resp.status = 200
        # Encode la page avec prefixes Lean ; bytes literal ne peut pas porter
        # d'unicode non-ASCII, on encode donc la chaîne en utf-8.
        page_html = "<html><body>──────▶ alpha beta ──────▶</body></html>"
        fake_resp.read.return_value = page_html.encode("utf-8")
        fake_resp.__enter__ = mock.MagicMock(return_value=fake_resp)
        fake_resp.__exit__ = mock.MagicMock(return_value=False)
        with mock.patch("urllib.request.urlopen", return_value=fake_resp):
            verdict = mod.check_equivalence(str(nb))
        # La normalisation doit permettre la detection
        assert verdict["verdict"] == "EQUIVALENT"
        assert verdict["found_lines"] == 1


# -----------------------------------------------------------------------------
# main() : codes de sortie (CLI)
# -----------------------------------------------------------------------------

class TestMainCLI:
    def test_cli_equivalent(self, tmp_path):
        nb = tmp_path / "test.ipynb"
        _make_notebook_with_outputs(
            nb,
            sources=["x = 1"],
            outputs=[{"output_type": "stream", "name": "stdout", "text": "42\n"}],
        )
        fake_resp = mock.MagicMock()
        fake_resp.status = 200
        fake_resp.read.return_value = b"<html>42</html>"
        fake_resp.__enter__ = mock.MagicMock(return_value=fake_resp)
        fake_resp.__exit__ = mock.MagicMock(return_value=False)
        with mock.patch("urllib.request.urlopen", return_value=fake_resp):
            rc = mod.main(["--notebook", str(nb), "--report"])
        assert rc == 0

    def test_cli_lost_outputs(self, tmp_path):
        nb = tmp_path / "test.ipynb"
        _make_notebook_with_outputs(
            nb,
            sources=["x = 1"],
            outputs=[{"output_type": "stream", "name": "stdout", "text": "secret\n"}],
        )
        fake_resp = mock.MagicMock()
        fake_resp.status = 200
        fake_resp.read.return_value = b"<html>autre</html>"
        fake_resp.__enter__ = mock.MagicMock(return_value=fake_resp)
        fake_resp.__exit__ = mock.MagicMock(return_value=False)
        with mock.patch("urllib.request.urlopen", return_value=fake_resp):
            rc = mod.main(["--notebook", str(nb), "--json"])
        assert rc == 1

    def test_cli_missing_page(self, tmp_path):
        nb = tmp_path / "test.ipynb"
        _make_notebook_with_outputs(
            nb,
            sources=["x = 1"],
            outputs=[{"output_type": "stream", "name": "stdout", "text": "x\n"}],
        )
        import urllib.error
        with mock.patch(
            "urllib.request.urlopen",
            side_effect=urllib.error.HTTPError("url", 404, "Not Found", {}, None),
        ):
            rc = mod.main(["--notebook", str(nb), "--report"])
        assert rc == 2

    def test_cli_unknown_network(self, tmp_path):
        nb = tmp_path / "test.ipynb"
        _make_notebook_with_outputs(
            nb,
            sources=["x = 1"],
            outputs=[{"output_type": "stream", "name": "stdout", "text": "x\n"}],
        )
        import urllib.error
        with mock.patch(
            "urllib.request.urlopen",
            side_effect=urllib.error.URLError("timeout"),
        ):
            rc = mod.main(["--notebook", str(nb), "--report"])
        assert rc == 3

    def test_cli_notebook_error(self):
        rc = mod.main(["--notebook", "/nonexistent.ipynb", "--report"])
        assert rc == 4
