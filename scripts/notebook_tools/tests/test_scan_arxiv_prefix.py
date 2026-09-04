"""Tests du fix #14435 (rem. 3) : l'ID legacy arXiv garde son préfixe d'archive.

Un identifiant ancien réduit à ses 7 chiffres est rejeté par l'API arXiv
(400) — le préfixe (`cs/`, `quant-ph/`, `cat/`, `math.AG/`) FAIT partie de
l'identifiant. Ces tests échouent si un scanner se remet à le capturer nu.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from scan_arxiv_citations import scan_notebook  # noqa: E402
from scan_pr_arxiv_diff import extract_arxiv_from_text  # noqa: E402


def _nb(tmp_path, md_text):
    """Écrire un notebook minimal d'une cellule markdown, retourner son chemin."""
    import nbformat
    nb = nbformat.v4.new_notebook()
    nb.cells = [nbformat.v4.new_markdown_cell(md_text)]
    p = tmp_path / "nb.ipynb"
    nbformat.write(nb, p)
    return p


class TestPrefixedLegacyIds:
    def test_prefixed_id_keeps_its_prefix_scan_citations(self, tmp_path):
        p = _nb(tmp_path, "Voir arXiv:cs/0011047 pour le détail.")
        assert scan_notebook(p) == [(0, "cs/0011047")]

    def test_prefixed_subject_id_keeps_prefix_scan_citations(self, tmp_path):
        p = _nb(tmp_path, "arXiv:math.AG/0309136 et arXiv:quant-ph/0604079.")
        assert {aid for _, aid in scan_notebook(p)} == {"math.AG/0309136", "quant-ph/0604079"}

    def test_cat_prefix_is_a_valid_archive_prefix(self, tmp_path):
        # `cat` matche [a-z\-]+ -- le cas nommé par #14435 rem. 3.
        p = _nb(tmp_path, "arXiv:cat/0703165.")
        assert scan_notebook(p) == [(0, "cat/0703165")]

    def test_prefixed_id_keeps_its_prefix_pr_diff(self):
        assert extract_arxiv_from_text("arXiv:cs/0011047") == {"cs/0011047"}

    def test_bare_seven_digit_id_unchanged(self):
        # Un legacy SANS préfixe reste nu (l'auteur l'a écrit ainsi).
        assert extract_arxiv_from_text("arXiv:0703123") == {"0703123"}
        assert extract_arxiv_from_text("arXiv:0703123") == {"0703123"}

    def test_modern_id_unchanged(self):
        assert extract_arxiv_from_text("arXiv:2301.12345") == {"2301.12345"}
        assert extract_arxiv_from_text("arXiv:2301.12345, arXiv:cs/0011047") == {
            "2301.12345", "cs/0011047"
        }

    def test_eight_digit_sequence_is_not_legacy(self):
        # 8 chiffres : ni moderne (pas de point) ni legacy (7 chiffres) -> rien.
        assert extract_arxiv_from_text("arXiv:07031234") == set()


class TestGuardAgainstRegression:
    def test_regex_capture_group_includes_prefix(self):
        import scan_pr_arxiv_diff as spd
        m = spd.ARXIV_RE_LEGACY.search("arXiv:quant-ph/0604079")
        assert m is not None
        assert m.group(1) == "quant-ph/0604079"  # nu : "0604079" = le défaut
