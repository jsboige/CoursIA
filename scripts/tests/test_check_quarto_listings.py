"""Contrôles des motifs des listings Quarto (#25680)."""
from pathlib import Path

from scripts.check_quarto_listings import check_document


def test_listings_scalar_and_multiple_patterns(tmp_path: Path) -> None:
    (tmp_path / "Infer-02.ipynb").touch()
    (tmp_path / "Infer-03.ipynb").touch()
    doc = tmp_path / "index.qmd"
    doc.write_text('''---
listing:
  - id: models
    contents:
      - "Infer-0[2-3].ipynb"
      - "Infer-04.ipynb"
  - id: empty
    contents: "missing-*.ipynb"
---
''', encoding="utf-8")
    errors = check_document(doc)
    assert len(errors) == 2
    assert "Infer-04.ipynb" in errors[0]
    assert "missing-*.ipynb" in errors[1]
    (tmp_path / "Infer-04.ipynb").touch()
    (tmp_path / "missing-one.ipynb").touch()
    assert check_document(doc) == []


def test_unsupported_pattern_is_not_silently_ignored(tmp_path: Path) -> None:
    doc = tmp_path / "index.qmd"
    doc.write_text('---\nlisting:\n  contents: "!excluded/*"\n---\n', encoding="utf-8")
    assert "non pris en charge" in check_document(doc)[0]
