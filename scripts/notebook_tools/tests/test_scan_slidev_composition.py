"""Tests unitaires du splitter source + heuristiques de scan_slidev_composition.

La partie navigateur (mesure Playwright) est couverte par le contrôle positif
(run_composition_control.py, fixture 6cabc826b) — pas par ces tests.
"""

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from scan_slidev_composition import (  # noqa: E402
    content_overflow,
    occupation_flagged,
    parse_headmatter_canvas,
    split_slides_source,
)


DECK = """---
theme: ../theme-ia101
paginate: true
drawings:
  persist: false
layout: cover
---


# Titre cover

---

# Sommaire

- point A
- point B

---
layout: section
---



# Intelligence artificielle

- Introduction
- Agents

---



# Contenu avec image

Voici du texte.

```python
# un --- dans une fence ne doit PAS séparer
x = 1
```

---
"""


def test_split_counts_and_lines():
    slides = split_slides_source(DECK)
    # cover, sommaire, divider, contenu = 4 slides (2 frontmatter exclues)
    assert len(slides) == 4, [s["start_line"] for s in slides]
    lines = DECK.split("\n")
    assert lines[slides[0]["start_line"] - 1].strip() == "# Titre cover"
    assert lines[slides[1]["start_line"] - 1].strip() == "# Sommaire"
    # le divider (# Title + puces) NE doit PAS être avalé comme frontmatter
    assert lines[slides[2]["start_line"] - 1].strip() == "# Intelligence artificielle"
    assert lines[slides[3]["start_line"] - 1].strip() == "# Contenu avec image"


def test_split_fence_aware():
    slides = split_slides_source(DECK)
    # la fence contenant '---' ne crée pas de slide fantôme
    assert len(slides) == 4


def test_yaml_nested_indent_not_a_slide():
    # la clé indentée (persist: false) reste dans la frontmatter globale :
    # le bloc '# Titre cover' est bien la slide 1
    slides = split_slides_source(DECK)
    assert slides[0]["start_line"] == DECK.split("\n").index("# Titre cover") + 1


def test_canvas_defaults_and_overrides(tmp_path):
    p = tmp_path / "slides.md"
    p.write_text(DECK, encoding="utf-8")
    assert parse_headmatter_canvas(p) == (980, 552)

    custom = DECK.replace("layout: cover", "layout: cover\ncanvasWidth: 1280\ncanvasHeight: 720")
    p.write_text(custom, encoding="utf-8")
    assert parse_headmatter_canvas(p) == (1280, 720)

    ratio = DECK.replace("theme: ../theme-ia101", "theme: x\naspectRatio: 4/3")
    p.write_text(ratio, encoding="utf-8")
    assert parse_headmatter_canvas(p) == (4, 3)


def test_content_overflow_ignores_container_only_boxes():
    # un DIV conteneur qui déborde seul (slidev-layout [0,0,980,587]) = boîte
    # CSS, pas un défaut visuel
    assert content_overflow({"hors_canvas": [
        {"tag": "DIV", "cls": "slidev-layout default", "bbox": [0, 0, 980, 587]}
    ]}) is False
    # le même conteneur AVEC un enfant texte/image qui déborde = défaut réel
    assert content_overflow({"hors_canvas": [
        {"tag": "DIV", "cls": "slidev-layout default", "bbox": [0, 0, 980, 587]},
        {"tag": "LI", "cls": "", "bbox": [48, 581, 932, 609]},
    ]}) is True
    assert content_overflow({"hors_canvas": [
        {"tag": "IMG", "cls": "", "bbox": [327, 0, 653, 700]}
    ]}) is True
    # pré/code (bloc de code qui déborde) = contenu
    assert content_overflow({"hors_canvas": [
        {"tag": "PRE", "cls": "shiki", "bbox": [48, 472, 932, 722]}
    ]}) is True
    # pas d'item -> pas de défaut
    assert content_overflow({"hors_canvas": []}) is False


def test_occupation_requires_side_empty_AND_vertical_saturation():
    base = {
        "slide": 1,
        "occupation": {"gap_left_pct": 67.0, "gap_right_pct": 2.0, "content_bottom": 400},
        "hors_canvas": [],
    }
    # bande vide mais PAS de saturation verticale -> pas de constat
    assert occupation_flagged(base, 552) is False
    # bande vide + bord frôlé -> constat
    saturated = dict(base)
    saturated["occupation"] = dict(base["occupation"], content_bottom=548)
    assert occupation_flagged(saturated, 552) is True
    # bande vide + débordement -> constat
    overflowing = dict(base, hors_canvas=[{"tag": "P"}])
    assert occupation_flagged(overflowing, 552) is True
    # pas de bande vide -> jamais
    balanced = dict(base)
    balanced["occupation"] = {"gap_left_pct": 10.0, "gap_right_pct": 10.0, "content_bottom": 548}
    assert occupation_flagged(balanced, 552) is False
    # pas d'images -> jamais
    assert occupation_flagged({"slide": 1, "occupation": None}, 552) is False
