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


def test_occupation_F1_unilateral_band_flagged():
    """F1 — bande unilatérale marquée (gap >= 55 %) : le cas fondateur #13223.

    La slide 7 @ 166195bfc porte UNE image collee a droite (gap_left=71.4 %,
    gap_right=2.0 %). L'ancien seuil exigeait EN PLUS une saturation
    verticale, ce qui faisait sortir `n_occupation_flagged: 2` sur 42 cas
    reels — `controle_positif_ok: False` documentait l'inertie sans la
    corriger. F1 attrape ce cas SANS saturation verticale.
    """
    r = {
        "slide": 7,
        "occupation": {
            "n_images": 1, "gap_left_pct": 71.4, "gap_right_pct": 2.0,
            "center_offset_pct": 34.7, "content_bottom": 400,
        },
        "hors_canvas": [],
    }
    assert occupation_flagged(r, 552) is True


def test_occupation_F2_moderate_band_with_offset_flagged():
    """F2 — bande moderee (>= 40 %) + decentrage cumule (|offset| >= 25).

    Reprend la logique 2D : un gap de 40 % sans offset est une composition
    assumee (image au tiers gauche, vide assumee a droite). Un gap de 40 %
    AVEC offset de 30 % EST un desequilibre reel.
    """
    r = {
        "slide": 21,
        "occupation": {
            "n_images": 2, "gap_left_pct": 4.9, "gap_right_pct": 64.5,
            "center_offset_pct": -29.8, "content_bottom": 400,
        },
        "hors_canvas": [],
    }
    assert occupation_flagged(r, 552) is True
    # 40 % SANS offset -> pas de constat (composition assumee)
    r_balanced = {
        "slide": 21,
        "occupation": {
            "n_images": 1, "gap_left_pct": 40.0, "gap_right_pct": 5.0,
            "center_offset_pct": -17.5, "content_bottom": 400,
        },
        "hors_canvas": [],
    }
    assert occupation_flagged(r_balanced, 552) is False


def test_occupation_F3_single_image_strongly_offset_flagged():
    """F3 — image unique tres decentre (n=1, |offset| >= 30).

    Le cas 'image plaquee sur un bord' : sans dispersion pour s'auto-corriger,
    un decentrage >= 30 % est visuellement saillant.
    """
    r = {
        "slide": 23,
        "occupation": {
            "n_images": 1, "gap_left_pct": 62.2, "gap_right_pct": 2.0,
            "center_offset_pct": 30.1, "content_bottom": 400,
        },
        "hors_canvas": [],
    }
    assert occupation_flagged(r, 552) is True
    # dispersion >= 2 images permet de tolerer un offset plus fort
    r_dispersion = {
        "slide": 23,
        "occupation": {
            "n_images": 3, "gap_left_pct": 20.0, "gap_right_pct": 20.0,
            "center_offset_pct": -32.0, "content_bottom": 400,
        },
        "hors_canvas": [],
    }
    assert occupation_flagged(r_dispersion, 552) is False


def test_occupation_F4_legacy_conjunction_preserved():
    """F4 — regression preservee : gap >= 25 + saturation verticale.

    Une composition qui coupe reellement (overflow ou bord frôle) reste
    signalee, independamment des nouvelles formes F1-F3.
    """
    base = {
        "slide": 1,
        "occupation": {"n_images": 2, "gap_left_pct": 30.0, "gap_right_pct": 5.0,
                       "center_offset_pct": -12.0, "content_bottom": 400},
        "hors_canvas": [],
    }
    # gap >= 25 mais PAS de saturation -> pas de constat par F4
    assert occupation_flagged(base, 552) is False
    # gap >= 25 + bord frôle -> constat
    saturated = dict(base)
    saturated["occupation"] = dict(base["occupation"], content_bottom=548)
    assert occupation_flagged(saturated, 552) is True
    # gap >= 25 + débordement contenu -> constat
    overflowing = dict(base, hors_canvas=[{"tag": "P"}])
    assert occupation_flagged(overflowing, 552) is True


def test_occupation_balanced_not_flagged():
    """Composition equilibree : aucune des 4 formes ne doit signaler."""
    r = {
        "slide": 1,
        "occupation": {"n_images": 1, "gap_left_pct": 8.0, "gap_right_pct": 8.0,
                       "center_offset_pct": 0.0, "content_bottom": 400},
        "hors_canvas": [],
    }
    assert occupation_flagged(r, 552) is False


def test_occupation_no_images_not_flagged():
    """Pas d'images : `occupation` est None -> jamais de constat."""
    assert occupation_flagged({"slide": 1, "occupation": None}, 552) is False


def test_controle_positif_warning_when_baseline_omitted():
    """`controle_positif_warning` renseigne un scan SANS baseline.

    Acceptance #13223 : un `controle_positif_ok: null` (scan sans controle
    positif arme) doit etre visible en tete de rapport. Le champ est rendu
    par la logique de build du `report`, pas par l'instrument navigateur.
    """
    import argparse
    import textwrap
    src = (Path(__file__).resolve().parents[1] / "scan_slidev_composition.py").read_text()
    start = src.index("    report = {")
    end_marker = '        "_slide_lines": {str(k): v for k, v in slide_lines.items()},\n    }'
    end = src.index(end_marker, start) + len(end_marker)
    block = textwrap.dedent(src[start:end])

    def _build(baseline_slide):
        ns = {
            "args": argparse.Namespace(baseline_slide=baseline_slide,
                                       baseline_commit="abc" if baseline_slide else None,
                                       slides_md=None, url="http://localhost:8767/"),
            "results": [],
            "content_overflow": lambda r: False,
            "occupation_flagged": lambda r, h: False,
            "slide_lines": {},
            # variables locales de main() — c'est ce que le bloc report lit
            "stale_streaks": [],
            "canvas_w": 980, "canvas_h": 552,
            "BORNE": "ADVISORY",
            "ctrl_positif_ok": None, "ctrl_positif_msg": None,
            "n_total": 0, "n_hors": 0, "n_chev": 0, "n_occ": 0,
        }
        exec(block, ns)
        return ns["report"]

    rpt = _build(None)
    assert rpt["controle_positif_armed"] is False
    assert rpt["controle_positif_warning"] is not None
    assert "sans contrôle positif" in rpt["controle_positif_warning"]
    # et le warning reste None quand le baseline est armé
    rpt2 = _build(7)
    assert rpt2["controle_positif_armed"] is True
    assert rpt2["controle_positif_warning"] is None
