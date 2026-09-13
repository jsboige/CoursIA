#!/usr/bin/env python3
r"""Tests scan_slidev_composition -- signal RECOUVREMENT texte x image (#15351).

La mesure navigateur est couverte par le controle positif live
(--baseline-slide) ; ces tests epinent les parties PURES du livrable :
le format de sortie par occurrence (acceptance 3 : un numero de slide
seul n'est pas actionnable) et la non-regression des annotations
historiques (HORS_CANVAS, CHEVAUCHEMENT, OCCUPATION).
"""
from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "notebook_tools"))

import scan_slidev_composition as ssc  # noqa: E402


def _report(results, canvas=(980, 552)):
    return {
        "canvas": list(canvas),
        "url": "http://localhost:8767/",
        "baseline_slide": None,
        "baseline_commit": None,
        "n_slides": len(results),
        "results": results,
        "_slide_lines": {str(r["slide"]): 100 + r["slide"] * 10 for r in results},
    }


RECOUV = {
    "texte": "1940-70 : Enthousiasme des debuts",
    "texte_bbox": [90, 152, 475, 185],
    "image": "img_006.png",
    "image_bbox_rendu": [470, 143, 1253, 415],
    "overlap": [4, 33],
    "alpha_zone": 1.0,
}


class TestGithubAnnotationsRecouvrement:
    def test_annotation_par_occurrence_actionnable(self):
        """Acceptance 3 : chaque occurrence cite le texte recouvert,
        l'image, les deux bbox, l'overlap -- pas un numero de slide seul."""
        r = {
            "slide": 5, "text_head": "1940-70 Enthousiasme",
            "hors_canvas": [], "chevauchements": [],
            "recouvrements": [dict(RECOUV), {**RECOUV, "texte": "autre ligne",
                                             "image": "img_008.jpg",
                                             "alpha_zone": 1.0}],
            "occupation": None,
        }
        lines = ssc.github_annotations(_report([r]), Path("slides/S3/slides.md"))
        rec = [l for l in lines if "RECOUVREMENT-TEXTE-IMAGE" in l]
        assert len(rec) == 2, "une annotation par occurrence"
        first = rec[0]
        assert "file=slides/S3/slides.md,line=150" in first  # mapping ligne source
        assert "Enthousiasme des debuts" in first
        assert "img_006.png" in first
        assert "overlap=[4, 33]px" in first
        assert "alpha=1.0" in first
        assert "texte_bbox=[90, 152, 475, 185]" in first
        assert "img_rendu=[470, 143, 1253, 415]" in first
        assert "slide 5" in first

    def test_annotation_tronque_le_texte_long(self):
        r = {
            "slide": 7, "text_head": "x",
            "hors_canvas": [], "chevauchements": [],
            "recouvrements": [{**RECOUV, "texte": "mot " * 40}],
            "occupation": None,
        }
        lines = ssc.github_annotations(_report([r]), Path("slides.md"))
        rec = next(l for l in lines if "RECOUVREMENT-TEXTE-IMAGE" in l)
        assert "mot mot" in rec
        assert "mot mot mot mot mot mot mot mot mot mot mot" not in rec, (
            "le texte cite doit etre tronque (40 chars) pour rester lisible"
        )

    def test_max_trois_annotations_par_slide(self):
        """Borne anti-bruit, conformement aux autres signaux ([:3])."""
        r = {
            "slide": 9, "text_head": "x",
            "hors_canvas": [], "chevauchements": [],
            "recouvrements": [dict(RECOUV, texte=f"ligne {i}") for i in range(6)],
            "occupation": None,
        }
        lines = ssc.github_annotations(_report([r]), Path("slides.md"))
        assert len([l for l in lines if "RECOUVREMENT-TEXTE-IMAGE" in l]) == 3

    def test_slide_sans_recouvrement_n_emet_rien(self):
        r = {
            "slide": 2, "text_head": "propre",
            "hors_canvas": [], "chevauchements": [],
            "recouvrements": [], "occupation": None,
        }
        lines = ssc.github_annotations(_report([r]), Path("slides.md"))
        assert not any("RECOUVREMENT" in l for l in lines)
        # la notice plancher advisory reste
        assert any("Plancher" in l for l in lines)


class TestGithubAnnotationsNonRegression:
    def test_chevauchement_texte_texte_inchange(self):
        r = {
            "slide": 3, "text_head": "deux textes",
            "hors_canvas": [], "chevauchements": [{
                "a": "P.foo", "b": "LI.bar", "a_bbox": [1, 2, 3, 4],
                "b_bbox": [5, 6, 7, 8], "overlap": [12, 8],
            }],
            "recouvrements": [], "occupation": None,
        }
        lines = ssc.github_annotations(_report([r]), Path("slides.md"))
        chev = next(l for l in lines if "CHEVAUCHEMENT" in l)
        assert "P.foo × LI.bar overlap=[12, 8]px" in chev

    def test_hors_canvas_contenu_inchange(self):
        r = {
            "slide": 4, "text_head": "debordement",
            "hors_canvas": [{"tag": "IMG", "cls": "absolute", "bbox": [0, 0, 10, 600]}],
            "chevauchements": [], "recouvrements": [], "occupation": None,
        }
        lines = ssc.github_annotations(_report([r]), Path("slides.md"))
        hc = next(l for l in lines if "HORS_CANVAS" in l)
        assert "::warning" in hc and "IMG" in hc


class TestConfirmationElement15695:
    """#15695 : seconde lecture -- une paire qui passe le seuil Range doit
    AUSSI avoir des boites element qui se chevauchent ; les effleurings
    eteints sont comptes (notice), pas taus."""

    def test_paire_rapportee_porte_les_deux_mesures(self):
        """Acceptance : la paire rapportee porte overlap (Range) ET
        element_overlap (boites element) cote a cote."""
        r = {
            "slide": 6, "text_head": "vraie collision",
            "hors_canvas": [], "chevauchements": [{
                "a": "P.x", "b": "P.y", "a_bbox": [1, 2, 3, 4],
                "b_bbox": [2, 3, 5, 6], "overlap": [12, 8],
                "element_overlap": [11.5, 7.25],
            }],
            "chevauchements_eteints": 0,
            "recouvrements": [], "occupation": None,
        }
        lines = ssc.github_annotations(_report([r]), Path("slides.md"))
        chev = next(l for l in lines if "[CHEVAUCHEMENT]" in l)
        assert "overlap=[12, 8]px" in chev
        assert "element_overlap=[11.5, 7.25]px" in chev

    def test_effleurement_eteint_emet_une_notice_comptee(self):
        """Un graze Range eteint par la porte element n'est PAS un silence :
        notice avec compte et reference -- sinon un correctif muet serait
        indiscernable d'un organe mort."""
        r = {
            "slide": 16, "text_head": "graze code padding",
            "hors_canvas": [], "chevauchements": [],
            "chevauchements_eteints": 1,
            "recouvrements": [], "occupation": None,
        }
        lines = ssc.github_annotations(_report([r]), Path("slides.md"))
        fant = next(l for l in lines if "CHEVAUCHEMENT-FANTOME" in l)
        assert "::notice" in fant
        assert "1 effleurement" in fant
        assert "#15695" in fant
        assert not any("[CHEVAUCHEMENT]" in l for l in lines), (
            "eteint = pas de warning CHEVAUCHEMENT"
        )

    def test_slide_propre_sans_eteints_n_emet_rien(self):
        r = {
            "slide": 2, "text_head": "propre",
            "hors_canvas": [], "chevauchements": [],
            "chevauchements_eteints": 0,
            "recouvrements": [], "occupation": None,
        }
        lines = ssc.github_annotations(_report([r]), Path("slides.md"))
        assert not any("CHEVAUCHEMENT" in l for l in lines)


class TestBornesAdvisory:
    def test_borne_documentee_dans_docstring(self):
        """Le signal est ADVISORY : le docstring du module (charge par
        --help et relu par les operateurs) doit le dire, sinon le premier
        rouge de deck croira a un blocage."""
        assert "ADVISORY" in ssc.__doc__
        assert "15351" in ssc.__doc__

    def test_recouvrements_absents_du_comptage_bloquant(self):
        """Instruments du code retour : hors_canvas, chevauchements,
        occupation -- le recouvrement advisory n'y figure pas. Le
        predicate bloquant est occupation_flagged + content_overflow ;
        verifier qu'aucune fonction de flag ne lit `recouvrements`
        (sinon le signal deviendrait bloquant par accident)."""
        import inspect
        for fn in (ssc.occupation_flagged, ssc.content_overflow):
            src = inspect.getsource(fn)
            assert "recouvrement" not in src, (
                f"{fn.__name__} ne doit pas lire le signal advisory"
            )
