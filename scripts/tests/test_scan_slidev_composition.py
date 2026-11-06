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


def _report(results, canvas=(980, 552), font_env=None, font_sig=None):
    rep = {
        "canvas": list(canvas),
        "url": "http://localhost:8767/",
        "baseline_slide": None,
        "baseline_commit": None,
        "n_slides": len(results),
        "results": results,
        "_slide_lines": {str(r["slide"]): 100 + r["slide"] * 10 for r in results},
    }
    if font_env is not None:
        rep["font_environment"] = font_env
        rep["font_signature"] = font_sig or ssc.font_signature(font_env)
    return rep


# Environnement de polices mesuré sur une machine Windows (Slidev ne dépend
# que des polices système — aucune @font-face dans slides/). "Arial" est
# déclarée dans la pile mais NON résolue (largeur identique à la police par
# défaut) : elle ne doit pas apparaître dans la liste des polices résolues.
FONT_ENV = {
    "declared_stack": "'Segoe UI', 'Calibri', Arial, sans-serif",
    "sampled_element": "P",
    "font_size": "18px",
    "line_height": "28px",
    "font_weight": "400",
    "default_width_px": 245.67,
    "probe_ok": True,
    "generic_width_px": {"monospace": 301.2, "serif": 233.4, "sans_serif": 251.9},
    "families": [
        {"name": "Segoe UI", "width_px": 251.9, "resolved": True, "generic": False, "probe_ok": True},
        {"name": "Calibri", "width_px": 244.1, "resolved": True, "generic": False, "probe_ok": True},
        {"name": "Arial", "width_px": 245.67, "resolved": False, "generic": False, "probe_ok": True},
        {"name": "sans-serif", "width_px": 251.9, "resolved": None, "generic": True, "probe_ok": True},
    ],
    "line_height_normal_stack_px": 22.4,
    "line_height_normal_generic_px": 21.6,
    "line_height_delta_px": 0.8,
    "line_height_real_px": 28.0,
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


class TestChevauchementFantomeEteint:
    """Issue #16188 — porte de confirmation élément muette = silent suppression.
    Les paires Range×Range éteintes par boîtes élément disjointes
    (chevauchement-fantôme) doivent être :
      1. visibles dans github_annotations sous le label [CHEVAUCHEMENT-FANTOME]
         en `::notice` non bloquant, avec le compte exact ;
      2. sans générer de warning [CHEVAUCHEMENT] (la porte les a étouffées) ;
      3. absentes en silence quand le slide n'en porte aucune.
    """

    def test_chevauchements_eteints_emet_notice_avec_compte(self):
        r = {
            "slide": 5, "text_head": "graze ~1.2 px",
            "hors_canvas": [], "chevauchements": [],
            # 3 paires Range chevauchent (graze ~1.2 px inline <code>),
            # mais boîtes élément disjointes → éteintes par la porte #15877.
            "chevauchements_eteints": [
                {"a": "LI.foo", "b": "LI.bar", "overlap_range": [1, 2], "element_disjoint": True},
                {"a": "LI.bar", "b": "LI.baz", "overlap_range": [1, 3], "element_disjoint": True},
                {"a": "P.qux",  "b": "P.quux", "overlap_range": [2, 1], "element_disjoint": True},
            ],
            "recouvrements": [], "occupation": None,
        }
        lines = ssc.github_annotations(_report([r]), Path("slides.md"))
        fantome = [l for l in lines if "CHEVAUCHEMENT-FANTOME" in l]
        assert len(fantome) == 1, f"une notice agregee par slide, got {fantome}"
        assert "::notice" in fantome[0], "notice non bloquante (HARD)"
        assert "3 effleurement(s)" in fantome[0], "compte exact des paires eteintes"
        assert "boîtes élément disjointes" in fantome[0]

    def test_chevauchements_eteints_etente_pas_de_warning(self):
        """La porte eteint les paires fantomes : aucun [CHEVAUCHEMENT] warning
        ne doit etre emis quand `chevauchements` est vide."""
        r = {
            "slide": 7, "text_head": "graze",
            "hors_canvas": [], "chevauchements": [],
            "chevauchements_eteints": [
                {"a": "LI.foo", "b": "LI.bar", "overlap_range": [1, 2], "element_disjoint": True},
            ],
            "recouvrements": [], "occupation": None,
        }
        lines = ssc.github_annotations(_report([r]), Path("slides.md"))
        # pas de warning CHEVAUCHEMENT (la porte a eteinte la paire)
        chev_warn = [l for l in lines if "[CHEVAUCHEMENT]" in l and "FANTOME" not in l]
        assert not chev_warn, f"la porte eteint : pas de warning CHEVAUCHEMENT, got {chev_warn}"
        # notice presente
        assert any("CHEVAUCHEMENT-FANTOME" in l for l in lines)

    def test_slide_propre_sans_eteint_n_emet_pas_notice(self):
        """Ni chevauchements ni eteints : aucune notice CHEVAUCHEMENT-FANTOME.
        Seule la notice plancher reste (cf TestGithubAnnotationsRecouvrement)."""
        r = {
            "slide": 2, "text_head": "propre",
            "hors_canvas": [], "chevauchements": [],
            "chevauchements_eteints": [],
            "recouvrements": [], "occupation": None,
        }
        lines = ssc.github_annotations(_report([r]), Path("slides.md"))
        assert not any("CHEVAUCHEMENT-FANTOME" in l for l in lines)
        assert not any("CHEVAUCHEMENT" in l for l in lines)
        # la notice plancher reste
        assert any("Plancher" in l for l in lines)


class TestEnvironnementPolices:
    """#24171 — le rendu Slidev ne depend que des polices SYSTEME : la hauteur
    des blocs de texte, donc le compteur HORS_CANVAS, varie d'une machine a
    l'autre. Le rapport doit porter l'empreinte de son environnement de
    polices, pour que la COMPARABILITE se verifie au lieu de s'opposer deux
    compteurs nus.

    Ces tests epinent les parties PURES (signature, annotation). La mesure
    navigateur reste couverte par le controle positif live.
    """

    def test_signature_stable_pour_le_meme_environnement(self):
        a = ssc.font_signature(FONT_ENV)
        b = ssc.font_signature(dict(FONT_ENV))
        assert a == b, "la signature est une fonction de l'environnement mesure"
        assert a and a != "indisponible"

    def test_signature_change_quand_la_police_resolue_change(self):
        """Le coeur du besoin : deux machines dont la police resolue differe
        doivent produire deux signatures differentes — sinon la comparaison
        de compteurs resterait un non-sens."""
        autre = dict(FONT_ENV)
        autre["families"] = [dict(f) for f in FONT_ENV["families"]]
        autre["families"][0]["resolved"] = False
        assert ssc.font_signature(autre) != ssc.font_signature(FONT_ENV)

    def test_signature_change_quand_la_hauteur_de_ligne_change(self):
        autre = dict(FONT_ENV)
        autre["line_height_normal_stack_px"] = 24.0
        assert ssc.font_signature(autre) != ssc.font_signature(FONT_ENV)

    def test_signature_change_quand_le_canal_monospace_change(self):
        """#24495 reparation : le canal monospace (code/pre) entre dans la
        signature. Deux rendus texte-IDENTIQUES mais dont la police monospace
        RESOLUE differe (le bloc pre change de hauteur) doivent produire deux
        signatures distinctes — c'est precisement l'aveugle que le
        verificateur a rejoue : signature `233aacc...` stable alors que
        `pre` passait de 133 a 126 px (hors canvas -> dedans)."""
        base = dict(FONT_ENV)
        base["monospace"] = {
            "declared_stack": "monospace",
            "sampled_element": "PRE",
            "font_size": "16px",
            "line_height": "normal",
            "families": [
                {"name": "Consolas", "width_px": 210.5, "resolved": True,
                 "generic": False, "probe_ok": True},
            ],
            "line_height_normal_stack_px": 18.9,
            "line_height_real_px": 24.0,
        }
        autre = dict(base)
        # meme canal texte, police monospace resolue + hauteur de ligne
        # intrinque differentes (le bloc pre n'a plus la meme hauteur).
        autre["monospace"] = {
            "declared_stack": "'Courier New', monospace",
            "sampled_element": "PRE",
            "font_size": "16px",
            "line_height": "normal",
            "families": [
                {"name": "Courier New", "width_px": 198.2, "resolved": True,
                 "generic": False, "probe_ok": True},
            ],
            "line_height_normal_stack_px": 17.4,
            "line_height_real_px": 21.0,
        }
        assert ssc.font_signature(base) != ssc.font_signature(autre), (
            "texte identique / monospace different -> signatures distinctes"
        )

    def test_signature_distingue_slide_avec_et_sans_code(self):
        """Une slide SANS bloc code/pre (monospace = None) ne doit pas
        collider avec une slide identique en texte mais portant un bloc
        code/pre : la presence du canal change l'empreinte."""
        sans_code = dict(FONT_ENV)  # pas de cle 'monospace' -> None
        avec_code = dict(FONT_ENV)
        avec_code["monospace"] = {
            "declared_stack": "monospace",
            "sampled_element": "PRE",
            "font_size": "16px",
            "line_height": "normal",
            "families": [
                {"name": "Consolas", "width_px": 210.5, "resolved": True,
                 "generic": False, "probe_ok": True},
            ],
            "line_height_normal_stack_px": 18.9,
            "line_height_real_px": 24.0,
        }
        assert ssc.font_signature(sans_code) != ssc.font_signature(avec_code), (
            "presence du canal code/pre change la signature"
        )

    def test_signature_indisponible_sur_erreur_ou_absence(self):
        assert ssc.font_signature({}) == "indisponible"
        assert ssc.font_signature({"error": "sonde casse"}) == "indisponible"

    def test_annotation_nome_la_signature_et_les_polices_resolues(self):
        r = {
            "slide": 2, "text_head": "propre",
            "hors_canvas": [], "chevauchements": [],
            "chevauchements_eteints": [], "recouvrements": [], "occupation": None,
        }
        lines = ssc.github_annotations(
            _report([r], font_env=FONT_ENV), Path("slides.md"))
        env = next(l for l in lines if "ENVIRONNEMENT-POLICES" in l)
        assert "::notice" in env, "notice non bloquante (HARD)"
        assert ssc.font_signature(FONT_ENV) in env, "la signature est nommee"
        assert "Segoe UI" in env and "Calibri" in env, "polices resolues nommees"
        assert "Arial" not in env, "une police NON resolue ne doit pas etre citee"
        assert "22.4px" in env, "la hauteur de ligne mesuree est nommee"

    def test_sonde_absente_nome_l_absence_de_mesure(self):
        """Une ignorance nommee vaut mieux qu'un silence : sans sonde, la
        notice dit que la comparabilite est inconnue."""
        r = {
            "slide": 2, "text_head": "propre",
            "hors_canvas": [], "chevauchements": [],
            "chevauchements_eteints": [], "recouvrements": [], "occupation": None,
        }
        lines = ssc.github_annotations(_report([r]), Path("slides.md"))
        env = next(l for l in lines if "ENVIRONNEMENT-POLICES" in l)
        assert "non exécutée" in env
        assert "inconnue" in env

    def test_environnement_polices_n_entre_dans_les_compteurs_bloquants(self):
        """Le diagnostic est ADVISORY : aucune fonction de flag ne doit lire
        l'environnement de polices (sinon le signal deviendrait bloquant par
        accident, comme le recouvrement — cf test_recouvrements_absents_du_
        comptage_bloquant)."""
        import inspect
        for fn in (ssc.occupation_flagged, ssc.content_overflow):
            src = inspect.getsource(fn)
            assert "font" not in src, f"{fn.__name__} ne doit pas lire le diagnostic polices"

    def test_docstring_documente_la_dependence_aux_polices(self):
        assert "24171" in ssc.__doc__
        assert "font_signature" in ssc.__doc__


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
