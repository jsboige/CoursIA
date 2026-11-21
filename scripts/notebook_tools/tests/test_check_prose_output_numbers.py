"""Tests for check_prose_output_numbers.py — prose de lecture vs sorties commitees.

Cas fondateur (ICT-38, reserve 1 de la review NanoClaw sur PR #27206) : la prose
cite les valeurs d'un run antérieur non commite (0.0742 / 0.1953) pendant que la
sortie commitee rend d'autres mesures (0.0859 / 0.2109). Chaque exemption est
issue d'un cas MESURE du jeu de reference (ICT-35 + ICT-38 pre/post-fix) :

* precision >= 3 decimales : seules les mesures copiees sont verifiees ; seuils
  (0,5), rapports (« 2,5 fois ») et arrondis de narration (0,33) exemptes ;
* derivee fractionnaire inline « 1/16 = 0.0625 » (ICT-38 post-fix) ;
* backticks : identifiant de code, pas une mesure ;
* annees 1900-2100 ;
* espace ORDINAIRE hors separateur de milliers : « F1 0.217 » (ICT-35, mesure)
  reste deux tokens — la famille insecable seule est neutralisee.

La correspondance est NUMERIQUE (Decimal) : 1,000 == 1.0000, et 0.0859 matche
une sortie 0.0859375 par arrondi ou troncature a la precision de la citation.

La logique sous test est l'``analyze_notebook`` pur — pas de git, pas de kernel.
"""
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from check_prose_output_numbers import (  # noqa: E402
    analyze_notebook,
    citation_matches,
    extract_numbers,
    lecture_cells,
    self_test,
)
from check_prose_output_numbers import NumToken  # noqa: E402


def _nb(md_cells, outputs):
    """Carnet jouet : cellules markdown puis une cellule code aux sorties donnees."""
    return {
        "cells": [
            *[{"cell_type": "markdown", "source": [c]} for c in md_cells],
            {
                "cell_type": "code",
                "source": ["x = 1"],
                "outputs": [
                    {"output_type": "stream", "text": [o]} for o in outputs
                ],
            },
        ]
    }


def _values(nb):
    return [f.value for f in analyze_notebook(nb, "t.ipynb").findings]


# --- Le cas fondateur doit tirer --------------------------------------------


def test_founding_case_ict38_shape_fires():
    """Prose cite 0.0742/0.1953, sortie commitee rend 0.0859/0.2109 : findings."""
    nb = _nb(
        ["## Lecture -- L'intervention causale appariée : 0.0742 contre 0.1953"],
        ["suivi du donneur : 0.0859\nsham : 0.2109"],
    )
    assert sorted(_values(nb)) == ["0.0742", "0.1953"]


def test_postfix_shape_is_silent():
    """Meme cellule re-alignee sur la sortie commitee : zero finding (FP-zero)."""
    nb = _nb(
        ["## Lecture -- L'intervention causale appariée : 0.0859 contre 0.2109"],
        ["suivi du donneur : 0.0859\nsham : 0.2109"],
    )
    assert _values(nb) == []


def test_repeated_citations_each_reported():
    """Une valeur citee sur plusieurs lignes : un finding par ligne."""
    nb = _nb(
        ["## Lecture", "premiere ligne citant 0.0742", "deuxieme ligne citant 0.0742"],
        ["x : 0.0859"],
    )
    assert _values(nb) == ["0.0742", "0.0742"]


# --- Correspondance numerique ------------------------------------------------


def test_french_comma_matches_dot_output():
    nb = _nb(["### Lecture du résultat : reste 0,2109"], ["sham : 0.2109"])
    assert _values(nb) == []


def test_numeric_equality_ignores_trailing_zeros():
    """« 1,000 » (3 dec.) correspond a une sortie « 1.0000 » (4 dec.)."""
    nb = _nb(["## Bilan : exactitude 1,000"], ["accuracy: 1.0000"])
    assert _values(nb) == []


def test_rounding_and_truncation_match_longer_output():
    """« 0.0859 » correspond a une sortie plus precise 0.0859375 (round ou trunc)."""
    assert citation_matches(
        NumToken(_d("0.0859"), 4, "0.0859"),
        extract_numbers("follow_donor : 0.0859375"),
    )
    # Troncature : 0.0546 est le trunc de 0.0546875, pas son arrondi (0.0547).
    assert citation_matches(
        NumToken(_d("0.0546"), 4, "0.0546"),
        extract_numbers("random_target : 0.0546875"),
    )


def test_precision_roughness_tolerated_but_different_value_rejected():
    """Correspondance a la precision de la citation, pas sous-chaine aveugle.

    « 0.085 » (troncation prefixe de la sortie 0.0859) MATCHE : la roughness de
    precision n'est pas le defaut chasse (ICT-38 : 0.0742 vs 0.0859, 2e chiffre
    significatif different), la signaler serait un FP. En revanche une VALEUR
    differente ne matche sous aucune precision.
    """
    assert citation_matches(
        NumToken(_d("0.085"), 3, "0.085"),
        extract_numbers("x : 0.0859"),
    )
    assert not citation_matches(
        NumToken(_d("0.0740"), 4, "0.0740"),
        extract_numbers("x : 0.0859"),
    )
    assert not citation_matches(
        NumToken(_d("0.2108"), 4, "0.2108"),
        extract_numbers("x : 0.2109"),
    )


def _d(raw):
    from decimal import Decimal

    return Decimal(raw.replace(",", "."))


# --- Porte de precision et exemptions ----------------------------------------


def test_low_precision_numbers_exempt():
    """Seuils, rapports et arrondis de narration : hors champ (< 3 decimales)."""
    nb = _nb(
        ["## Bilan : effet >= 0,5, ecart >= 0,25, soit 2,5 fois ; "
         "l'ancien banc donnait 0,33"],
        ["x : 0.2109"],
    )
    result = analyze_notebook(nb, "t.ipynb")
    assert result.findings == []
    assert result.citations_checked == 0


def test_fraction_derivation_exempt():
    """« (1/16 = 0.0625) » : la prose porte la preuve du calcul (ICT-38 post-fix)."""
    nb = _nb(
        ["## Lecture : colle à 0.0547, au hasard par valeur (1/16 = 0.0625)"],
        ["random_target : 0.0547"],
    )
    assert "0.0625" not in _values(nb)


def test_quoted_literature_value_exempt():
    """« la prédiction 4,267 ... est citée » : valeur de littérature déclarée,
    pas une mesure du carnet (Complexity-02b/02c, seuil 3-SAT, census initial)."""
    nb = _nb(
        ["## Bilan : la prédiction 4,267 pour le seuil 3-SAT est citée, "
         "non démontrée par ces mesures"],
        ["seuil_mesure : 4.30"],
    )
    assert _values(nb) == []


def test_quoted_keyword_does_not_exempt_whole_line():
    """Sonde Hermes #27233 (faux négatif 1) : un mot-clé bibliographique
    n'exempte QUE le nombre qu'il gouverne, pas la ligne entière.

    « l'article rapporte 0.0742, notre run rend 0.0859 et 0.0742 reste notre
    lecture » : 0.0742 (gouverné par « l'article rapporte ») est exempt, 0.0859
    matche la sortie committée, mais la REPRISE de 0.0742 comme « notre
    lecture » doit être vérifiée — l'ancien ``search(line)`` rendait
    citations_checked=0 et le défaut fondateur invisible.
    """
    nb = _nb(
        ["## Lecture : l'article rapporte 0.0742, notre run rend 0.0859 "
         "et 0.0742 reste notre lecture"],
        ["suivi du donneur : 0.0859"],
    )
    result = analyze_notebook(nb, "t.ipynb")
    assert _values(nb) == ["0.0742"]
    assert result.citations_checked == 2


def test_nbsp_thousands_do_not_shift_link_exemption():
    """Sonde Hermes #27233 (faux négatif 2) : spans d'exemption et positions
    des nombres sur la MÊME chaîne normalisée.

    « total 1[NBSP]000 et 2[NBSP]500 unités, [ref](…) 0.0742 tire » : la
    normalisation retire 2 caractères côté nombres, l'ancien calcul des spans
    sur le texte brut faisait glisser 0.0742 dans le span du lien (exempté à
    tort, citations_checked=0).
    """
    nbsp = " "
    nb = _nb(
        ["## Bilan : total 1" + nbsp + "000 et 2" + nbsp + "500 unités, "
         "[ref](https://arxiv.org/abs/2202.05822) 0.0742 tire"],
        ["suivi : 0.0859"],
    )
    assert _values(nb) == ["0.0742"]


def test_citation_more_precise_than_print_is_refused():
    """« 1.99923 » vs print « 1.9992 » (Complexity-03e) : REFUSE, a dessein.

    La correspondance par extension de prefixe masque le defaut fondateur --
    mesure en re-calibrant ICT-38 pre-fix : la citation perimee 0.1953 matchait
    par prefixe une sortie 0.195 d'une AUTRE quantite, et les 8 findings du cas
    fondateur tombaient a 0. Le residu 1.99923 reste un bruit du sweep
    report-only, jamais un masquage du gate PR.
    """
    assert not citation_matches(
        NumToken(_d("1.99923"), 5, "1.99923"),
        extract_numbers("ratio : 1.9992"),
    )
    # La regle de prefixe refusee est bien celle qui masquait le fondateur.
    assert not citation_matches(
        NumToken(_d("0.1953"), 4, "0.1953"),
        extract_numbers("autre_quantite : 0.195"),
    )
    assert not citation_matches(
        NumToken(_d("0.0742"), 4, "0.0742"),
        extract_numbers("x : 0.0859"),
    )


def test_backtick_numbers_exempt():
    nb = _nb(["## Conclusion : le seuil `0.7500` interne"], ["x : 0.2109"])
    assert _values(nb) == []


def test_markdown_link_and_url_numbers_exempt():
    """arXiv 2202.05822 et DOI dans un lien bibliographique : identifiants,
    pas des mesures (CLIPasso 05-2, census initial)."""
    nb = _nb(
        ["> arXiv [2202.05822](https://arxiv.org/abs/2202.05822) — ACM TOG 41(4), "
         "DOI [10.1145/3528223.3530068](https://doi.org/10.1145/3528223.3530068)"],
        ["x : 0.2109"],
    )
    assert _values(nb) == []


def test_years_exempt():
    nb = _nb(["## Bilan : mesuré depuis 2019, exactitude 0.9999"], ["acc: 0.9999"])
    assert _values(nb) == []


def test_ordinary_space_is_not_a_thousands_separator():
    """« F1 0.217 » (ICT-35, mesure) : deux tokens, pas 10.217."""
    tokens = extract_numbers("F1 0.217")
    assert [t.value for t in tokens] == [_d("1"), _d("0.217")]
    nb = _nb(["## Lecture 3 -- F1 0.217 : sous le ratio de classe"],
             ["f1_score : 0.2170"])
    assert _values(nb) == []


def test_nbsp_family_is_a_thousands_separator():
    tokens = extract_numbers("1 234,567")
    assert _d("1234.567") in [t.value for t in tokens]


# --- Perimetre -----------------------------------------------------------------


def test_code_cell_comments_out_of_scope():
    """Les commentaires de cellules code ne sont pas de la prose de lecture."""
    nb = _nb(
        ["## Lecture : valeur 0.2109 confirmée"],
        ["# ancienne valeur 0.0742\nx : 0.2109"],
    )
    assert _values(nb) == []


def test_non_lecture_markdown_out_of_scope():
    """Un bloc markdown d'enonce (pas de marqueur de lecture) n'est pas verifie."""
    nb = _nb(
        ["## Mise en place du banc", "l'ancienne version mesurait 0.0742"],
        ["x : 0.0859"],
    )
    assert _values(nb) == []


def test_headingless_continuation_in_scope():
    nb = _nb(["## Lecture", "prose de continuation citant 0.0742"], ["x : 0.0859"])
    assert _values(nb) == ["0.0742"]


def test_new_section_heading_closes_block():
    """Une cellule avec entete hors lecture ferme le bloc de continuation."""
    nb = _nb(
        ["## Lecture", "### Ce que ça veut dire, avec 0.0742", "## Exercices"],
        ["x : 0.0859"],
    )
    # « ### Ce que ... » matche le marqueur : in scope. « ## Exercices » non.
    assert _values(nb) == ["0.0742"]


def test_lecture_cells_indices():
    nb = {
        "cells": [
            {"cell_type": "markdown", "source": ["## Enoncé"]},
            {"cell_type": "markdown", "source": ["## Lecture du résultat"]},
            {"cell_type": "markdown", "source": ["continuation"]},
            {"cell_type": "markdown", "source": ["## Exercices"]},
            {"cell_type": "code", "source": ["x"], "outputs": []},
        ]
    }
    assert lecture_cells(nb) == {1, 2}


def test_outputs_from_execute_result_text_plain():
    """Les execute_result (data.text/plain) comptent, pas seulement stream."""
    nb = {
        "cells": [
            {"cell_type": "markdown", "source": ["## Lecture : perte 0.3210"]},
            {
                "cell_type": "code",
                "source": ["loss"],
                "outputs": [
                    {
                        "output_type": "execute_result",
                        "data": {"text/plain": ["tensor(0.3210)"]},
                    }
                ],
            },
        ]
    }
    assert _values(nb) == []


def test_outputs_from_display_markdown_count_as_anchor():
    """display(Markdown(...)) : la mesure vit dans text/markdown, le text/plain
    est l'objet-repr sans nombre (App-18, Search -- 25 citations du stock)."""
    nb = {
        "cells": [
            {"cell_type": "markdown", "source": ["### Lecture — le pic\n\nGA atteint **0.758**."]},
            {
                "cell_type": "code",
                "source": ["display(Markdown(f'best = **{best:.3f}**'))"],
                "outputs": [
                    {
                        "output_type": "display_data",
                        "data": {
                            "text/markdown": ["best = **0.758**"],
                            "text/plain": ["<IPython.core.display.Markdown object>"],
                        },
                    }
                ],
            },
        ]
    }
    assert _values(nb) == []


def test_display_markdown_different_value_still_fires():
    """L'ancrage text/markdown ne blanchit pas une valeur differente de la prose."""
    nb = {
        "cells": [
            {"cell_type": "markdown", "source": ["### Lecture — le pic\n\nGA atteint **0.791**."]},
            {
                "cell_type": "code",
                "source": ["display(Markdown(...))"],
                "outputs": [
                    {
                        "output_type": "display_data",
                        "data": {
                            "text/markdown": ["best = **0.758**"],
                            "text/plain": ["<IPython.core.display.Markdown object>"],
                        },
                    }
                ],
            },
        ]
    }
    assert _values(nb) == ["0.791"]


# --- Self-test embarque (pre-controle pre_argv) ----------------------------------


def test_embedded_self_test_passes():
    assert self_test() == 0
