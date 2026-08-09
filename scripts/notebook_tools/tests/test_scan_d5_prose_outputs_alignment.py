"""Tests du detecteur v3 coherence prose <-> outputs intra-revision.

Issue #9790 : scope borne, contre-epreuve positive obligatoire sur
ICT-1-PhiTrajectories pre-`7de14792c` (le commit fix #9416 a corrige la
dérive, mais le notebook parent `e8dc56ac9` doit etre signale par le
detecteur -- c'est la definition du succes de la v3).

10 classes de tests, ~30 tests attendus.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

import pytest

_HERE = os.path.dirname(os.path.abspath(__file__))
_ROOT = os.path.dirname(_HERE)
if _ROOT not in sys.path:
    sys.path.insert(0, _ROOT)

import scan_d5_prose_outputs_alignment as mod


# --------------------------------------------------------------------------- #
#  Helpers
# --------------------------------------------------------------------------- #


def _make_notebook(cells: list[dict], path: Path) -> None:
    """Atomically write a notebook JSON file."""
    payload = {
        "cells": cells,
        "metadata": {},
        "nbformat": 4,
        "nbformat_minor": 5,
    }
    path.write_text(json.dumps(payload, ensure_ascii=False, indent=1),
                    encoding="utf-8")


def _markdown_cell(source: str) -> dict:
    return {"cell_type": "markdown", "metadata": {}, "source": [source]}


def _code_cell(source: str, outputs: list[dict]) -> dict:
    return {
        "cell_type": "code",
        "metadata": {},
        "source": [source],
        "outputs": outputs,
        "execution_count": 1,
    }


# --------------------------------------------------------------------------- #
#  Parsing FR / EN
# --------------------------------------------------------------------------- #


class TestParseFrNumber:
    def test_simple_integer(self):
        assert mod._parse_fr_number("42") == 42.0

    def test_simple_decimal_en(self):
        assert mod._parse_fr_number("0.69") == 0.69

    def test_simple_decimal_fr(self):
        assert mod._parse_fr_number("0,69") == 0.69

    def test_thousands_separator_fr(self):
        assert mod._parse_fr_number("1 234") == 1234.0
        assert mod._parse_fr_number("1 234,56") == 1234.56

    def test_thousands_separator_en(self):
        assert mod._parse_fr_number("1,234.56") == 1234.56

    def test_scientific(self):
        assert mod._parse_fr_number("1e-3") == 1e-3
        assert mod._parse_fr_number("1,5e-3") == 1.5e-3

    def test_negative(self):
        assert mod._parse_fr_number("-3.14") == -3.14

    def test_out_of_range_filtered(self):
        # MAX_NUMBER_VALUE = 1e15 ; 1e16 doit etre filtre, 1e14 doit passer.
        assert mod._parse_fr_number("0") is None              # < 1e-9
        assert mod._parse_fr_number("1e14") is not None
        assert mod._parse_fr_number("1e16") is None           # > 1e15

    def test_unparseable(self):
        assert mod._parse_fr_number("") is None
        assert mod._parse_fr_number("abc") is None


# --------------------------------------------------------------------------- #
#  Extraction prose
# --------------------------------------------------------------------------- #


class TestExtractProseNumbers:
    def test_basic_en(self):
        nums = mod._extract_prose_numbers("The value is 0.69 here.")
        assert 0.69 in nums

    def test_basic_fr(self):
        nums = mod._extract_prose_numbers("La valeur est 0,69 ici.")
        assert 0.69 in nums

    def test_filter_years(self):
        nums = mod._extract_prose_numbers("En 2026, on a vu 0.5.")
        assert 2026 not in nums
        assert 0.5 in nums

    def test_filter_issue_numbers(self):
        nums = mod._extract_prose_numbers("Voir #9416 pour le detail, ratio 0.82.")
        assert 9416 not in nums
        assert 0.82 in nums

    def test_filter_section_headers(self):
        nums = mod._extract_prose_numbers("## 4.2 Resultats\nLe ratio est 0.7.")
        # 4.2 sur une ligne de titre ATX = filtre (titre structural) ;
        # 0.7 dans la prose du corps = garde.
        assert 0.7 in nums
        assert 4.2 not in nums

    def test_filter_h1_title_notebook_id(self):
        # Gap documente dans le corpus run #9790 : les titres H1 (`# SC-8`,
        # `# MGS-9`, `# SocialChoice 03`) fuyaient car les hints couvraient
        # H2+ mais pas H1. Le numero d'ID du notebook est structural.
        nums = mod._extract_prose_numbers("# SC-8-DeFi-Primitives\n\nLe solde est 0.69.")
        assert 8 not in nums
        assert 0.69 in nums

    def test_filter_h1_title_count(self):
        nums = mod._extract_prose_numbers("# SocialChoice 03 - Methodes\nLe ratio 0.7.")
        assert 3 not in nums
        assert 0.7 in nums

    def test_h1_heading_does_not_filter_following_body(self):
        # Un nombre sur la ligne SUIVANT un titre H1 (corps de paragraphe)
        # doit etre preserve -- le filtre cible la ligne de titre, pas le
        # paragraphe d'apres.
        nums = mod._extract_prose_numbers("# Titre du notebook\n\nSharpe = 0.512.")
        assert 0.512 in nums

    def test_filter_versions(self):
        nums = mod._extract_prose_numbers("Version v3 de l'algo, score 0.95.")
        assert 0.95 in nums

    def test_filter_cell_indices(self):
        nums = mod._extract_prose_numbers("Voir cell[7] pour output, resultat 0.69.")
        assert 0.69 in nums

    def test_multiple_numbers(self):
        nums = mod._extract_prose_numbers("Trois niveaux : 0.19, 0.69, 2.31.")
        assert 0.19 in nums
        assert 0.69 in nums
        assert 2.31 in nums

    def test_filter_inline_latex_math(self):
        # A number inside an inline LaTeX formula ($2^n - 1$, $v(S) \in \{0, 1\}$)
        # is a mathematical constant/base, not a measurement from outputs.
        # Documented FP class (c.1293): Planners-6 "$2^n - 1$" -> prose_number 2.0.
        nums = mod._extract_prose_numbers("La formule $2^n - 1$ donne la longueur, resultat observe 0.69.")
        assert 0.69 in nums
        assert 2.0 not in nums
        assert 1.0 not in nums

    def test_filter_inline_latex_set_notation(self):
        # $v(S) \in \{0, 1\}$ -- the 0 and 1 are set elements, not outputs.
        nums = mod._extract_prose_numbers("Jeux de vote : $v(S) \\in \\{0, 1\\}$, ratio mesure 0.42.")
        assert 0.42 in nums
        assert 0.0 not in nums
        assert 1.0 not in nums

    def test_filter_display_math_block(self):
        # Display math $$...$$ spanning content -- bases inside are filtered.
        nums = mod._extract_prose_numbers("L'espace d'etats $$3^n$$ croit vite, valeur 0.77 obtenue.")
        assert 0.77 in nums
        assert 3.0 not in nums

    def test_legit_decimal_outside_math_preserved(self):
        # A real measurement after a math span is still captured.
        nums = mod._extract_prose_numbers("Modele $f(x)$, score final 0.88, precedent 0.71.")
        assert 0.88 in nums
        assert 0.71 in nums


class TestOrderedListMarkerFalsePositive:
    """Filtre marqueur de liste ordonnee (po-2023 #9790, FP class 7).

    Un entier qui est le MARQUEUR d'un item de liste (ligne debutant par
    ``N.`` / ``N)`` + espace) est un indice d'enumeration, jamais une mesure
    d'output. Falsifiable both-directions : une mesure decimale (``1.15``) ou
    un entier en milieu de phrase (``5 widgets``) ne rend jamais sous la forme
    d'un marqueur (premier token de la ligne + ``.``/``)`` + espace). Verifie
    firsthand (G.1, 2026-08-09) : 770/10411 findings (7.4 %) sont des marqueurs
    purs sur le corpus full.
    """

    def test_filter_dot_marker(self):
        # "5. **Exercices**" -- le 5 est un indice de liste, pas une mesure.
        nums = mod._extract_prose_numbers("5. Analyser le jeu de la Chasse au Cerf.")
        assert 5.0 not in nums

    def test_filter_paren_marker(self):
        # "1) First item" -- marqueur parenthese.
        nums = mod._extract_prose_numbers("1) Premier element de la liste.")
        assert 1.0 not in nums

    def test_filter_indented_marker(self):
        # Nested list item (indentation <= 3 espaces, CommonMark).
        nums = mod._extract_prose_numbers("  2. sous-element imbrique")
        assert 2.0 not in nums

    def test_filter_marker_followed_by_bold(self):
        # Cas corpus (GameTheory-13, GenAI) : "3. **Monitoring** : ..."
        nums = mod._extract_prose_numbers("3. **Convergence** -- la strategie moyenne converge vers Nash")
        assert 3.0 not in nums

    def test_filter_marker_at_eol(self):
        # Marqueur seul en fin de ligne ("5.\n6. ...").
        nums = mod._extract_prose_numbers("5.\n6. suite")
        assert 5.0 not in nums
        assert 6.0 not in nums

    def test_preserve_decimal_measurement(self):
        # CRUCIAL both-directions : "1.15" est une mesure decimale, le point
        # est un SEPARATEUR DECIMAL interne au token, pas un marqueur.
        nums = mod._extract_prose_numbers("Le ratio de Sharpe est 1.15 sur la periode OOS.")
        assert 1.15 in nums

    def test_preserve_integer_mid_line(self):
        # CRUCIAL both-directions : un entier en milieu de phrase n'est pas un
        # marqueur (du texte le precede sur la ligne).
        nums = mod._extract_prose_numbers("On obtient 5 widgets apres optimisation.")
        assert 5.0 in nums

    def test_preserve_sentence_internal_period(self):
        # CRUCIAL both-directions : "Le seuil est 5. Continuons." -- le 5 est
        # en MILIEU de ligne (pas le premier token), donc le "5." n'est PAS un
        # marqueur de liste. C'est une mesure suivie d'une fin de phrase.
        nums = mod._extract_prose_numbers("Le seuil est 5. Continuons l'analyse.")
        assert 5.0 in nums

    def test_preserve_marker_and_measurement_same_cell(self):
        # Une cellule peut avoir un marqueur "5." ET une mesure "5" ailleurs :
        # seul le marqueur est filtre, la mesure survive.
        nums = mod._extract_prose_numbers(
            "5. Cinquieme etape du protocole\n\nLa dimension de l'espace est 5."
        )
        # La mesure 5 (deuxieme ligne, milieu de phrase) est conservee.
        assert 5.0 in nums


class TestHexColorAndExponentFalsePositives:
    """Filtre codes couleur hex + exposants plaine (EPIC #9768, c.1295).

    Deux classes residuelles de FP decouvertes firsthand en scannant 4 familles
    (Probas/IIT/Search/SemanticWeb). Distinctes de la math LaTeX (c.1293) :
    elles apparaissent hors de tout span $...$.
    """

    def test_filter_hex_color_mermaid_classdef(self):
        # SW-6-CSharp-RDFS cell[6]: mermaid `classDef root fill:#cfe2ff,stroke:#084298`
        # -> the #084298 channel was extracted as the number 84298. Systematic in
        # any mermaid-styled notebook.
        nums = mod._extract_prose_numbers(
            "classDef root fill:#cfe2ff,stroke:#084298,color:#052c65. Resultat observe 0.69."
        )
        assert 0.69 in nums
        assert 84298.0 not in nums
        assert 5132.0 not in nums  # #0f5132 style also filtered when present

    def test_filter_hex_color_six_digits(self):
        # A standalone hex color #ff0000 in prose must not leak red/green/blue channels.
        nums = mod._extract_prose_numbers("Couleur #ff0000, score mesure 0.42.")
        assert 0.42 in nums
        assert 255.0 not in nums  # would-be leak from #ff
        assert 0.0 not in nums

    def test_filter_hex_color_not_overfilter_legit_hash_ref(self):
        # A short `#5` or `#12` (< 3 hex) is NOT a color code -- it stays subject
        # to the other reference filters, not the hex one. And a real measurement
        # after a `#ref` is preserved.
        nums = mod._extract_prose_numbers("Voir #12, valeur reelle 84298 atteinte.")
        assert 84298.0 in nums  # legit big number preserved (no `#` prefix)

    def test_filter_plaintext_exponent(self):
        # Infer-7-Skills-IRT cell[64]: "2^3 combinaisons" -> base 2 and exp 3
        # are constituents of a math expression, not separate measurements.
        nums = mod._extract_prose_numbers("Soit 2^3 combinaisons, resultat observe 0.77.")
        assert 0.77 in nums
        assert 2.0 not in nums
        assert 3.0 not in nums

    def test_filter_plaintext_exponent_letter_base(self):
        # n^2 / n^k -- the exponent digit is a math constituent.
        nums = mod._extract_prose_numbers("Complexite n^2, avec ratio mesure 0.31.")
        assert 0.31 in nums
        assert 2.0 not in nums

    def test_legit_measure_near_exponent_notation_preserved(self):
        # A real measurement adjacent to an exponent is still captured.
        nums = mod._extract_prose_numbers("Facteur 10^5, et on mesure 84298 cas au total.")
        assert 84298.0 in nums
        assert 5.0 not in nums  # exp of 10^5 filtered
        assert 10.0 not in nums  # base filtered


class TestReferenceIdentifiers:
    """Filtre DOI / arXiv (EPIC #9768 Phase 0, c.1291).

    Les identifiants de reference (DOI 10.XXXX/..., arXiv YYMM.NNNNN) sont la
    classe dominante de FP firsthand sur Probas/Infer.NET (~40 findings/notebook)
    et les labs ML.NET. Ils doivent etre filtres ; un vrai resultat doit passer.
    """

    def test_doi_registrant_prefix_filtered(self):
        # 10.1145 / 10.1109 : prefix registrant DOI, jamais une mesure.
        nums = mod._extract_prose_numbers("Voir DOI 10.1145 pour le detail.")
        assert 10.1145 not in nums
        nums = mod._extract_prose_numbers("Reference IEEE 10.1109 du papier.")
        assert 10.1109 not in nums

    def test_doi_url_suffix_filtered(self):
        # Le suffixe 564376.564421 suit immediatement le registrant (URL DOI).
        nums = mod._extract_prose_numbers("Paper : 10.1145/564376.564421 (ACM).")
        assert 564376.564421 not in nums
        assert 10.1145 not in nums

    def test_arxiv_id_filtered(self):
        # arXiv:2402.0103 -- annee plausible 24.
        nums = mod._extract_prose_numbers("Decrit dans arXiv:2402.0103.")
        assert 2402.0103 not in nums

    def test_arxiv_bare_year_plausible_filtered(self):
        # Bare YYMM.NNNNN avec annee plausible (23) meme sans prefixe « arXiv ».
        nums = mod._extract_prose_numbers("Methode de 2309.07864 appliquee ici.")
        assert 2309.07864 not in nums

    def test_legit_decimal_preserved(self):
        # Un rating 1923.7 (1 decimale) n'est PAS un arXiv ID -> preserve.
        nums = mod._extract_prose_numbers("Elo estime : 1923.7 points.")
        assert 1923.7 in nums

    def test_legit_4digit_decimal_outside_arxiv_range_preserved(self):
        # 1234.56789 : annee 12 hors plage arXiv (19-30) -> preserve.
        nums = mod._extract_prose_numbers("Mesure precise : 1234.56789 unite.")
        assert 1234.56789 in nums

    def test_legit_number_after_doi_with_space_preserved(self):
        # Un vrai resultat apres un DOI, separe par une espace, n'est pas un
        # suffixe d'URL -> preserve (anti-regression du filtre suffixe).
        nums = mod._extract_prose_numbers("DOI 10.1145/564376.564421 ; ratio 0.82.")
        assert 0.82 in nums
        assert 564376.564421 not in nums

    def test_real_marginal_preserved(self):
        # 0.647 (la marginale exacte P(W=T) d'Infer-4) doit rester extraite.
        nums = mod._extract_prose_numbers("La proba exacte est P(W=T) = 0.647.")
        assert 0.647 in nums


# --------------------------------------------------------------------------- #
#  Extraction outputs
# --------------------------------------------------------------------------- #


class TestExtractOutputNumbers:
    def test_text_plain_string(self):
        nums = mod._extract_output_numbers({"text": "0.6875\n"})
        assert 0.6875 in nums

    def test_text_plain_list(self):
        nums = mod._extract_output_numbers({"data": {"text/plain": ["0.1875", "0.6875"]}})
        assert 0.1875 in nums
        assert 0.6875 in nums

    def test_data_with_text_plain(self):
        nums = mod._extract_output_numbers({"data": {"text/plain": "result=0.95"}})
        assert 0.95 in nums

    def test_non_dict(self):
        assert mod._extract_output_numbers("not a dict") == []

    def test_empty(self):
        assert mod._extract_output_numbers({}) == []


# --------------------------------------------------------------------------- #
#  Detection d'enumeration prose (MISSING_FROM_PROSE_ENUMERATION)
# --------------------------------------------------------------------------- #


class TestDetectProseEnumeration:
    """Detecteur de la categorie MISSING_FROM_PROSE_ENUMERATION (#9416)."""

    def test_two_levels_fr_keyword(self):
        # Pattern fort « N niveaux : a, b »
        nums = mod._detect_prose_enumeration("On observe 2 niveaux : 0,19 et 2,31.")
        assert nums is not None
        assert 0.19 in nums
        assert 2.31 in nums

    def test_three_levels_fr_keyword(self):
        nums = mod._detect_prose_enumeration("les 3 valeurs sont 0.19, 0.69 et 2.31.")
        assert nums is not None
        assert len(nums) == 3

    def test_four_levels_colon(self):
        nums = mod._detect_prose_enumeration("Le systeme a 4 phases : 0.1, 0.3, 0.5, 0.7.")
        assert nums is not None
        assert len(nums) == 4

    def test_natural_phrase_two_groups(self):
        # Cas fondateur ICT-1 : « un pic a X, le reste a Y »
        # Ne contient PAS de mot-cle fort mais la formulation naturelle
        # « un <mot> a X, ... le reste a Y » est une enumeration de 2.
        nums = mod._detect_prose_enumeration("un pic a 2,31, le reste a 0,19")
        assert nums is not None
        assert 2.31 in nums
        assert 0.19 in nums

    def test_not_enumeration_no_match(self):
        # Pas de mot-cle, pas d'enumeration -> None
        assert mod._detect_prose_enumeration("La temperature est 0.69.") is None
        assert mod._detect_prose_enumeration("Plusieurs pics apparaissent.") is None
        assert mod._detect_prose_enumeration("") is None

    def test_domain_range_not_enumeration(self):
        # A domain/range description (« 81 valeurs (1-9) ») is NOT an output-
        # level enumeration: the hyphenated pair denotes value-space bounds,
        # not distinct observed levels. Confirmed FP firsthand Sudoku-5-PSO
        # cell[9] (« Chaque particule contient 81 valeurs (1-9) » was read as
        # a 2-level enumeration of {1, 9} then compared to global outputs).
        # ASCII hyphen, en-dash and em-dash variants must all be excluded.
        assert mod._detect_prose_enumeration(
            "Chaque particule contient 81 valeurs (1-9) pour chaque cellule.") is None
        assert mod._detect_prose_enumeration(
            "Chaque particule contient 81 valeurs (1–9) pour chaque cellule.") is None
        assert mod._detect_prose_enumeration(
            "Chaque bloc contient 81 valeurs 1—9 initialisees.") is None

    def test_latex_decimal_span_preserved(self):
        # $2{,}31$ is a LaTeX decimal == 2.31 -- a real value, must be kept.
        nums = mod._detect_prose_enumeration("2 niveaux : $0{,}19$ et $2{,}31$.")
        assert nums is not None
        assert 0.19 in nums
        assert 2.31 in nums

    def test_latex_formula_span_filtered(self):
        # $2^n - 1$ is a formula, not a measurement -- its base "2" must NOT
        # be extracted as an enumerated level. FP documented c.1293 (Planners-6).
        nums = mod._detect_prose_enumeration(
            "La formule $2^n - 1$ donne la longueur, observe 2 niveaux : 0,19 et 2,31.")
        assert nums is not None
        assert 2.0 not in nums
        assert 1.0 not in nums
        assert 0.19 in nums
        assert 2.31 in nums

    def test_latex_set_notation_filtered(self):
        # $v(S) \in \{0, 1\}$ -- the 0/1 are set elements, not enumerated levels.
        # Uses a recognized enumeration keyword ("niveaux") so the parser engages.
        nums = mod._detect_prose_enumeration(
            "Jeux de vote : $v(S) \\in \\{0, 1\\}$, 2 niveaux : 0,42 et 0,88.")
        assert nums is not None
        assert 0.0 not in nums
        assert 1.0 not in nums
        assert 0.42 in nums


class TestDistinctLevels:
    """Comptage de niveaux distincts a tolerance pres."""

    def test_three_well_separated(self):
        # 3 valeurs bien espacees (cas ICT-1 outputs)
        assert mod._distinct_levels([0.1875, 0.6875, 2.3125]) == 3

    def test_two_close_one_far(self):
        # 2 valeurs proches (0.18, 0.20) + 1 lointaine (2.5)
        # 0.18 et 0.20 sont à 10% > 5% (donc 2 niveaux entre eux),
        # 2.5 est isolé. Total : 3 niveaux.
        assert mod._distinct_levels([0.18, 0.20, 2.5]) == 3

    def test_single_value(self):
        assert mod._distinct_levels([0.5]) == 1

    def test_empty(self):
        assert mod._distinct_levels([]) == 0

    def test_two_identical(self):
        assert mod._distinct_levels([0.5, 0.5]) == 1

    def test_two_within_tolerance(self):
        # 2 valeurs à 4% l'une de l'autre : DANS la tolérance -> 1 seul niveau.
        # base = max(|0.5|, |0.48|) = 0.5 ; diff = 0.02 ; ratio = 4% < 5%
        assert mod._distinct_levels([0.5, 0.48]) == 1

    def test_two_outside_tolerance(self):
        # 2 valeurs à 10% l'une de l'autre : HORS tolérance -> 2 niveaux.
        # base = max(|0.5|, |0.45|) = 0.5 ; diff = 0.05 ; ratio = 10% > 5%
        assert mod._distinct_levels([0.5, 0.45]) == 2


class TestMissingFromProseEnumeration:
    """Integration : MISSING_FROM_PROSE_ENUMERATION attrape le cas ICT-1."""

    def test_ict1_founder_signaled(self, tmp_path):
        """Cas fondateur #9416 : prose dit « 2,31 + 0,19 » (2 niveaux)
        mais outputs exhibent 3 niveaux dont 0.6875 omis."""
        nb = tmp_path / "ict1_founder.ipynb"
        _make_notebook([
            _markdown_cell("un pic a 2,31, le reste a 0,19"),
            _code_cell("print(0.1875); print(0.6875); print(2.3125)",
                       [{"text": "0.1875\n0.6875\n2.3125\n"}]),
        ], nb)
        result = mod.analyze_notebook(nb)
        assert result.total_findings >= 1
        enum_findings = [f for f in result.findings
                         if f.category == "MISSING_FROM_PROSE_ENUMERATION"]
        assert len(enum_findings) == 1, (
            f"Cas fondateur ICT-1 doit produire exactement 1 finding "
            f"MISSING_FROM_PROSE_ENUMERATION, trouve {len(enum_findings)}"
        )
        f = enum_findings[0]
        assert f.prose_number == pytest.approx(2)
        assert "3 niveaux distincts" in f.details
        assert "2 niveaux" in f.details

    def test_no_signal_when_outputs_match_prose(self, tmp_path):
        """Si la prose enumere N niveaux ET outputs en exhibent N, RAS."""
        nb = tmp_path / "clean_enum.ipynb"
        _make_notebook([
            _markdown_cell("les 3 valeurs sont 0.19, 0.69 et 2.31."),
            _code_cell("print(0.19); print(0.69); print(2.31)",
                       [{"text": "0.19\n0.69\n2.31\n"}]),
        ], nb)
        result = mod.analyze_notebook(nb)
        enum_findings = [f for f in result.findings
                         if f.category == "MISSING_FROM_PROSE_ENUMERATION"]
        assert enum_findings == [], (
            f"3 niveaux prose + 3 niveaux outputs ne doit pas signaler "
            f"MISSING_FROM_PROSE_ENUMERATION, trouve {len(enum_findings)}"
        )


# --------------------------------------------------------------------------- #
#  Tolerances
# --------------------------------------------------------------------------- #


class TestIsClose:
    def test_exact(self):
        assert mod._is_close(0.69, 0.69)

    def test_within_relative(self):
        assert mod._is_close(0.69, 0.70)  # ~1.4%

    def test_outside_relative(self):
        assert not mod._is_close(0.69, 0.90)  # ~30%

    def test_within_absolute(self):
        assert mod._is_close(1e-9, 1e-9 + 1e-12)

    def test_zero(self):
        assert mod._is_close(0.0, 0.0)
        assert not mod._is_close(0.0, 1.0)


# --------------------------------------------------------------------------- #
#  Analyse notebooks
# --------------------------------------------------------------------------- #


class TestAnalyzeNotebook:
    def test_clean_notebook(self, tmp_path):
        nb = tmp_path / "clean.ipynb"
        _make_notebook([
            _markdown_cell("## Resultats\nLe ratio est 0.7."),
            _code_cell("print(0.7)", [{"text": "0.7\n"}]),
        ], nb)
        result = mod.analyze_notebook(nb)
        assert result.total_findings == 0
        assert result.n_prose_numbers == 1
        assert result.n_output_numbers == 1

    def test_prose_value_missing(self, tmp_path):
        nb = tmp_path / "missing.ipynb"
        _make_notebook([
            _markdown_cell("Phi = 0.69"),
            _code_cell("print(0.1875)", [{"text": "0.1875\n"}]),
        ], nb)
        result = mod.analyze_notebook(nb)
        assert result.total_findings == 1
        f = result.findings[0]
        assert f.category == "MISSING_FROM_OUTPUTS"
        assert f.prose_number == pytest.approx(0.69)

    def test_prose_within_tolerance(self, tmp_path):
        nb = tmp_path / "tol.ipynb"
        _make_notebook([
            _markdown_cell("Phi = 0.69"),
            _code_cell("print(0.70)", [{"text": "0.70\n"}]),
        ], nb)
        result = mod.analyze_notebook(nb)
        assert result.total_findings == 0

    def test_invalid_notebook(self, tmp_path):
        nb = tmp_path / "bad.ipynb"
        nb.write_text("not json", encoding="utf-8")
        result = mod.analyze_notebook(nb)
        assert result.error is not None
        assert result.total_findings == 0


# --------------------------------------------------------------------------- #
#  Gate anti-bruit dense-cell (EPIC #9768 Phase 0)
# --------------------------------------------------------------------------- #


class TestDenseCellOrphanGate:
    """Lock le gate anti-bruit sur les cellules denses (>=3 nombres prose).

    Contexte : le detecteur v2 emettait 21589 findings full-corpus dont
    l'inspection firsthand montre ~99% de FP (prose = references, numeros de
    section, dates, identifiants). Le gate n'emet MISSING_FROM_OUTPUTS pour une
    cellule DENSE que si la majorite de ses nombres sont orphelins (ratio >=
    MISSING_FROM_OUTPUTS_CELL_RATIO). Les cellules clairsemees (1-2 nombres)
    sont preservees : une mesure unique manquante reste un signal valide.
    """

    def test_sparse_cell_single_missing_still_emitted(self, tmp_path):
        # Cellule clairsemee (1 nombre) : la mesure manquante reste signalee.
        # C'est le contrat preserve (cf test_prose_value_missing).
        nb = tmp_path / "sparse.ipynb"
        _make_notebook([
            _markdown_cell("Sharpe = 0.69"),
            _code_cell("print(0.1875)", [{"text": "0.1875\n"}]),
        ], nb)
        result = mod.analyze_notebook(nb)
        assert result.total_findings == 1
        assert result.findings[0].category == "MISSING_FROM_OUTPUTS"

    def test_dense_cell_minority_orphan_suppressed(self, tmp_path):
        # Cellule dense (5 nombres) avec 1 orphelin sur 5 = 20% < seuil 50%.
        # C'est du bruit (4 nombres presentes, 1 reference croisee) -> supprime.
        nb = tmp_path / "dense_minority.ipynb"
        _make_notebook([
            _markdown_cell("a=0.5, b=0.6, c=0.7, d=0.8, ref=42"),
            _code_cell("print([0.5, 0.6, 0.7, 0.8])",
                       [{"text": "[0.5, 0.6, 0.7, 0.8]\n"}]),
        ], nb)
        result = mod.analyze_notebook(nb)
        mfo = [f for f in result.findings if f.category == "MISSING_FROM_OUTPUTS"]
        assert mfo == [], f"dense cell with minority orphan should be suppressed, got {mfo}"

    def test_dense_cell_majority_orphan_emitted(self, tmp_path):
        # Cellule dense (5 nombres) avec 4 orphelins sur 5 = 80% >= seuil 50%.
        # C'est de la derive authentique (la prose decrit des resultats non
        # calcules) -> signale.
        nb = tmp_path / "dense_majority.ipynb"
        _make_notebook([
            _markdown_cell("a=0.5, b=0.6, c=0.7, d=0.8, e=0.9"),
            _code_cell("print(0.5)", [{"text": "0.5\n"}]),  # seul 0.5 present
        ], nb)
        result = mod.analyze_notebook(nb)
        mfo = [f for f in result.findings if f.category == "MISSING_FROM_OUTPUTS"]
        assert len(mfo) == 4, f"4 orphans should survive the gate, got {len(mfo)}"

    def test_dense_cell_threshold_boundary(self, tmp_path):
        # Cellule dense (4 nombres) avec 2 orphelins sur 4 = 50% = seuil exact.
        # >= seuil -> signale (frontiere inclusive).
        nb = tmp_path / "boundary.ipynb"
        _make_notebook([
            _markdown_cell("a=0.5, b=0.6, c=0.7, d=0.8"),
            _code_cell("print([0.5, 0.6])", [{"text": "[0.5, 0.6]\n"}]),
        ], nb)
        result = mod.analyze_notebook(nb)
        mfo = [f for f in result.findings if f.category == "MISSING_FROM_OUTPUTS"]
        assert len(mfo) == 2, f"50% orphan at boundary should emit, got {len(mfo)}"


# --------------------------------------------------------------------------- #
#  FP class 2 (#9995) : cellules stub d'exercice
# --------------------------------------------------------------------------- #


class TestStubCellExerciseFilter:
    """FP class 2 (#9995) : prose d'enonce d'exercice precedant un stub.

    La prose d'enonce decrit le PROBLEME (donnees : maison 200 000 EUR,
    P=2%, prime 5 000), pas un RESULTAT. Le stub suivant ("Exercice a
    completer") n'a pas de sortie reelle -> ne peut rien verifier contre.
    Verifie firsthand DecPyMC-1 cell[25]->[26], Pyro_RSA_Hyperbole
    cell[15]->[16]. Corpus Probas : 112/1023 findings = 11% FP de cette classe.
    """

    def test_exercise_stub_output_suppresses(self, tmp_path):
        # Cas fondateur DecPyMC-1 : enonce d'exercice -> stub "a completer".
        # Les 3 nombres de l'enonce (200000, 0.02, 5000) sont des donnees,
        # pas des mesures -> MISSING_FROM_OUTPUTS supprime.
        nb = tmp_path / "stub.ipynb"
        _make_notebook([
            _markdown_cell("### Exercice : modele d'assurance\n"
                           "Maison de 200000 EUR, P(inondation) = 0.02, "
                           "prime 5000 EUR/an."),
            _code_cell("# TODO etudiant : construisez le modele\n"
                       "result = None",
                       [{"text": "Exercice a completer : assurance\n"}]),
        ], nb)
        result = mod.analyze_notebook(nb)
        mfo = [f for f in result.findings if f.category == "MISSING_FROM_OUTPUTS"]
        assert mfo == [], (
            f"exercise-setup prose before a stub must be suppressed, got {mfo}")

    def test_stub_detected_via_todo_source_no_phrase(self, tmp_path):
        # Stub marque uniquement en source (# TODO etudiant) sans la phrase
        # "Exercice a completer" dans l'output, mais sans sortie numerique.
        nb = tmp_path / "stub_src.ipynb"
        _make_notebook([
            _markdown_cell("On considere alpha = 0.15 et beta = 0.30."),
            _code_cell("# TODO etudiant : calculer le posterior\nresult = None",
                       [{"text": "(en attente de resolution)\n"}]),
        ], nb)
        result = mod.analyze_notebook(nb)
        mfo = [f for f in result.findings if f.category == "MISSING_FROM_OUTPUTS"]
        assert mfo == [], (
            f"stub marked in source (# TODO) suppresses setup prose, got {mfo}")

    def test_stub_with_real_numbers_not_suppressed(self, tmp_path):
        # Falsifiabilite (anti-overfilter) : un stub qui produit QUAND MEME des
        # nombres n'est pas un stub -- ses nombres sont des sorties reelles.
        # Ici le code a "# TODO" mais print un nombre -> 0.69 orphelin reste
        # signale (le filtre ne s'applique pas car has_numbers=True).
        nb = tmp_path / "stub_with_nums.ipynb"
        _make_notebook([
            _markdown_cell("Phi = 0.69"),
            _code_cell("# TODO etudiant : afficher Phi\nprint(0.1875)",
                       [{"text": "0.1875\n"}]),
        ], nb)
        result = mod.analyze_notebook(nb)
        mfo = [f for f in result.findings if f.category == "MISSING_FROM_OUTPUTS"]
        assert len(mfo) == 1 and mfo[0].prose_number == pytest.approx(0.69), (
            f"stub with real numeric output must NOT suppress the orphan, got {mfo}")

    def test_solved_exercise_not_affected(self, tmp_path):
        # Un exercice RESOLU (le nombre de la prose est dans l'output) -> pas de
        # finding, independamment du filtre (le filtre ne change rien ici).
        nb = tmp_path / "solved.ipynb"
        _make_notebook([
            _markdown_cell("### Exercice\nOn trouve Phi = 0.69."),
            _code_cell("print(0.69)", [{"text": "0.69\n"}]),
        ], nb)
        result = mod.analyze_notebook(nb)
        assert result.total_findings == 0

    def test_stub_not_immediately_following_not_suppressed(self, tmp_path):
        # Si une cellule markdown s'intercale entre l'enonce et le stub, le
        # signal "immediate next" ne s'applique pas -> pas de suppression
        # (signal tight, evite le sur-filtrage). La prose orpheline reste signalee.
        nb = tmp_path / "gap.ipynb"
        _make_notebook([
            _markdown_cell("Sharpe = 0.69"),
            _markdown_cell("## Note intermediaire"),  # s'intercale
            _code_cell("print(0.1875)", [{"text": "0.1875\n"}]),
        ], nb)
        result = mod.analyze_notebook(nb)
        mfo = [f for f in result.findings if f.category == "MISSING_FROM_OUTPUTS"]
        assert len(mfo) == 1, (
            f"non-adjacent stub must not suppress, got {len(mfo)}")

    def test_is_stub_code_cell_helper(self):
        # Tests unitaires du helper _is_stub_code_cell.
        stub_out = mod._code_cell if hasattr(mod, "_code_cell") else None
        # Stub via phrase placeholder, aucun nombre.
        cell_stub_phrase = {
            "cell_type": "code", "source": ["x = None"],
            "outputs": [{"text": "Exercice a completer : posterior\n"}],
            "execution_count": 3,
        }
        assert mod._is_stub_code_cell(cell_stub_phrase) is True
        # Stub via # TODO source, aucun nombre, output non-placeholder.
        cell_stub_src = {
            "cell_type": "code", "source": ["# TODO etudiant\nresult = None"],
            "outputs": [{"text": "(en attente)\n"}], "execution_count": 4,
        }
        assert mod._is_stub_code_cell(cell_stub_src) is True
        # Pas un stub : produit des nombres (sortie reelle).
        cell_real = {
            "cell_type": "code", "source": ["# TODO\nprint(0.5)"],
            "outputs": [{"text": "0.5\n"}], "execution_count": 5,
        }
        assert mod._is_stub_code_cell(cell_real) is False
        # Pas un stub : cellule markdown (helper renvoie False).
        assert mod._is_stub_code_cell(
            {"cell_type": "markdown", "source": ["x"]}) is False


# --------------------------------------------------------------------------- #
#  FP class 4 (#9995) : references bibliographiques (volume:page-page)
# --------------------------------------------------------------------------- #


class TestBibliographicReferenceFilter:
    """FP class 4 (#9995) : references bibliographiques au format volume:page-page.

    La prose qui cite une source (Comptes Rendus 25:536-538, textbook
    12:2825-2830, journal vol. 183:301-324) contient des nombres qui ne sont
    PAS des mesures calculees -- ce sont des identifiants de citation. Verifie
    firsthand : 38/10895 orphelins corpus (0.35%), concentres dans
    ML\\DataScienceWithAgents (textbook 12:2825-2830, 8+ notebooks) + Comptes
    Rendus 25:536-538 (DecPyMC-2) + NumPy 585:357-362 + GameTheory.
    """

    def test_helper_volume_match_with_context(self):
        # Comptes Rendus 25:536-538 -- le volume 25 est un identifiant de citation.
        text = "Resultat publie dans Comptes Rendus 25:536-538 (2024)."
        assert mod._is_bibliographic_reference(25.0, text) is True

    def test_helper_page_match_with_context(self):
        # Les pages 536 et 538 de la meme reference sont aussi des identifiants.
        text = "Resultat publie dans Comptes Rendus 25:536-538 (2024)."
        assert mod._is_bibliographic_reference(536.0, text) is True
        assert mod._is_bibliographic_reference(538.0, text) is True

    def test_helper_textbook_volume_with_keyword(self):
        # ML textbook citation 12:2825-2830 avec mot-cle "volume".
        text = "Theorique : voir volume 12:2825-2830 du manuel de reference."
        assert mod._is_bibliographic_reference(12.0, text) is True
        assert mod._is_bibliographic_reference(2825.0, text) is True

    def test_helper_no_context_not_filtered(self):
        # Falsifiabilite (anti-overfilter) : un pattern N:N-N SANS contexte
        # biblio (intervalle d'indices, range de donnees) n'est PAS filtre.
        # Ici "25:536-538" pourrait etre un intervalle d'indices sans contexte.
        text = "Les indices 25:536-538 couvrent la plage de donnees."
        assert mod._is_bibliographic_reference(25.0, text) is False
        assert mod._is_bibliographic_reference(536.0, text) is False

    def test_helper_no_pattern_not_filtered(self):
        # Aucun pattern N:N-N dans le texte -> le nombre demeure un orphelin.
        text = "Le ratio mesure est 0.69 et le seuil 0.5."
        assert mod._is_bibliographic_reference(0.69, text) is False
        assert mod._is_bibliographic_reference(25.0, text) is False

    def test_helper_value_not_in_pattern_not_filtered(self):
        # Un nombre qui n'est ni volume ni page d'un pattern biblio present ->
        # non filtre (conservateur).
        text = "Cf. Comptes Rendus 25:536-538 pour le detail."
        assert mod._is_bibliographic_reference(42.0, text) is False
        assert mod._is_bibliographic_reference(0.69, text) is False

    def test_helper_decimal_not_rounded_to_volume(self):
        # Anti-sur-filtrage (G.9, mesure corpus 2.7/Infer-16/PyMC-16) : une
        # DECIMALE comme 12.2 ou 5.7 ne doit PAS etre filtree meme si elle
        # s'arrondit au volume d'une ref biblio (12.2 -> 12 == vol de
        # 12:2825-2830). Un volume/page est TOUJOURS entier ; arrondir une
        # decimale = sur-filtrage non-falsifiable. 12.2 demeure un orphelin.
        text = "Cf. Journal of Machine Learning Research 12:2825-2830."
        assert mod._is_bibliographic_reference(12.2, text) is False
        assert mod._is_bibliographic_reference(12.3, text) is False
        # L'entier 12 (le vrai volume) EST filtre.
        assert mod._is_bibliographic_reference(12.0, text) is True
        text2 = "Journal of Machine Learning Research 6:1939-1959, sparse."
        assert mod._is_bibliographic_reference(6.2, text2) is False
        assert mod._is_bibliographic_reference(5.7, text2) is False
        assert mod._is_bibliographic_reference(6.0, text2) is True

    def test_integration_comptes_rendus_suppressed(self, tmp_path):
        # Cas fondateur DecPyMC-2 cell[23] : prose cite "Comptes Rendus
        # 25:536-538" -- 25, 536, 538 sont des identifiants de citation,
        # aucun output ne peut les "verifier" -> MISSING_FROM_OUTPUTS supprime.
        nb = tmp_path / "biblio.ipynb"
        _make_notebook([
            _markdown_cell("### Reference\n"
                           "Approche classique (Comptes Rendus 25:536-538) et "
                           "le seuil admissible 25."),
            _code_cell("print(0.1875)", [{"text": "0.1875\n"}]),
        ], nb)
        result = mod.analyze_notebook(nb)
        mfo = [f for f in result.findings if f.category == "MISSING_FROM_OUTPUTS"]
        # Le "25" est a la fois volume biblio ET repetition prose -- filtre.
        # Aucun autre orphelin legitime ici.
        biblio_filtered = [f for f in mfo if f.prose_number == pytest.approx(25.0)]
        assert biblio_filtered == [], (
            f"bibliographic volume 25 must be filtered, got {biblio_filtered}")

    def test_integration_legit_orphan_near_biblio_preserved(self, tmp_path):
        # Falsifiabilite : une mesure orpheline LEGITIME (0.69) dans une cellule
        # qui contient aussi une ref biblio (25:536-538) DOIT rester signalee.
        # Le filtre biblio ne supprime QUE les nombres de la citation, pas les
        # vraies mesures cohabitant dans la meme cellule.
        nb = tmp_path / "mixed.ipynb"
        _make_notebook([
            _markdown_cell("Le ratio observe est 0.69, cf. aussi Comptes Rendus "
                           "25:536-538 pour le contexte theorique."),
            _code_cell("print(0.1875)", [{"text": "0.1875\n"}]),
        ], nb)
        result = mod.analyze_notebook(nb)
        mfo = [f for f in result.findings if f.category == "MISSING_FROM_OUTPUTS"]
        legit = [f for f in mfo if f.prose_number == pytest.approx(0.69)]
        biblio = [f for f in mfo if f.prose_number in (25.0, 536.0, 538.0)]
        assert len(legit) == 1, (
            f"legit orphan 0.69 must survive the biblio filter, got {mfo}")
        assert biblio == [], (
            f"biblio ids 25/536/538 must be filtered, got {biblio}")

    def test_integration_dense_cell_biblio_filter_post_gate(self, tmp_path):
        # Le filtre biblio s'applique APRES le gate dense (preserve la
        # sémantique du ratio). Cellule dense (4 nombres) avec 3 orphelins
        # dont 2 sont biblio (25, 536) : la gate voit 3/4 = 75% >= 50% -> passe,
        # puis le filtre biblio retire 25 et 536 -> seul le legit 0.69 survive.
        nb = tmp_path / "dense_biblio.ipynb"
        _make_notebook([
            _markdown_cell("a=0.5, b=0.69, et Comptes Rendus 25:536-538."),
            _code_cell("print([0.5])", [{"text": "[0.5]\n"}]),  # seul 0.5 present
        ], nb)
        result = mod.analyze_notebook(nb)
        mfo = [f for f in result.findings if f.category == "MISSING_FROM_OUTPUTS"]
        # 0.69 legit orphelin survive ; 25 et 536 filtres par biblio.
        values = sorted(f.prose_number for f in mfo)
        assert 0.69 in values, f"legit 0.69 must survive, got {values}"
        assert 25.0 not in values, f"biblio vol 25 must be filtered, got {values}"
        assert 536.0 not in values, f"biblio page 536 must be filtered, got {values}"


# --------------------------------------------------------------------------- #
#  FP class 6 (#9998) : vol(issue):pages -- 2-tier safe-by-construction
# --------------------------------------------------------------------------- #


class TestVolIssuePagesFilter:
    """FP class 6 (#9998) : references bibliographiques au format
    ``vol(issue):pages`` (Nature 585(7825):357-362, Econometrica 50(6):1431-1451).

    Le pattern ancre volume + issue + page-range ensemble ; aucun des 4
    nombres n'est une mesure calculee. Heuristique 2-tier safe-by-construction
    (gate ``[gate-must-verify-detector-fp-before-wiring]``) :

    * **Tier 1** : keyword biblio en proximite 60 chars (Nature, Science,
      Proceedings, Journal, Comptes Rendus, Econometrica, etc.)
    * **Tier 2** : pattern anchor + year (19xx/20xx) sur la meme ligne

    Mesure corpus : 270 hits / 56 notebooks / 1080 valeurs ; 173 hits
    filtraient deja via Tier 1 des contextes biblio etendus ; 97
    supplementaires filtraient via Tier 2 (year on line) ; **0 hits ne
    filtraient par aucun tier** (real risk = 0).
    """

    def test_helper_nature_with_keyword(self):
        # Tier 1 -- Nature 585(7825):357-362, le keyword 'Nature' en
        # proximite 60 chars active le filtre. Tous les 4 nombres sont biblio.
        text = "Article publie dans Nature 585(7825):357-362 (2020)."
        assert mod._is_bibliographic_reference(585.0, text) is True
        assert mod._is_bibliographic_reference(7825.0, text) is True
        assert mod._is_bibliographic_reference(357.0, text) is True
        assert mod._is_bibliographic_reference(362.0, text) is True

    def test_helper_econometrica_with_keyword(self):
        # Tier 1 -- Econometrica 50(6):1431-1451, journal de référence.
        text = "Reference : Econometrica 50(6):1431-1451 (1982)."
        assert mod._is_bibliographic_reference(50.0, text) is True
        assert mod._is_bibliographic_reference(6.0, text) is True
        assert mod._is_bibliographic_reference(1431.0, text) is True
        assert mod._is_bibliographic_reference(1451.0, text) is True

    def test_helper_comptes_rendus_extended_keyword(self):
        # Tier 1 -- 'comptes rendus' matche le keyword etendu (case-insensitive,
        # pas d'accent requis). Meme pattern que Comptes Rendus 25:536-538 mais
        # avec issue explicite.
        text = "Cf. Comptes Rendus 56(3):712-720 (2024)."
        assert mod._is_bibliographic_reference(56.0, text) is True
        assert mod._is_bibliographic_reference(3.0, text) is True
        assert mod._is_bibliographic_reference(712.0, text) is True
        assert mod._is_bibliographic_reference(720.0, text) is True

    def test_helper_year_on_line_no_keyword(self):
        # Tier 2 -- pas de keyword biblio, mais l'annee (2019) sur la meme
        # ligne suffit. Cas legitime : une ref sans nom de journal explicite
        # mais datee.
        text = "Article 7(2):45-67, 2019. https://example.com/paper.html"
        assert mod._is_bibliographic_reference(7.0, text) is True
        assert mod._is_bibliographic_reference(2.0, text) is True
        assert mod._is_bibliographic_reference(45.0, text) is True
        assert mod._is_bibliographic_reference(67.0, text) is True

    def test_helper_annals_math_with_french_keyword(self):
        # Tier 1 -- journal francais 'Annales' (sibling 'annals' du keyword).
        text = "Annales de Mathematiques 54(2):286-295 (1901)."
        assert mod._is_bibliographic_reference(54.0, text) is True
        assert mod._is_bibliographic_reference(2.0, text) is True
        assert mod._is_bibliographic_reference(286.0, text) is True
        assert mod._is_bibliographic_reference(295.0, text) is True

    def test_helper_year_only_no_keyword(self):
        # Tier 2 -- year 2020 seule sur la ligne, sans keyword. Si le pattern
        # vol(issue):pages n'est pas accompagne d'un year sur la meme ligne,
        # le filtre EST conservateur (ne filtre pas).
        text = "Resultat 7(2):45-67 sur la plage de mesure."
        assert mod._is_bibliographic_reference(7.0, text) is False
        assert mod._is_bibliographic_reference(2.0, text) is False
        assert mod._is_bibliographic_reference(45.0, text) is False

    def test_helper_no_pattern_not_filtered(self):
        # Aucun pattern N(N):N-N -> nombre orphelin normal.
        text = "Le ratio est 0.69 et le seuil 0.5."
        assert mod._is_bibliographic_reference(0.69, text) is False
        assert mod._is_bibliographic_reference(25.0, text) is False

    def test_helper_value_not_in_pattern_not_filtered(self):
        # Anti-sur-filtrage (G.9) : un nombre qui n'est pas dans le pattern
        # (pas vol/issue/page) n'est pas filtre.
        text = "Nature 585(7825):357-362 contient la mesure cle 0.847."
        assert mod._is_bibliographic_reference(0.847, text) is False
        assert mod._is_bibliographic_reference(42.0, text) is False

    def test_helper_decimal_not_rounded_to_volume(self):
        # Anti-sur-filtrage (G.9) : 585.2 ne doit PAS etre filtre par le vol 585.
        text = "Nature 585(7825):357-362, mesure brute 585.2 mK."
        assert mod._is_bibliographic_reference(585.2, text) is False
        # L'entier 585 EST filtre.
        assert mod._is_bibliographic_reference(585.0, text) is True

    def test_integration_nature_suppressed(self, tmp_path):
        # Cas fondateur : Nature 585(7825):357-362, vol + issue + page-range.
        # Aucune sortie ne peut les 'verifier', mais ce sont des identifiants
        # de citation. 585, 7825, 357, 362 filtres.
        nb = tmp_path / "nature.ipynb"
        _make_notebook([
            _markdown_cell("Reference : Nature 585(7825):357-362 (2020)."),
            _code_cell("print(0.42)", [{"text": "0.42\n"}]),
        ], nb)
        result = mod.analyze_notebook(nb)
        mfo = [f for f in result.findings if f.category == "MISSING_FROM_OUTPUTS"]
        # Aucune des 4 biblio IDs ne doit etre signalee.
        for bib_id in (585.0, 7825.0, 357.0, 362.0):
            assert bib_id not in [f.prose_number for f in mfo], (
                f"biblio id {bib_id} must be filtered, got {mfo}")

    def test_integration_legit_orphan_near_vol_issue_pages_preserved(self, tmp_path):
        # Falsifiabilite : la mesure legitime 0.69 dans une cellule qui
        # contient aussi Nature 585(7825):357-362 DOIT rester signalee.
        nb = tmp_path / "mixed.ipynb"
        _make_notebook([
            _markdown_cell("ratio=0.69 (cf. Nature 585(7825):357-362)."),
            _code_cell("print(0.42)", [{"text": "0.42\n"}]),
        ], nb)
        result = mod.analyze_notebook(nb)
        mfo = [f for f in result.findings if f.category == "MISSING_FROM_OUTPUTS"]
        legit = [f for f in mfo if f.prose_number == pytest.approx(0.69)]
        biblio = [f for f in mfo if f.prose_number in (585.0, 7825.0, 357.0, 362.0)]
        assert len(legit) == 1, (
            f"legit orphan 0.69 must survive the vol(issue):pages filter, got {mfo}")
        assert biblio == [], (
            f"biblio ids 585/7825/357/362 must be filtered, got {biblio}")

    def test_integration_year_only_line(self, tmp_path):
        # Tier 2 path (real corpus finding) : 7(2):45-67, 2019 -- pas de
        # keyword biblio, mais year on line. Tous les 4 filtres.
        nb = tmp_path / "yearline.ipynb"
        _make_notebook([
            _markdown_cell("Paper 7(2):45-67, 2019. https://example.com"),
            _code_cell("print(0.5)", [{"text": "0.5\n"}]),
        ], nb)
        result = mod.analyze_notebook(nb)
        mfo = [f for f in result.findings if f.category == "MISSING_FROM_OUTPUTS"]
        for bib_id in (7.0, 2.0, 45.0, 67.0):
            assert bib_id not in [f.prose_number for f in mfo], (
                f"year-on-line anchor {bib_id} must be filtered, got {mfo}")


# --------------------------------------------------------------------------- #
#  Contre-epreuve positive ICT-1

# --------------------------------------------------------------------------- #


class TestNotebookCrossReferenceFilter:
    """FP class 5 (#9998) : references croisees vers un notebook voisin.

    La prose pedagogique pointe un autre notebook de la serie via un lien
    markdown dont le TEXTE est l'indice : « la theorie du
    [2.8](2.8-Theorie-PAC.ipynb) », « l'ACP du
    [2.6](2.6-Clustering-KMeans-PCA.ipynb) ». Le nombre (2.8, 2.6) est
    l'IDENTIFIANT du notebook pointe, pas une mesure. Verifie firsthand :
    25/10895 orphelins corpus (0.23%), concentres dans
    ML\\DataScienceWithAgents\\02-ML-Cours (cellules de conclusion/navigation).
    """

    def test_helper_link_match(self):
        # « theorie du [2.8](2.8-Theorie-PAC.ipynb) » -- 2.8 est l'indice du
        # notebook pointe, pas une mesure.
        text = "Relions ce constat a la sample complexity du [2.8](2.8-Theorie-PAC.ipynb)."
        assert mod._is_notebook_cross_reference(2.8, text) is True

    def test_helper_link_with_path_subdir(self):
        # Lien vers un notebook dans un sous-dossier (.ipynb present).
        text = "Voir [1.3](notebooks/1.3-Pandas.ipynb) pour Pandas."
        assert mod._is_notebook_cross_reference(1.3, text) is True

    def test_helper_multiple_links(self):
        # Cellule avec plusieurs liens : chacun matche sa propre valeur.
        text = ("compromis biais-variance du [2.5](2.5-Biais.ipynb) et "
                "capacite du [2.8](2.8-PAC.ipynb).")
        assert mod._is_notebook_cross_reference(2.5, text) is True
        assert mod._is_notebook_cross_reference(2.8, text) is True

    def test_helper_no_ipynb_link_not_filtered(self):
        # Falsifiabilite (anti-overfilter) : un nombre dans un lien markdown
        # qui ne pointe PAS vers un .ipynb (lien web, ancre) n'est pas filtre.
        text = "Voir [2.8](https://example.org) pour le detail."
        assert mod._is_notebook_cross_reference(2.8, text) is False
        text2 = "Aller a [2.8](#section) ci-dessous."
        assert mod._is_notebook_cross_reference(2.8, text2) is False

    def test_helper_keyword_only_not_filtered(self):
        # Anti-overfilter : le pattern keyword « section 2.8 » SANS lien .ipynb
        # n'est PAS filtre (trop ambigu -- un measurand pourrait coïncider avec
        # un numero de section). Seule la syntaxe de lien .ipynb est retenue.
        text = "Le cout d'ajustement de la section 2.8 n'est pas negligeable."
        assert mod._is_notebook_cross_reference(2.8, text) is False

    def test_helper_value_not_in_any_link_not_filtered(self):
        # Un nombre qui n'apparait dans AUCUN lien .ipynb -> non filtre.
        text = "Le ratio mesure est 0.69, cf. [2.8](2.8-PAC.ipynb) pour le contexte."
        assert mod._is_notebook_cross_reference(0.69, text) is False
        assert mod._is_notebook_cross_reference(2.8, text) is True

    def test_helper_integer_link_filtered(self):
        # Cas reel GameTheory/SymbolicAI : certaines series nomment leurs
        # notebooks par un INDICE ENTIER. « [12](12-quelquechose.ipynb) » ->
        # 12 est l'indice du notebook pointe, pas une mesure. L'exclusion
        # historique des entiers (refutee par forensic po-2023 c.188) est levee.
        text = "Voir [12](12-quelquechose.ipynb) pour la suite."
        assert mod._is_notebook_cross_reference(12.0, text) is True

    def test_helper_integer_gameyseries_nav_link(self):
        # Cas fondateur (forensic po-2023 c.188, SymbolicAI 15% / GameTheory 34%
        # des MISSING_FROM_OUTPUTS) : barre de navigation entre notebooks d'une
        # serie a indice entier. Le « 7 » de « GameTheory-7 » est l'indice du
        # notebook pointe, dans le texte ET dans l'URL du lien .ipynb.
        text = ("**Navigation** : [GameTheory-7](GameTheory-7-ExtensiveForm-Csharp.ipynb) "
                "| [GameTheory-11 (Bayesien)](GameTheory-11-BayesianGames.ipynb)")
        assert mod._is_notebook_cross_reference(7.0, text) is True
        assert mod._is_notebook_cross_reference(11.0, text) is True

    def test_helper_integer_prevnext_bar(self):
        # Barre prev/next « [<< 12-Reputation] » : l'indice 12 est en tete du
        # texte du lien, objet navigationnel, pas une mesure.
        text = "**Transition** : [<< 12-ReputationGames](12-ReputationGames.ipynb)"
        assert mod._is_notebook_cross_reference(12.0, text) is True

    def test_helper_integer_overfilter_guard_occurrence_outside_link(self):
        # Anti-sur-filtrage (propriete SAFE cle, entiers) : si un entier apparait
        # a la fois dans un lien .ipynb ET comme occurrence hors-lien (potentielle
        # vraie mesure en prose, ex. « 2 joueurs »), on NE filtre PAS. Le
        # conservatisme prime -- l'occurrence hors-lien peut etre le measurand.
        text = "Ce jeu a 2 joueurs, cf. [2-Coordination](2-Coordination.ipynb)."
        assert mod._is_notebook_cross_reference(2.0, text) is False

    def test_helper_integer_measurement_cell_not_overfiltered(self):
        # La cellule peut cohabiter indices-entiers (filtres) ET vraies mesures
        # decimales (preservees) -- le filtre est par-valeur, SAFE. Ici 0.73 est
        # une vraie valeur de Shapley en prose hors-lien -> non filtre, tandis
        # que 15 (indice du notebook pointe) est filtre.
        text = ("La valeur de Shapley calculee est 0.73 ; "
                "suite : [GameTheory-15-Cooperatif](GameTheory-15-CooperativeGames.ipynb)")
        assert mod._is_notebook_cross_reference(15.0, text) is True
        assert mod._is_notebook_cross_reference(0.73, text) is False

    def test_helper_overfilter_guard_occurrence_outside_link(self):
        # Anti-sur-filtrage (propriete SAFE cle) : si N.M apparait a la fois
        # dans un lien .ipynb ET comme occurrence hors-lien (potentielle vraie
        # mesure en prose), on NE filtre PAS -- l'occurrence hors-lien pourrait
        # etre le measurand legitime. Le conservatisme prime.
        text = "Le ratio mesure est 2.8, cf. [2.8](2.8-Theorie-PAC.ipynb)."
        assert mod._is_notebook_cross_reference(2.8, text) is False

    def test_helper_long_link_text_leading_index(self):
        # Cas reel 2.9-Grokking : le lien a un texte long « [<< 2.8-Theorie-PAC] »
        # ou l'indice 2.8 est en tete. L'indice dans le texte ET dans l'URL.
        text = "Retour sur la theorie du [<< 2.8-Theorie-PAC](2.8-Theorie-PAC.ipynb)."
        assert mod._is_notebook_cross_reference(2.8, text) is True

    def test_integration_navigation_cell_suppressed(self, tmp_path):
        # Cas fondateur 2.9-Grokking cell[0] : cellule de navigation avec liens
        # vers les notebooks voisins de la serie. Les indices 2.8/3.1 cites
        # dans les liens ne sont pas des mesures -> MISSING_FROM_OUTPUTS supprime.
        # Note : on n'ecrit PAS de « (2.8) » hors-lien -- un indice hors-lien
        # n'est pas filtre par le LINK-only filter (cas KEYWORD defer, volontai-
        # rement conservateur). Les indices decimaux (2.8, 3.1) et entiers
        # sont desormais tous deux filtres (forensic po-2023 c.188).
        nb = tmp_path / "nav.ipynb"
        _make_notebook([
            _markdown_cell("# 2.9 Grokking\n"
                           "**Navigation** : [<< 2.8-Theorie-PAC](2.8-Theorie-PAC.ipynb) "
                           "| [>> 3.1-Suite](3.1-Suite.ipynb)"),
            _code_cell("print(0.5)", [{"text": "0.5\n"}]),
        ], nb)
        result = mod.analyze_notebook(nb)
        mfo = [f for f in result.findings if f.category == "MISSING_FROM_OUTPUTS"]
        xref_filtered = [f for f in mfo if f.prose_number in (2.8, 3.1)]
        assert xref_filtered == [], (
            f"notebook xref indices 2.8/3.1 must be filtered, got {xref_filtered}")

    def test_integration_legit_orphan_near_link_preserved(self, tmp_path):
        # Falsifiabilite : une mesure orpheline LEGITIME (0.69) dans une cellule
        # qui contient aussi un lien .ipynb (2.8) DOIT rester signalee. Le filtre
        # ne supprime QUE la valeur dans le lien, pas les vraies mesures
        # cohabitant dans la meme cellule.
        nb = tmp_path / "mixed.ipynb"
        _make_notebook([
            _markdown_cell("Le ratio observe est 0.69, cf. la theorie du "
                           "[2.8](2.8-Theorie-PAC.ipynb) pour le contexte."),
            _code_cell("print(0.1875)", [{"text": "0.1875\n"}]),
        ], nb)
        result = mod.analyze_notebook(nb)
        mfo = [f for f in result.findings if f.category == "MISSING_FROM_OUTPUTS"]
        legit = [f for f in mfo if f.prose_number == pytest.approx(0.69)]
        xref = [f for f in mfo if f.prose_number == pytest.approx(2.8)]
        assert len(legit) == 1, (
            f"legit orphan 0.69 must survive the xref filter, got {mfo}")
        assert xref == [], (
            f"xref index 2.8 must be filtered, got {xref}")


# --------------------------------------------------------------------------- #
#  FP class 1 (#9998) : parametres de code restitues dans la prose (backtick)
# --------------------------------------------------------------------------- #


class TestCodeDefinedValueFilter:
    """FP class 1 (#9998) : parametres de code restitues dans la prose en span backtick.

    Un nombre orphelin n'est pas une mesure manquante si la prose le cite comme
    un PARAMETRE de code, entre backticks : « `n_init=10` », « `random_state=42` »,
    « `alpha=0,5` ». La valeur pilote le calcul, elle n'en est pas un output.

    SAFE par construction (mesure corpus firsthand, 4 gardes cumulatifs) :
      1. assignment ``identifiant = valeur`` DANS un span backtick (l'auteur cite
         du CODE). Une METRIQUE RESTITUEE en prose narrative (« **MAE = 0,41** »)
         n'est jamais backtickee -> non filtree : c'est un output a verifier.
      2. identifiant non-resultat-de-solveur (exclut ``x_1 = 0.5``).
      3. valeur = RHS complet (pas une formule ``MONEY = 10000·M`` ni un % ``heat = 18%``).
      4. bornes numeriques + ``_`` (exclut le prefixe 4 de ``QUORUM = 4_000_000``).

    Verifie firsthand ML.NET : 2/184 (ML-1 Size=2.5, ML-8 n_init=10) ; full corpus
    65 orphelins filtres. Aucune metrique restituee (MAE/RMSE/score) filtree.
    """

    def test_helper_backtick_param_int(self):
        # "`n_init=10`" -- 10 est un parametre de KMeans, cite en backtick.
        text = "K-Means avec `n_clusters=3`, `random_state=42`, `n_init=10`."
        assert mod._is_code_defined_value(10.0, text) is True
        assert mod._is_code_defined_value(42.0, text) is True

    def test_helper_backtick_param_decimal(self):
        # "`alpha=0.5`" -- decimale en backtick.
        text = "Regression ridge avec `alpha=0.5`."
        assert mod._is_code_defined_value(0.5, text) is True

    def test_helper_backtick_param_fr_decimal(self):
        # "`alpha=0,5`" -- decimale francaise en backtick (prose pedagogique FR).
        text = "Regression ridge avec `alpha=0,5` (seuil FR)."
        assert mod._is_code_defined_value(0.5, text) is True

    def test_helper_no_backtick_not_filtered(self):
        # Anti-sur-filtrage : une valeur en prose SANS backtick n'est pas filtree
        # (peut etre une metrique narrative). "Sharpe = 0.69" non backticke.
        text = "Le ratio de Sharpe est 0.69 sur la periode OOS."
        assert mod._is_code_defined_value(0.69, text) is False

    def test_helper_reported_metric_bold_not_filtered(self):
        # Anti-sur-filtrage (cas ML-4 c[36]) : une METRIQUE RESTITUEE en prose
        # narrative (MAE, RMSE) en gras n'est PAS un parametre de code -> non
        # filtree. C'est un output que le detecteur doit pouvoir verifier.
        text = "Les metriques sont **R^2 = 0,941**, **MAE = 0,41**, **RMSE = 2,33**."
        assert mod._is_code_defined_value(0.41, text) is False
        assert mod._is_code_defined_value(2.33, text) is False

    def test_helper_solver_result_backtick_not_filtered(self):
        # Anti-sur-filtrage (cas OR-tools-Stiegler c[13]) : une VALEUR DE SOLUTION
        # de solveur restituee en backtick (`x_1 = 0.5`) est un OUTPUT, pas un
        # parametre de config -> non filtree.
        text = "La solution optimale est `x_1 = 0.5` et `x_2 = 0.3`."
        assert mod._is_code_defined_value(0.5, text) is False

    def test_helper_formula_expression_not_filtered(self):
        # Anti-sur-filtrage (cas 13_Cryptarithmetic c[2]) : une formule en
        # backtick (`MONEY = 10000·M + ...`) -- 10000 est un coefficient de
        # place-value, RHS incomplet -> non filtre.
        text = "Decomposition : `MONEY = 10000·M + 1000·O + 100·N + 10·E + Y`."
        assert mod._is_code_defined_value(10000.0, text) is False

    def test_helper_unicode_minus_formula_not_filtered(self):
        # Anti-sur-filtrage (cas 05-SemanticKernel c[19]) : identite mathematique
        # avec moins Unicode U+2212 « Cosine Distance = 1 − ... » -> 1 non filtre.
        text = "Rappel : `Cosine Distance = 1 − Cosine Similarity`."
        assert mod._is_code_defined_value(1.0, text) is False

    def test_helper_underscore_grouping_not_filtered(self):
        # Anti-sur-filtrage (cas SC-9 c[5]) : le separateur underscore `4_000_000`
        # ne doit pas faire matcher le prefixe 4 comme parametre.
        text = "Seuil de gouvernance `QUORUM = 4_000_000` tokens."
        assert mod._is_code_defined_value(4.0, text) is False

    def test_helper_comparison_not_filtered(self):
        # Anti-sur-filtrage : un comparateur (`count >= 5`, `ratio == 0.9`) n'est
        # pas un assignment de parametre.
        text = "On garde si `count >= 5` et `ratio == 0.9`."
        assert mod._is_code_defined_value(5.0, text) is False
        assert mod._is_code_defined_value(0.9, text) is False

    def test_helper_value_not_in_any_assignment_not_filtered(self):
        # Un nombre hors de tout assignment backtick -> orphelin normal.
        text = "Le code `model.fit(X)` produit un score. Valeur cible 0.69."
        assert mod._is_code_defined_value(0.69, text) is False

    def test_integration_param_suppressed(self, tmp_path):
        # Cas fondateur ML-8 c[5] : prose cite `n_init=10` -> 10 orphelin filtre.
        nb = tmp_path / "param.ipynb"
        _make_notebook([
            _markdown_cell("## Pipeline\nK-Means avec `n_clusters=3`, `n_init=10` "
                           "(10 redemarrages)."),
            _code_cell("print(0.42)", [{"text": "0.42\n"}]),
        ], nb)
        result = mod.analyze_notebook(nb)
        mfo = [f for f in result.findings if f.category == "MISSING_FROM_OUTPUTS"]
        filtered = [f for f in mfo if f.prose_number == pytest.approx(10.0)]
        assert filtered == [], f"param n_init=10 must be filtered, got {filtered}"

    def test_integration_legit_orphan_alongside_param_preserved(self, tmp_path):
        # Falsifiabilite : une vraie mesure orpheline (0.69) coexistant avec un
        # parametre backtick (n_init=10) DOIT rester signalee.
        nb = tmp_path / "mixed.ipynb"
        _make_notebook([
            _markdown_cell("Sharpe observe = 0.69 ; K-Means `n_init=10`."),
            _code_cell("print(0.42)", [{"text": "0.42\n"}]),
        ], nb)
        result = mod.analyze_notebook(nb)
        mfo = [f for f in result.findings if f.category == "MISSING_FROM_OUTPUTS"]
        legit = [f for f in mfo if f.prose_number == pytest.approx(0.69)]
        param = [f for f in mfo if f.prose_number == pytest.approx(10.0)]
        assert len(legit) == 1, f"legit orphan 0.69 must survive, got {mfo}"
        assert param == [], f"param n_init=10 must be filtered, got {param}"


# --------------------------------------------------------------------------- #


class TestICT1CounterEvidence:
    """Le detecteur v3 DOIT signaler ICT-1 PRE-`7de14792c` (issue #9416).

    A la revision `e8dc56ac9` (parent du fix), la prose dit
    « un pic a 2,31, le reste a 0,19 » (2 niveaux) mais les outputs
    exhibent 3 niveaux dont 0.6875 qui ne figure pas dans la prose.

    Note : cette contre-epreuve lit le notebook depuis le worktree parent
    (D:/dev/CoursIA-2-c1266-9790-v3-prose-outputs) ou depuis la copie
    principale. Si le notebook est absent (lint ignore), on skip avec un
    pytest.skip explicite -- le test est OPTIONNEL selon la disponibilite
    du fichier, mais RECOMMANDE en pre-merge.
    """

    # Cherchons d'abord une racine de repo presente (worktree parent
    # OU copie principale OU env var). Le path Linux/Windows natif est
    # developper-specific (cf Hermes review nit) -- on prend n'importe
    # lequel qui existe, sinon on skip explicitement.
    _CANDIDATE_ROOTS = (
        Path("D:/dev/CoursIA-2"),
        Path("D:/dev/CoursIA"),
        Path(os.environ.get("COURSIA_ROOT", "") or "_/_"),
    )
    REPO_ROOT = next((p for p in _CANDIDATE_ROOTS if p.exists() and p.is_dir()), _CANDIDATE_ROOTS[0])
    NB_PATH = "MyIA.AI.Notebooks/IIT/ICT-Series/ICT-1-PhiTrajectories.ipynb"

    def test_pre_fix_ict_1_signaled(self):
        """Lecture du notebook a la revision parente du fix #9416 via git show.

        Le commit fix est `7de14792c` (« ICT-1 conclusion restores the 0.69
        intermediate Phi relief »). Son parent = `7de14792c^` = l'etat
        pre-fix avec prose « un pic a 2,31, le reste a 0,19 » qui omet le
        3e niveau 0.6875 deja present dans `cell[7]`.

        Skip si aucune racine de repo n'est accessible (path developper-specific
        sur le runner CI). Cf Hermes review nit PR #9793.
        """
        if not self.REPO_ROOT.exists():
            pytest.skip(f"Repo root {self.REPO_ROOT} absent (developper-specific path)")
        try:
            content = subprocess.check_output(
                ["git", "show", "7de14792c^:MyIA.AI.Notebooks/IIT/ICT-Series/ICT-1-PhiTrajectories.ipynb"],
                cwd=str(self.REPO_ROOT),
                stderr=subprocess.PIPE,
            )
        except subprocess.CalledProcessError:
            pytest.skip("ICT-1 absent ou commit absent localement")
        # Ecriture dans un tmp pour analyse via le module.
        import tempfile
        with tempfile.NamedTemporaryFile(suffix=".ipynb", delete=False) as f:
            f.write(content)
            tmp_path = Path(f.name)
        try:
            result = mod.analyze_notebook(tmp_path)
        finally:
            tmp_path.unlink()
        # La prose pre-#9416 inclut « 2,31 » et « 0,19 » mais PAS « 0,69 ».
        # Les outputs incluent 0.6875 (avec arrondi). Le detecteur DOIT
        # signaler au moins un finding MISSING_FROM_OUTPUTS sur la valeur
        # 0.69 OU un cas ou la prose enonce « un pic a 2,31, le reste a 0,19 »
        # (donc pretend qu'il n'y a que 2 niveaux) mais les outputs en
        # exhibent 3.
        # C'est la classe MISSING_FROM_PROSE_ENUMERATION si implementee,
        # ou MISSING_FROM_OUTPUTS sinon (au moins un nombre de la prose
        # qui ne matche pas les outputs directement).
        # Pour cette V1, on accepte tout finding dans ICT-1 pre-fix.
        assert result.total_findings >= 1, (
            f"Contre-epreuve positive ICT-1 pre-#9416 devrait signaler "
            f"au moins 1 finding, mais 0 trouve. "
            f"prose_n={result.n_prose_numbers}, output_n={result.n_output_numbers}"
        )
        # La definition du succes de v3 (issue #9790) : la categorie
        # MISSING_FROM_PROSE_ENUMERATION DOIT etre parmi les findings,
        # pas seulement MISSING_FROM_OUTPUTS (qui peut etre silencieux
        # si les 2 niveaux de la prose matchent au tolerance pres).
        enum_findings = [f for f in result.findings
                         if f.category == "MISSING_FROM_PROSE_ENUMERATION"]
        assert enum_findings, (
            f"Contre-epreuve ICT-1 doit produire >= 1 finding "
            f"MISSING_FROM_PROSE_ENUMERATION (cas fondateur #9416), "
            f"aucun trouve parmi {len(result.findings)} findings. "
            f"categories={[f.category for f in result.findings]}"
        )


# --------------------------------------------------------------------------- #
#  Walk full-corpus
# --------------------------------------------------------------------------- #


class TestIterNotebooks:
    def test_simple(self, tmp_path):
        _make_notebook(
            [_markdown_cell("x = 0.5"), _code_cell("print(0.5)", [{"text": "0.5"}])],
            tmp_path / "a.ipynb",
        )
        (tmp_path / "sub").mkdir()
        _make_notebook(
            [_markdown_cell("y = 0.3"), _code_cell("print(0.3)", [{"text": "0.3"}])],
            tmp_path / "sub" / "b.ipynb",
        )
        results = list(mod.iter_notebooks(tmp_path))
        assert len(results) == 2

    def test_excludes_archive_dirs(self, tmp_path):
        _make_notebook(
            [_markdown_cell("x = 0.5"), _code_cell("print(0.5)", [{"text": "0.5"}])],
            tmp_path / "a.ipynb",
        )
        (tmp_path / "_archive").mkdir()
        _make_notebook(
            [_markdown_cell("y = 0.3"), _code_cell("print(0.3)", [{"text": "0.3"}])],
            tmp_path / "_archive" / "b.ipynb",
        )
        results = list(mod.iter_notebooks(tmp_path))
        assert len(results) == 1
        assert results[0].name == "a.ipynb"

    def test_root_does_not_exist(self, tmp_path):
        results = list(mod.iter_notebooks(tmp_path / "does_not_exist"))
        assert results == []


# --------------------------------------------------------------------------- #
#  Smoke full-corpus (limite pour CI)
# --------------------------------------------------------------------------- #


class TestCorpusScanSmoke:
    """Smoke test sur le corpus reel avec --limit=10 (CI-friendly)."""

    def test_scan_real_corpus_limited(self):
        # Cherchons une racine corpus accessible (worktree, copie principale, env var).
        candidates = (
            Path("D:/dev/CoursIA-2-c1266-9790-v3-prose-outputs/MyIA.AI.Notebooks"),
            Path("D:/dev/CoursIA-2/MyIA.AI.Notebooks"),
            Path("D:/dev/CoursIA/MyIA.AI.Notebooks"),
            Path(os.environ.get("COURSIA_NOTEBOOKS", "") or "_/_"),
        )
        p = next((c for c in candidates if c.exists() and c.is_dir()), candidates[0])
        if not p.exists():
            pytest.skip(f"Corpus {p} non disponible (developper-specific path)")
        results = mod.scan_corpus(p, exclude_dirs=mod.DEFAULT_EXCLUDE_DIRS)
        # On prend juste les 10 premiers pour le smoke.
        results = results[:10]
        for r in results:
            assert r.error is None or r.findings  # soit OK, soit finding documente
            assert r.n_code_cells >= 0  # au moins parse


# --------------------------------------------------------------------------- #
#  CLI
# --------------------------------------------------------------------------- #


class TestCLI:
    def test_exit_code_2_on_missing_root(self, tmp_path):
        """Lecon po-2024 #9783 : chemin inexistant DOIT retourner 2, pas 0 ni 1."""
        result = subprocess.run(
            [sys.executable, "-m", "scan_d5_prose_outputs_alignment",
             "--root", str(tmp_path / "absent"), "--check"],
            cwd=_ROOT, capture_output=True, text=True,
        )
        assert result.returncode == 2, f"attendu 2, obtenu {result.returncode}\n{result.stderr}"

    def test_exit_code_1_on_pathological(self, tmp_path):
        """Si un notebook a un finding et --check, exit 1."""
        nb = tmp_path / "bad.ipynb"
        _make_notebook([
            _markdown_cell("Phi = 0.69"),
            _code_cell("print(0.1875)", [{"text": "0.1875\n"}]),
        ], nb)
        result = subprocess.run(
            [sys.executable, "-m", "scan_d5_prose_outputs_alignment",
             "--root", str(tmp_path), "--check"],
            cwd=_ROOT, capture_output=True, text=True,
        )
        assert result.returncode == 1

    def test_exit_code_0_on_clean(self, tmp_path):
        nb = tmp_path / "ok.ipynb"
        _make_notebook([
            _markdown_cell("Ratio OK 0.7"),
            _code_cell("print(0.7)", [{"text": "0.7\n"}]),
        ], nb)
        result = subprocess.run(
            [sys.executable, "-m", "scan_d5_prose_outputs_alignment",
             "--root", str(tmp_path), "--check"],
            cwd=_ROOT, capture_output=True, text=True,
        )
        assert result.returncode == 0
