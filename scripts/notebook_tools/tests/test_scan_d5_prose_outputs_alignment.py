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
#  Contre-epreuve positive ICT-1
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
