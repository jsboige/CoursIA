"""Tests du Kernel drift guard -- tolerance numerique 1 ULP (#19961).

Decision codee ici : « bruit assume » -- deux signatures float dont les
valeurs sont egales a 1 ULP pres ne sont PAS un drift. C'est l'extension a
la signature float de la doctrine #17371 (patch drift sans changement de
semantique), motivee par la mesure #19961 : une re-exec ICT-23 sous 3.13.3
face a une base 3.13.13 produit des byte-repr differents a 1 ULP pres et
faisait rougir le guard sur une PR saine (#19787).

Les contre-temoins sont la moitie de la valeur du fichier : une tolerance
qui blanchirait TOUT ne serait plus un garde.
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "notebook_tools"))

from check_kernel_drift import (  # noqa: E402
    _diff_signatures_ordinal,
    _signatures_equivalent,
    _within_ulp,
    diff_signatures,
    float_signatures,
)

ONE_ULP_BELOW_1 = 0.9999999999999999   # 1 nextafter step sous 1.0
TWO_ULP_BELOW_1 = 0.9999999999999998   # 2 steps


def _nb(*outputs_text, cell_id="c1"):
    return {
        "cells": [
            {
                "cell_type": "code",
                "id": cell_id,
                "outputs": [
                    {"output_type": "execute_result",
                     "data": {"text/plain": text}}
                    for text in outputs_text
                ],
            }
        ]
    }


class TestWithinUlp:
    def test_exact_equality(self):
        assert _within_ulp(1.0, 1.0)

    def test_one_ulp_is_noise(self):
        assert _within_ulp(1.0, ONE_ULP_BELOW_1)
        assert _within_ulp(ONE_ULP_BELOW_1, 1.0)

    def test_two_ulp_is_drift(self):
        assert not _within_ulp(1.0, TWO_ULP_BELOW_1)

    def test_nan_nan_accepted(self):
        assert _within_ulp(float("nan"), float("nan"))

    def test_nan_vs_value_refused(self):
        assert not _within_ulp(float("nan"), 1.0)

    def test_infinities_require_exact_sign(self):
        assert _within_ulp(float("inf"), float("inf"))
        assert not _within_ulp(float("inf"), float("-inf"))
        assert not _within_ulp(float("inf"), 1e308)

    def test_subnormal_one_step(self):
        assert _within_ulp(0.0, 5e-324)     # le plus petit sous-normal
        assert not _within_ulp(0.0, 1e-323)

    def test_complex_partwise(self):
        assert _within_ulp(complex(1.0, 2.0), complex(ONE_ULP_BELOW_1, 2.0))
        assert not _within_ulp(complex(1.0, 2.0), complex(1.0, 2.5))


class TestSignaturesEquivalent:
    def test_numpy2_repr_case_is_noise(self):
        """Le cas fondateur : NumPy 1.x imprime 1.0 la ou 2.x imprime
        0.9999999999999999 -- meme valeur a 1 ULP pres, pas de drift."""
        base = ("[1.0, 1.0, 1.0]",)
        head = (f"[1.0, {ONE_ULP_BELOW_1!r}, 1.0]",)
        assert base != head                      # byte-text DIFFERENT
        assert _signatures_equivalent(base, head)

    def test_beyond_one_ulp_stays_drift(self):
        base = ("[1.0, 1.0]",)
        head = (f"[{TWO_ULP_BELOW_1!r}, 1.0]",)
        assert not _signatures_equivalent(base, head)

    def test_different_value_stays_drift(self):
        assert not _signatures_equivalent(("[1.0, 2.0]",), ("[1.0, 2.1]",))

    def test_element_count_mismatch_stays_drift(self):
        assert not _signatures_equivalent(("[1.0, 1.0]",), ("[1.0]",))

    def test_array_count_mismatch_stays_drift(self):
        assert not _signatures_equivalent(("[1.0, 1.0]",), ())
        assert not _signatures_equivalent(
            ("[1.0, 1.0]",), ("[1.0, 1.0]", "[2.0, 3.0]"))

    def test_identical_text_short_circuits(self):
        assert _signatures_equivalent(("[1.0, 1.0]",), ("[1.0, 1.0]",))

    def test_unparseable_falls_back_to_text_fail_closed(self):
        """Une paire qui ne parse pas retombe sur l'egalite textuelle :
        jamais d'equivalence fabriquee sur une valeur non mesuree."""
        assert _signatures_equivalent(("[1.0, a.b]",), ("[1.0, a.b]",))
        assert not _signatures_equivalent(("[1.0, a.b]",), ("[1.0, c.d]",))


class TestDiffSignatures:
    def test_id_aligned_one_ulp_not_reported(self):
        base = _nb("[1.0, 1.0, 1.0]")
        head = _nb(f"[1.0, {ONE_ULP_BELOW_1!r}, 1.0]")
        b_sig, h_sig = float_signatures(base), float_signatures(head)
        assert b_sig != h_sig
        assert diff_signatures(b_sig, h_sig, base_nb=base, head_nb=head) == []

    def test_id_aligned_beyond_one_ulp_reported(self):
        base = _nb("[1.0, 1.0]")
        head = _nb(f"[{TWO_ULP_BELOW_1!r}, 1.0]")
        b_sig, h_sig = float_signatures(base), float_signatures(head)
        assert diff_signatures(b_sig, h_sig, base_nb=base, head_nb=head) == ["c1"]

    def test_ordinal_fallback_same_tolerance(self):
        # Notebooks sans ids : alignement ordinal legacy, meme tolerance.
        base = _nb("[1.0, 1.0]")
        base["cells"][0].pop("id")
        head = _nb(f"[1.0, {ONE_ULP_BELOW_1!r}]")
        head["cells"][0].pop("id")
        b_sig, h_sig = float_signatures(base), float_signatures(head)
        assert _diff_signatures_ordinal(b_sig, h_sig) == []
        head2 = _nb("[1.0, 2.0]")
        head2["cells"][0].pop("id")
        assert _diff_signatures_ordinal(b_sig, float_signatures(head2)) == [0]
