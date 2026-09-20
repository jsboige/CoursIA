"""Tests du banc fini de composition de regards (opération 12)."""

import pytest
from ict import regards as rg


@pytest.fixture(scope="module")
def family():
    return rg.reference_family()


def by_name(family, name):
    return next(regard for regard in family if regard.name == name)


@pytest.mark.parametrize("stratum,size", [("W", 9), ("Z3", 3), ("Z2", 2)])
def test_declared_strata_have_expected_size(stratum, size):
    assert len(rg.elements(stratum)) == size


@pytest.mark.parametrize(
    "name", ["idW", "idZ3", "idZ2", "SWAP", "LUM", "LUM-D",
             "CHG", "CHG-D", "SHIFT", "MEMO"]
)
def test_reference_components_are_lenses(family, name):
    assert rg.law_report(by_name(family, name))["is_lens"]


@pytest.mark.parametrize("stratum", ["W", "Z3", "Z2"])
def test_identity_is_a_lens(stratum):
    assert rg.law_report(rg.identity(stratum))["is_lens"]


def test_unknown_stratum_is_rejected():
    with pytest.raises(ValueError, match="inconnue"):
        rg.identity("missing")


def test_all_composable_pairs_remain_lenses(family):
    reports = [
        rg.law_report(rg.compose(outer, inner))
        for inner in family
        for outer in family
        if inner.tgt == outer.src
    ]
    assert len(reports) == 32
    assert all(report["is_lens"] for report in reports)


def test_incompatible_composition_is_rejected(family):
    with pytest.raises(ValueError, match="non composables"):
        rg.compose(by_name(family, "LUM"), by_name(family, "MEMO"))


@pytest.mark.parametrize("name", ["SWAP", "LUM", "CHG", "SHIFT", "MEMO"])
def test_left_and_right_units_extensionally_agree(family, name):
    regard = by_name(family, name)
    left = rg.compose(rg.identity(regard.tgt), regard)
    right = rg.compose(regard, rg.identity(regard.src))
    assert rg.agreement(left, regard, on="get")["rate"] == 1.0
    assert rg.agreement(left, regard, on="put")["rate"] == 1.0
    assert rg.agreement(right, regard, on="get")["rate"] == 1.0
    assert rg.agreement(right, regard, on="put")["rate"] == 1.0


@pytest.mark.parametrize("left_name,right_name", [("LUM", "LUM-D"), ("CHG", "CHG-D")])
def test_direct_witness_has_total_forward_agreement(family, left_name, right_name):
    report = rg.agreement(by_name(family, left_name), by_name(family, right_name), on="get")
    assert report["same"] == 9
    assert report["total"] == 9


@pytest.mark.parametrize("left_name,right_name", [("LUM", "LUM-D"), ("CHG", "CHG-D")])
def test_direct_witness_has_eighteen_backward_disagreements(family, left_name, right_name):
    report = rg.agreement(by_name(family, left_name), by_name(family, right_name), on="put")
    assert report["same"] == 9
    assert report["total"] == 27
    assert len(report["disagreements"]) == 18


def test_direct_agreement_occurs_exactly_without_correction(family):
    lum = by_name(family, "LUM")
    lum_d = by_name(family, "LUM-D")
    report = rg.agreement(lum, lum_d, on="put")
    agreeing = {
        (state, demand)
        for state in rg.elements("W")
        for demand in rg.elements("Z3")
        if (state, demand) not in {
            (row[0], row[1]) for row in report["disagreements"]
        }
    }
    assert agreeing == {(state, state[0]) for state in rg.elements("W")}


@pytest.mark.parametrize(
    "outer_name,expected_disagreements,expected_total",
    [("MEMO", 9, 18), ("SHIFT", 18, 27)],
)
def test_witness_survives_composition(family, outer_name, expected_disagreements, expected_total):
    outer = by_name(family, outer_name)
    left = rg.compose(outer, by_name(family, "LUM"))
    right = rg.compose(outer, by_name(family, "LUM-D"))
    forward = rg.agreement(left, right, on="get")
    backward = rg.agreement(left, right, on="put")
    assert forward["rate"] == 1.0
    assert len(backward["disagreements"]) == expected_disagreements
    assert backward["total"] == expected_total


def test_composed_disagreement_is_visible_to_third_regard(family):
    memo = by_name(family, "MEMO")
    left = rg.compose(memo, by_name(family, "LUM"))
    right = rg.compose(memo, by_name(family, "LUM-D"))
    report = rg.witness_report(left, right, by_name(family, "CHG"), 0)
    assert report["detected"] == ((1, 0), (1, 1), (1, 2))


def test_composed_disagreement_is_invisible_to_forward_reading(family):
    memo = by_name(family, "MEMO")
    left = rg.compose(memo, by_name(family, "LUM"))
    right = rg.compose(memo, by_name(family, "LUM-D"))
    report = rg.witness_report(left, right, by_name(family, "LUM"), 0)
    assert report["n_detectable"] == 0


def test_associativity_is_exhaustive_on_reference_domain(family):
    report = rg.associativity_report(family)
    assert report == {
        "n_composable_triples": 92,
        "n_points": 2422,
        "n_violations": 0,
        "violations": (),
    }


def test_associativity_second_pass_checks_every_point(family):
    report = rg.associativity_report(tuple(reversed(family)))
    assert report["n_points"] == 2422
    assert report["violations"] == ()


def test_correct_swap_composition_preserves_laws(family):
    swap = by_name(family, "SWAP")
    report = rg.law_report(rg.compose(swap, swap))
    assert report["is_lens"]


def test_wrong_composition_breaks_get_put(family):
    swap = by_name(family, "SWAP")
    report = rg.law_report(rg.compose_without_reinjection(swap, swap))
    assert len(report["get_put_violations"]) == 6


def test_wrong_composition_breaks_put_get(family):
    swap = by_name(family, "SWAP")
    report = rg.law_report(rg.compose_without_reinjection(swap, swap))
    assert len(report["put_get_violations"]) == 54


def test_op12_verdict_is_deterministic():
    assert rg.op12_verdict() == rg.op12_verdict()


def test_op12_verdict_checks_both_legs_of_both_units():
    units = rg.op12_verdict()["units"]
    assert set(units) == {"SWAP", "LUM", "LUM-D", "CHG", "CHG-D", "SHIFT", "MEMO"}
    assert all(
        report == {
            "right_get": 1.0,
            "right_put": 1.0,
            "left_get": 1.0,
            "left_put": 1.0,
        }
        for report in units.values()
    )


def test_op12_verdict_exposes_all_evidence():
    assert set(rg.op12_verdict()) == {
        "laws", "witness_direct", "witness_mirror", "witness_composed",
        "associativity", "control_correct", "control_wrong", "units",
    }
