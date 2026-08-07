"""Tests de `ict.proxy_contextuality` (ICT #7290).

Invariants falsifiables couverts :

1. **Le detecteur detecte.** Sur la boite PR -- dont l'insatisfiabilite se prouve
   a la main par parite -- le verdict est ``STRONGLY_CONTEXTUAL``. Un detecteur
   qui rendrait SAT ici serait casse, et tout verdict rendu sur des donnees
   reelles serait sans valeur.
2. **Les deux degenerescences dominent le verdict de contextualite.** Un modele
   sans recouvrement ne recoit jamais ``NON_CONTEXTUAL`` (SAT force par
   construction) ; un modele a supports singletons ne recoit jamais
   ``STRONGLY_CONTEXTUAL`` (UNSAT trivial). C'est le garde-fou
   anti-analogie-decorative, et c'est ce que testent
   `test_no_overlap_*` / `test_rigid_*`.
3. **Les trois crans se distinguent.** Un modele peut etre satisfiable tout en
   portant une obstruction locale : le cran ``LOGICALLY_CONTEXTUAL`` doit etre
   rendu, pas ``NON_CONTEXTUAL``. Sans quoi un SAT brut conclurait a tort.
4. **CP-SAT et l'enumeration exhaustive s'accordent.** Le desaccord est un bug
   d'encodage, jamais un resultat -- il doit lever.
5. **Determinisme.** L'enumeration rend le meme ordre a chaque appel (elle
   canonicalise les temoins que CP-SAT, lui, ne garantit pas).
6. **La minimalite est une vraie minimalite.** Retirer n'importe quel contexte
   de la sous-famille rendue doit rendre le modele satisfiable.

Pattern herite de `test_compression.py` : bootstrap `sys.path` module-level,
sans fixtures.
"""

import os
import sys

import pytest

_HERE = os.path.dirname(os.path.abspath(__file__))
_ROOT = os.path.dirname(_HERE)
sys.path.insert(0, _ROOT)

from ict import proxy_contextuality as pc  # noqa: E402

try:
    from ortools.sat.python import cp_model  # noqa: F401

    _HAS_ORTOOLS = True
except ImportError:
    _HAS_ORTOOLS = False


# --------------------------------------------------------------------------- #
#  1. Le detecteur detecte : boite PR fortement contextuelle                   #
# --------------------------------------------------------------------------- #
def test_pr_box_has_no_global_section():
    """Preuve par parite : somme des 4 contraintes XOR = 1 (mod 2), impossible."""
    model = pc.pr_box_model()
    assert pc.global_sections(model) == []


def test_pr_box_verdict_is_strongly_contextual():
    out = pc.contextuality_verdict(pc.pr_box_model())
    assert out["verdict"] == pc.STRONGLY_CONTEXTUAL
    assert out["satisfiable"] is False


def test_pr_box_is_not_degenerate():
    """L'UNSAT de la boite PR doit etre structurel, pas un artefact."""
    report = pc.overlap_report(pc.pr_box_model())
    assert report["degeneracy"] is None
    assert report["n_shared_proxies"] == 4  # a1, a2, b1, b2 chacun dans 2 contextes
    assert report["min_support_size"] == 2  # aucun support singleton
    assert report["n_distinct_covers"] == 4  # recouvrement genuinement partiel


def test_pr_box_minimal_obstruction_is_the_whole_family():
    """Les 4 contextes sont necessaires : c'est la ceremonie complete qui bloque."""
    model = pc.pr_box_model()
    minimal = pc.minimal_obstruction(model)
    assert minimal is not None
    assert len(minimal) == 4


def test_pr_box_minimal_obstruction_is_irreducible():
    """Propriete de minimalite : retirer un contexte quelconque rend SAT."""
    model = pc.pr_box_model()
    minimal = pc.minimal_obstruction(model)
    for drop in minimal:
        sub = pc.EmpiricalModel(
            contexts=tuple(model.contexts[i] for i in minimal if i != drop),
            outcomes=model.outcomes,
        )
        assert pc.global_sections(sub, limit=1), (
            f"retirer le contexte {drop} devrait rendre satisfiable"
        )


def test_minimal_obstruction_excludes_irrelevant_context():
    """Un contexte permissif ajoute ne doit pas entrer dans l'obstruction minimale."""
    xor0 = ((0, 0), (1, 1))
    xor1 = ((0, 1), (1, 0))
    full = ((0, 0), (0, 1), (1, 0), (1, 1))
    model = pc.empirical_model(
        [
            pc.Context(("a1", "b1"), xor0),
            pc.Context(("a1", "b2"), xor0),
            pc.Context(("a2", "b1"), xor0),
            pc.Context(("a2", "b2"), xor1),
            pc.Context(("a1", "a2"), full),  # ne contraint rien
        ],
        outcomes=(0, 1),
    )
    minimal = pc.minimal_obstruction(model)
    assert minimal is not None
    assert 4 not in minimal
    assert len(minimal) == 4


def test_minimal_obstruction_is_none_when_satisfiable():
    assert pc.minimal_obstruction(pc.non_contextual_model()) is None


# --------------------------------------------------------------------------- #
#  2. Les degenerescences dominent (le garde-fou)                              #
# --------------------------------------------------------------------------- #
def test_no_overlap_is_flagged_degenerate():
    """Sans proxy partage, SAT est force : le verdict ne doit pas etre NON_CONTEXTUAL."""
    model = pc.empirical_model(
        [
            pc.Context(("a1", "a2"), ((0, 0), (1, 1))),
            pc.Context(("b1", "b2"), ((0, 1), (1, 0))),
        ],
        outcomes=(0, 1),
    )
    assert pc.overlap_report(model)["degeneracy"] == pc.DEGENERATE_NO_OVERLAP
    out = pc.contextuality_verdict(model)
    assert out["verdict"] == pc.DEGENERATE_NO_OVERLAP
    # ... et pourtant le modele EST satisfiable : c'est precisement pour cela
    # que rapporter "non contextuel" ici serait vide.
    assert out["satisfiable"] is True
    assert out["verdict"] != pc.NON_CONTEXTUAL


def test_rigid_supports_unsat_is_not_reported_as_contextual():
    """LE test decisif du garde-fou.

    Recouvrement reel (``b`` est dans les deux contextes) et UNSAT (``b`` doit
    valoir 0 et 1), mais chaque support est un singleton : l'UNSAT n'est qu'un
    changement de valeur d'un contexte a l'autre -- une dissociation, pas une
    obstruction. Le verdict doit etre DEGENERATE_RIGID.
    """
    model = pc.empirical_model(
        [
            pc.Context(("a", "b"), ((0, 0),)),
            pc.Context(("b", "c"), ((1, 1),)),
        ],
        outcomes=(0, 1),
    )
    assert pc.global_sections(model) == []  # bien UNSAT
    out = pc.contextuality_verdict(model)
    assert out["verdict"] == pc.DEGENERATE_RIGID
    assert out["verdict"] != pc.STRONGLY_CONTEXTUAL
    assert "singleton" in out["rationale"]


def test_identical_covers_are_flagged_single_cover():
    """Meme ensemble de proxys partout => recouvrement trivial, question reduite.

    Le modele est UNSAT (aucun tuple commun aux deux supports), mais ce n'est pas
    de la contextualite : c'est un desaccord entre deux protocoles mesurant
    exactement la meme chose.
    """
    model = pc.empirical_model(
        [
            pc.Context(("p", "q"), ((0, 0), (0, 1))),
            pc.Context(("p", "q"), ((1, 0), (1, 1))),
        ],
        outcomes=(0, 1),
    )
    assert pc.global_sections(model) == []  # UNSAT
    out = pc.contextuality_verdict(model)
    assert out["verdict"] == pc.DEGENERATE_SINGLE_COVER
    assert out["verdict"] != pc.STRONGLY_CONTEXTUAL
    assert "PARTIEL" in out["rationale"]


def test_single_context_is_single_cover():
    """Un contexte unique : la section globale est son support, par construction."""
    model = pc.empirical_model([pc.Context(("p", "q"), ((0, 1),))], outcomes=(0, 1))
    assert pc.overlap_report(model)["degeneracy"] == pc.DEGENERATE_SINGLE_COVER


def test_single_cover_takes_precedence_over_rigid():
    """Les deux sont vraies ; le recouvrement trivial est le constat plus fondamental."""
    model = pc.empirical_model(
        [pc.Context(("p", "q"), ((0, 0),)), pc.Context(("p", "q"), ((1, 1),))],
        outcomes=(0, 1),
    )
    report = pc.overlap_report(model)
    assert report["max_support_size"] == 1  # rigide aussi
    assert report["degeneracy"] == pc.DEGENERATE_SINGLE_COVER


def test_partial_cover_is_what_lifts_degeneracy():
    """Contexte-temoin : c'est le passage a un recouvrement PARTIEL qui debloque."""
    partial = pc.empirical_model(
        [
            pc.Context(("p", "q"), ((0, 0), (1, 1))),
            pc.Context(("q", "r"), ((0, 0), (1, 1))),
        ],
        outcomes=(0, 1),
    )
    report = pc.overlap_report(partial)
    assert report["n_distinct_covers"] == 2
    assert report["shared_proxies"] == ["q"]
    assert report["degeneracy"] is None


def test_no_overlap_takes_precedence_over_rigid():
    """Les deux degenerescences peuvent coexister ; l'absence de recouvrement gagne."""
    model = pc.empirical_model(
        [pc.Context(("a",), ((0,),)), pc.Context(("b",), ((1,),))],
        outcomes=(0, 1),
    )
    assert pc.overlap_report(model)["degeneracy"] == pc.DEGENERATE_NO_OVERLAP


def test_degeneracy_reason_is_always_populated():
    for model in (
        pc.empirical_model(
            [pc.Context(("a", "b"), ((0, 0),)), pc.Context(("b", "c"), ((1, 1),))],
            outcomes=(0, 1),
        ),
        pc.empirical_model(
            [
                pc.Context(("a1", "a2"), ((0, 0), (1, 1))),
                pc.Context(("b1", "b2"), ((0, 1), (1, 0))),
            ],
            outcomes=(0, 1),
        ),
    ):
        report = pc.overlap_report(model)
        assert report["degeneracy"] is not None
        assert report["degeneracy_reason"]


# --------------------------------------------------------------------------- #
#  3. Les trois crans se distinguent                                           #
# --------------------------------------------------------------------------- #
def test_non_contextual_model_verdict():
    out = pc.contextuality_verdict(pc.non_contextual_model())
    assert out["verdict"] == pc.NON_CONTEXTUAL
    assert out["satisfiable"] is True
    assert out["logical"]["n_without_extension"] == 0


def test_logically_but_not_strongly_contextual_is_distinguished():
    """SAT, donc pas fortement contextuel -- mais l'obstruction survit, localisee.

    C'est le modele qu'un simple test SAT declarerait "non contextuel" a tort.
    """
    model = pc.logically_but_not_strongly_contextual_model()
    sections = pc.global_sections(model)
    assert sections, "ce modele doit admettre au moins une section globale"

    out = pc.contextuality_verdict(model)
    assert out["verdict"] == pc.LOGICALLY_CONTEXTUAL
    assert out["satisfiable"] is True
    assert out["verdict"] != pc.NON_CONTEXTUAL
    assert out["logical"]["n_without_extension"] > 0


def test_logical_witnesses_really_have_no_extension():
    """Verifie les temoins un a un contre l'enumeration, sans faire confiance au verdict."""
    model = pc.logically_but_not_strongly_contextual_model()
    logical = pc.logical_contextuality(model)
    sections = pc.global_sections(model)
    for w in logical["witnesses"]:
        ctx = model.contexts[w["context_index"]]
        target = tuple(w["outcome"])
        assert target in ctx.support
        assert all(ctx.restrict(s) != target for s in sections)


def test_strongly_contextual_implies_no_logical_key():
    """Le cran 2 ne se calcule que si des sections globales existent."""
    out = pc.contextuality_verdict(pc.pr_box_model())
    assert "logical" not in out


def test_logical_contextuality_counts_all_local_sections():
    model = pc.non_contextual_model()
    logical = pc.logical_contextuality(model)
    assert logical["n_local_sections"] == 16  # 4 contextes x 4 tuples
    assert logical["logically_contextual"] is False


# --------------------------------------------------------------------------- #
#  4. CP-SAT s'accorde avec l'oracle exhaustif                                 #
# --------------------------------------------------------------------------- #
@pytest.mark.skipif(not _HAS_ORTOOLS, reason="OR-Tools absent")
def test_cpsat_agrees_with_exhaustive_on_all_fixtures():
    for builder in (
        pc.pr_box_model,
        pc.logically_but_not_strongly_contextual_model,
        pc.non_contextual_model,
    ):
        model = builder()
        exhaustive = bool(pc.global_sections(model, limit=1))
        cp = pc.global_sections_cpsat(model)
        assert cp["available"] is True
        assert cp["satisfiable"] == exhaustive, f"desaccord sur {builder.__name__}"


@pytest.mark.skipif(not _HAS_ORTOOLS, reason="OR-Tools absent")
def test_cpsat_never_returns_a_witness():
    """Le temoin CP-SAT n'est pas deterministe : il ne doit pas etre rapporte."""
    cp = pc.global_sections_cpsat(pc.non_contextual_model())
    assert "assignment" not in cp
    assert "solution" not in cp
    assert set(cp) == {"available", "satisfiable", "status_name"}


@pytest.mark.skipif(not _HAS_ORTOOLS, reason="OR-Tools absent")
def test_cpsat_handles_non_contiguous_alphabet():
    """Un alphabet non contigu ne doit pas laisser passer les valeurs intermediaires."""
    model = pc.empirical_model(
        [pc.Context(("a", "b"), ((0, 7), (7, 0)))], outcomes=(0, 7)
    )
    exhaustive = pc.global_sections(model)
    assert len(exhaustive) == 2
    assert pc.global_sections_cpsat(model)["satisfiable"] is True


def test_verdict_without_ortools_still_decides():
    """cross_check=False : l'oracle exhaustif suffit, aucun resultat n'est fabrique."""
    out = pc.contextuality_verdict(pc.pr_box_model(), cross_check=False)
    assert out["verdict"] == pc.STRONGLY_CONTEXTUAL
    assert out["cpsat"]["available"] is False


# --------------------------------------------------------------------------- #
#  5. Determinisme et bornes                                                   #
# --------------------------------------------------------------------------- #
def test_enumeration_is_deterministic():
    model = pc.non_contextual_model()
    assert pc.global_sections(model) == pc.global_sections(model)


def test_enumeration_order_is_lexicographic_on_sorted_proxies():
    model = pc.non_contextual_model()
    sections = pc.global_sections(model)
    assert list(sections[0].keys()) == sorted(sections[0].keys())
    assert sections[0] == {"a1": 0, "a2": 0, "b1": 0, "b2": 0}


def test_search_space_too_large_raises():
    model = pc.non_contextual_model()  # 2**4 = 16
    with pytest.raises(OverflowError):
        pc.global_sections(model, max_search=8)


def test_verdict_reports_inconclusive_rather_than_guessing():
    out = pc.contextuality_verdict(
        pc.non_contextual_model(), max_search=8, cross_check=False
    )
    assert out["verdict"] == pc.INCONCLUSIVE_TOO_LARGE
    assert out["satisfiable"] is None


def test_limit_stops_enumeration_early():
    sections = pc.global_sections(pc.non_contextual_model(), limit=3)
    assert len(sections) == 3


# --------------------------------------------------------------------------- #
#  6. Validation de construction : une erreur, jamais un silence               #
# --------------------------------------------------------------------------- #
def test_empty_support_is_an_error_not_a_permissive_context():
    with pytest.raises(ValueError, match="support vide"):
        pc.Context(("a", "b"), ())


def test_arity_mismatch_raises():
    with pytest.raises(ValueError, match="arite"):
        pc.Context(("a", "b"), ((0, 1), (0,)))


def test_duplicate_proxy_in_context_raises():
    with pytest.raises(ValueError, match="dupliques"):
        pc.Context(("a", "a"), ((0, 1),))


def test_empty_context_raises():
    with pytest.raises(ValueError, match="au moins un proxy"):
        pc.Context((), ((0,),))


def test_no_context_raises():
    with pytest.raises(ValueError, match="au moins un contexte"):
        pc.empirical_model([])


def test_outcome_outside_alphabet_raises():
    with pytest.raises(ValueError, match="hors alphabet"):
        pc.empirical_model([pc.Context(("a",), ((5,),))], outcomes=(0, 1))


def test_trivial_alphabet_raises():
    """Une seule issue possible : toute assignation est forcee, la question est vide."""
    with pytest.raises(ValueError, match="trivial"):
        pc.empirical_model([pc.Context(("a", "b"), ((0, 0),))], outcomes=(0,))


def test_model_accepts_mapping_form():
    model = pc.empirical_model(
        [{"proxies": ["a", "b"], "support": [(0, 0), (1, 1)]}], outcomes=(0, 1)
    )
    assert model.measurements == ("a", "b")
    assert model.search_space == 4


# --------------------------------------------------------------------------- #
#  7. Pont mesures -> modele : mesurer une fois rend le test vide              #
# --------------------------------------------------------------------------- #
def test_single_seed_per_context_yields_singleton_supports():
    """Une graine par contexte => supports singletons.

    C'est l'exigence de protocole rendue mesurable : sans plusieurs graines par
    contexte, les supports sont rigides et aucun verdict de contextualite n'est
    atteignable (cf. `test_rigid_supports_unsat_is_not_reported_as_contextual`).
    """
    signatures = {
        "ctx_A": [{"spectral_gap": 0.1, "sensitivity_mean": 0.9}],
        "ctx_B": [{"spectral_gap": 0.9, "sensitivity_mean": 0.1}],
    }
    model, _ = pc.model_from_signatures(
        signatures, ("spectral_gap", "sensitivity_mean")
    )
    assert pc.overlap_report(model)["max_support_size"] == 1


def test_multiple_seeds_produce_non_singleton_supports():
    """Plusieurs graines lèvent bien la rigidite des supports."""
    signatures = {
        "ctx_A": [
            {"spectral_gap": 0.1, "sensitivity_mean": 0.9},
            {"spectral_gap": 0.8, "sensitivity_mean": 0.2},
        ],
        "ctx_B": [
            {"spectral_gap": 0.9, "sensitivity_mean": 0.1},
            {"spectral_gap": 0.2, "sensitivity_mean": 0.8},
        ],
    }
    model, thresholds = pc.model_from_signatures(
        signatures, ("spectral_gap", "sensitivity_mean")
    )
    report = pc.overlap_report(model)
    assert report["min_support_size"] == 2
    assert set(thresholds) == {"spectral_gap", "sensitivity_mean"}


def test_bridge_always_yields_single_cover_degeneracy():
    """LE constat structurel sur le zoo ICT, rendu executable.

    Le pont affecte tous les proxys a chaque contexte -- parce que les proxys du
    zoo partagent la signature ``(states, n_symbols)`` et sont donc
    conjointement mesurables. Le modele produit est donc toujours
    DEGENERATE_SINGLE_COVER : la question KS n'est pas posable en l'etat, quel
    que soit le nombre de graines.
    """
    signatures = {
        "ctx_A": [{"p": 0.1, "q": 0.9}, {"p": 0.8, "q": 0.2}],
        "ctx_B": [{"p": 0.9, "q": 0.1}, {"p": 0.2, "q": 0.8}],
        "ctx_C": [{"p": 0.5, "q": 0.5}, {"p": 0.3, "q": 0.7}],
    }
    model, _ = pc.model_from_signatures(signatures, ("p", "q"))
    report = pc.overlap_report(model)
    assert report["n_distinct_covers"] == 1
    assert report["degeneracy"] == pc.DEGENERATE_SINGLE_COVER
    out = pc.contextuality_verdict(model)
    assert out["verdict"] == pc.DEGENERATE_SINGLE_COVER
    assert out["verdict"] not in {pc.NON_CONTEXTUAL, pc.STRONGLY_CONTEXTUAL}


def test_median_thresholds_split_the_corpus():
    signatures = {
        "c1": [{"p": 0.0}, {"p": 1.0}],
        "c2": [{"p": 2.0}, {"p": 3.0}],
    }
    thr = pc.median_split_thresholds(signatures, ("p",))
    assert thr["p"] == pytest.approx(1.5)


def test_discretization_is_ge_threshold():
    signatures = {"c1": [{"p": 1.5}], "c2": [{"p": 0.0}]}
    model, thr = pc.model_from_signatures(signatures, ("p",), thresholds={"p": 1.5})
    supports = {ctx.support for ctx in model.contexts}
    assert ((1,),) in supports  # 1.5 >= 1.5 -> issue 1
    assert ((0,),) in supports
    assert thr["p"] == 1.5


def test_context_without_measurement_raises():
    with pytest.raises(ValueError, match="sans aucune mesure"):
        pc.model_from_signatures({"c1": []}, ("p",))


def test_missing_proxy_in_all_runs_raises():
    with pytest.raises(ValueError, match="aucune mesure pour le proxy"):
        pc.median_split_thresholds({"c1": [{"other": 1.0}]}, ("p",))


# --------------------------------------------------------------------------- #
#  8. Coherence interne du rapport                                             #
# --------------------------------------------------------------------------- #
def test_overlap_report_multiplicity_matches_contexts():
    report = pc.overlap_report(pc.pr_box_model())
    assert report["context_multiplicity"] == {"a1": 2, "a2": 2, "b1": 2, "b2": 2}
    assert report["search_space"] == 16


def test_verdict_always_carries_overlap_and_rationale():
    for builder in (
        pc.pr_box_model,
        pc.logically_but_not_strongly_contextual_model,
        pc.non_contextual_model,
    ):
        out = pc.contextuality_verdict(builder())
        assert out["rationale"]
        assert "overlap" in out
        assert out["verdict"] in {
            pc.STRONGLY_CONTEXTUAL,
            pc.LOGICALLY_CONTEXTUAL,
            pc.NON_CONTEXTUAL,
        }


def test_admits_and_restrict_are_consistent():
    ctx = pc.Context(("a", "b"), ((0, 1),))
    assert ctx.restrict({"a": 0, "b": 1, "c": 9}) == (0, 1)
    assert ctx.admits({"a": 0, "b": 1}) is True
    assert ctx.admits({"a": 1, "b": 1}) is False
