"""Tests du pont Python des preuves Lean AMD et Groves (jalon 3 de #22381).

Ce que ces tests mesurent :

- l'**extracteur** lit les declarations d'un `.lean` (commentaires imbriques,
  namespaces imbriques, enonce coupe au premier `:` de tete) — et il est
  verifie sur des sources synthetiques, donc sans dependre de la toolchain Lean ;
- la **transcription** est verrouillee : un `.lean` modifie sans regeneration
  produit une derive nommee, une declaration renommee est signalee, et un
  module absent n'est pas un succes — c'est un etat declare ;
- les **instances** du pont (temoin AMD, impossibilite, pivot de Clarke, temoin
  negatif `badAlloc`) rendent le verdict de l'enonce forme, et une contradiction
  entre les deux leve `BridgeMismatch` au lieu de passer ;
- la **convention de signe** de `Groves.lean` (transfert recu) est necessaire :
  sous le signe naif, le temoin negatif disparait — c'est mesure, pas affirme.

Aucun carnet, aucun `.lean` : ces tests n'ecrivent rien dans le depot.
"""

import itertools
import sys
from dataclasses import replace
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from amd_lean_bridge import (  # noqa: E402
    AMD_LEAN,
    BAD_ALLOC_VALUES,
    GROVES_LEAN,
    TRANSCRIPTION_AMD,
    TRANSCRIPTION_GROVES,
    TRANSCRIPTION_TARGETS_AMD,
    BridgeCheck,
    BridgeMismatch,
    all_instances,
    bad_alloc_domain,
    bad_alloc_instance,
    bad_alloc_mechanism,
    build_transcription,
    check_transcription,
    clarke_domain,
    clarke_g,
    clarke_mechanism,
    dump_transcription,
    ensure_conforms,
    groves_others_welfare,
    groves_payment,
    groves_payoff,
    groves_welfare,
    issue_val,
    lean_u0,
    lean_u1,
    o_star,
    p_star,
    parse_lean_declarations,
    payments_from_groves,
    strip_lean_comments,
    theta_val,
    to_int_profile,
    welfare_maximiser,
)
from amd_synthesis import (  # noqa: E402
    Mechanism,
    amd_domain,
    amd_star_mechanism,
    synthesize,
    verify,
    verify_dsic_sincere_anchored,
    verify_ir_sincere,
    verify_utility,
)


# ---------------------------------------------------------------------------
# Extracteur : verifie sur des sources synthetiques
# ---------------------------------------------------------------------------

NESTED_SOURCE = """
import Mathlib.Tactic

namespace Outer

/-! bloc de documentation
    /- imbrique : ceci ne doit pas fermer le bloc -/
    encore du texte
-/

/-- Docstring de `foo`. -/
def foo (x : ℕ) : ℕ := x + 1  -- commentaire de ligne

namespace Inner

theorem bar (h : foo 0 = 1) : True := by
  trivial

end Inner

end Outer
"""


def test_strip_lean_comments_handles_nested_blocks():
    """Un bloc `/- -/` imbrique ne ferme pas le bloc parent."""
    stripped = strip_lean_comments(NESTED_SOURCE)
    assert "imbrique" not in stripped
    assert "Docstring" not in stripped
    assert "commentaire de ligne" not in stripped
    assert "def foo (x : ℕ) : ℕ := x + 1" in stripped
    assert "theorem bar" in stripped


def test_strip_lean_comments_preserves_line_structure():
    """Retirer un commentaire ne colle pas deux declarations sur une meme ligne."""
    source = "def a : ℕ := 0\n/- x -/\ndef b : ℕ := 1\n"
    stripped = strip_lean_comments(source)
    assert stripped.count("\n") == source.count("\n")
    declarations = parse_lean_declarations(source)
    assert set(declarations) == {"a", "b"}


def test_strip_lean_comments_rejects_unclosed_block():
    """Un bloc non ferme est une erreur nommee, pas un silence."""
    with pytest.raises(ValueError, match="non ferme"):
        strip_lean_comments("def a : ℕ := 0\n/- jamais ferme\n")


def test_parse_tracks_nested_namespaces():
    """Un namespace imbrique qualifie la declaration, `end` depile un niveau."""
    declarations = parse_lean_declarations(NESTED_SOURCE)
    assert set(declarations) == {"Outer.foo", "Outer.Inner.bar"}
    assert declarations["Outer.foo"].kind == "def"
    assert declarations["Outer.Inner.bar"].kind == "theorem"


def test_parse_cuts_the_statement_at_the_top_level_colon():
    """Un `:` dans un binder n'est pas le `:` de tete de l'enonce."""
    source = (
        "theorem foo (h : ∀ x, x = x) (h2 : 1 = 1) :\n"
        "    ∀ y, y ≥ 0 := by\n  intro y\n  exact Nat.zero_le y\n"
    )
    declarations = parse_lean_declarations(source)
    assert declarations["foo"].statement == "∀ y, y ≥ 0"


def test_parse_statement_of_a_bare_abbrev():
    """`abbrev X := Y` n'a pas de type annonce : l'enonce est le corps."""
    declarations = parse_lean_declarations("abbrev AgentType := Bool\n")
    assert declarations["AgentType"].statement == "Bool"
    assert declarations["AgentType"].kind == "abbrev"


def test_parse_rejects_duplicate_declarations():
    """Deux declarations de meme nom qualifie sont ambigues, pas silencieuses."""
    with pytest.raises(ValueError, match="dupliquee"):
        parse_lean_declarations("def a : ℕ := 0\ndef a : ℕ := 1\n")


# ---------------------------------------------------------------------------
# Extracteur : verifie sur AMD.lean (le fichier reel)
# ---------------------------------------------------------------------------


def test_amd_source_is_present():
    """Sans `AMD.lean`, tout le reste du pont perd son ancrage : on le dit ici."""
    assert AMD_LEAN.is_file(), f"source Lean introuvable : {AMD_LEAN}"


def test_amd_source_contains_exactly_the_transcribed_declarations():
    """Le jour ou une declaration apparait dans `AMD.lean`, ce test le reclame.

    C'est le verrou de COMPLETUDE : la transcription ne peut pas rester
    partielle sans que la suite le signale.
    """
    declarations = parse_lean_declarations(AMD_LEAN.read_text(encoding="utf-8"))
    assert set(declarations) == set(TRANSCRIPTION_TARGETS_AMD)


def test_amd_transcription_matches_the_lean_source():
    """Aucune derive entre la transcription du pont et le `.lean` sur disque."""
    drifts = check_transcription(AMD_LEAN, TRANSCRIPTION_AMD)
    assert drifts == (), "\n".join(str(d) for d in drifts)


def test_amd_key_statements_are_transcribed_verbatim():
    """Les enonces cites par les instances sont ceux du fichier, au mot pres."""
    assert TRANSCRIPTION_AMD["SocialChoice.AMD.amd_star_DSIC"].statement == "DSIC o_star p_star p_star"
    assert TRANSCRIPTION_AMD["SocialChoice.AMD.amd_star_IR"].statement == "IR o_star p_star p_star"
    assert TRANSCRIPTION_AMD["SocialChoice.AMD.amd_star_J"].statement == "J o_star true true = 2"
    assert TRANSCRIPTION_AMD["SocialChoice.AMD.amd_star_J_optimal"].statement == "J o true true ≤ 2"
    assert (
        TRANSCRIPTION_AMD["SocialChoice.AMD.impossibility_strict_payments"].statement
        == "¬ IR o p0 p1"
    )


# ---------------------------------------------------------------------------
# Verrou de transcription : contrôle negatif (le detecteur detecte)
# ---------------------------------------------------------------------------

AMD_FIXTURE = "def o_star (r : Profile) : Bool := r.1 && r.2\ntheorem amd_star_J : J o_star true true = 2 := by\n  simp\n"


def _mutated_source(mutation_old: str, mutation_new: str) -> str:
    source = AMD_LEAN.read_text(encoding="utf-8")
    assert mutation_old in source, f"mutation impossible : {mutation_old!r} absent de AMD.lean"
    return source.replace(mutation_old, mutation_new, 1)


def test_transcription_lock_detects_a_changed_proof_body(tmp_path):
    """Une preuve modifiee sans regeneration produit une derive d'empreinte."""
    mutated = _mutated_source(
        "def p_star (_r : Profile) : ℤ := 0", "def p_star (_r : Profile) : ℤ := 1"
    )
    target = tmp_path / "AMD.lean"
    target.write_text(mutated, encoding="utf-8")
    drifts = check_transcription(target, TRANSCRIPTION_AMD)
    kinds = {drift.kind for drift in drifts}
    assert "empreinte" in kinds
    assert any(d.name == "SocialChoice.AMD.p_star" for d in drifts)
    assert all(d.kind != "module-absent" for d in drifts)


def test_transcription_lock_detects_a_changed_statement(tmp_path):
    """Un enonce change est signale comme `enonce`, pas seulement comme empreinte."""
    mutated = _mutated_source("J o_star true true = 2 := by", "J o_star true true = 3 := by")
    target = tmp_path / "AMD.lean"
    target.write_text(mutated, encoding="utf-8")
    drifts = check_transcription(target, TRANSCRIPTION_AMD)
    kinds = {d.kind for d in drifts}
    assert {"empreinte", "enonce"} <= kinds
    hit = [d for d in drifts if d.name == "SocialChoice.AMD.amd_star_J"]
    assert hit, "le theoreme dont l'enonce a change doit etre nomme"


def test_transcription_lock_detects_a_renamed_declaration(tmp_path):
    """Une declaration renommee est `declaration-absente`, pas une derive muette."""
    mutated = _mutated_source("def o_star (r : Profile)", "def oStar (r : Profile)")
    target = tmp_path / "AMD.lean"
    target.write_text(mutated, encoding="utf-8")
    drifts = check_transcription(target, TRANSCRIPTION_AMD)
    assert any(
        d.kind == "declaration-absente" and d.name == "SocialChoice.AMD.o_star" for d in drifts
    )


def test_transcription_lock_accepts_the_unmutated_source(tmp_path):
    """Controle positif : recopier la source a l'identique ne produit aucune derive."""
    target = tmp_path / "AMD.lean"
    target.write_text(AMD_LEAN.read_text(encoding="utf-8"), encoding="utf-8")
    assert check_transcription(target, TRANSCRIPTION_AMD) == ()


def test_absent_module_is_declared_not_silently_green(tmp_path):
    """Un module absent rend un unique `module-absent` : un etat, pas un succes."""
    drifts = check_transcription(tmp_path / "Absent.lean", TRANSCRIPTION_GROVES)
    assert len(drifts) == 1
    assert drifts[0].kind == "module-absent"


def test_dump_transcription_is_reproducible():
    """La regeneration depuis la source redonne exactement la transcription engagee."""
    rebuilt = build_transcription(AMD_LEAN, TRANSCRIPTION_TARGETS_AMD)
    assert rebuilt == dict(TRANSCRIPTION_AMD)
    dumped = dump_transcription("AMD")
    for name in TRANSCRIPTION_TARGETS_AMD:
        assert f'"{name}"' in dumped
        assert TRANSCRIPTION_AMD[name].digest in dumped


def test_transcription_of_a_fixture_round_trips(tmp_path):
    """Le meme mecanisme, sur une source synthetique : extraction -> transcription -> verrou."""
    target = tmp_path / "Fixture.lean"
    target.write_text(AMD_FIXTURE, encoding="utf-8")
    transcription = build_transcription(
        target, ("o_star", "amd_star_J")
    )
    assert check_transcription(target, transcription) == ()
    target.write_text(AMD_FIXTURE.replace("= 2", "= 3"), encoding="utf-8")
    assert check_transcription(target, transcription), "la mutation doit etre vue"


def test_groves_transcription_matches_when_the_module_lands():
    """`Groves.lean` n'est pas encore sur `main` (PR #22686).

    Tant qu'il est absent, ce test se declare NON APPLICABLE — il ne passe pas
    au vert par defaut. Des que le fichier arrive, la comparaison s'applique et
    une divergence fait echouer la suite.
    """
    drifts = check_transcription(GROVES_LEAN, TRANSCRIPTION_GROVES)
    if len(drifts) == 1 and drifts[0].kind == "module-absent":
        pytest.skip(
            "Groves.lean absent de l'arbre (PR #22686 ouverte) — transcription non applicable"
        )
    assert drifts == (), "\n".join(str(d) for d in drifts)


# ---------------------------------------------------------------------------
# Reproduction des utilites d'AMD.lean (critere 6)
# ---------------------------------------------------------------------------


def test_theta_and_issue_values_match_the_lean_definitions():
    """`thetaVal` et `issueVal` valent 1 sur T et 0 sur F, dans les deux sens."""
    assert (theta_val(False), theta_val(True)) == (0, 1)
    assert (issue_val(False), issue_val(True)) == (0, 1)


def test_lean_utilities_match_the_independent_verifier():
    """`u0`/`u1` de `AMD.lean` et `verify_utility` coincident sur tout le domaine.

    Deux ecritures independantes de la meme utilite : la traduction litterale du
    Lean et le verificateur de `amd_synthesis`. Un ecart signalerait une erreur
    de convention, pas un desaccord de theorie.
    """
    domain = amd_domain()
    mechanism = amd_star_mechanism(domain)
    for true_type in (False, True):
        for profile in itertools.product((False, True), repeat=2):
            int_profile = to_int_profile(profile)
            assert lean_u0(o_star, p_star, true_type, profile) == verify_utility(
                domain, mechanism, 0, int(true_type), int_profile
            )
            assert lean_u1(o_star, p_star, true_type, profile) == verify_utility(
                domain, mechanism, 1, int(true_type), int_profile
            )


def test_lean_utilities_match_with_non_zero_payments():
    """La coincidence tient aussi hors du temoin : paiements arbitraires, verificateur inchange."""
    domain = amd_domain(payment_bounds=(0, 2))
    star = amd_star_mechanism(domain)
    payments = tuple((r % 3, (r + 1) % 3) for r in range(len(domain.profiles)))
    mechanism = Mechanism(allocation=star.allocation, payments=payments)

    def p0(profile: tuple[bool, bool]) -> int:
        return payments[domain.profiles.index(to_int_profile(profile))][0]

    def p1(profile: tuple[bool, bool]) -> int:
        return payments[domain.profiles.index(to_int_profile(profile))][1]

    for true_type in (False, True):
        for profile in itertools.product((False, True), repeat=2):
            int_profile = to_int_profile(profile)
            assert lean_u0(o_star, p0, true_type, profile) == verify_utility(
                domain, mechanism, 0, int(true_type), int_profile
            )
            assert lean_u1(o_star, p1, true_type, profile) == verify_utility(
                domain, mechanism, 1, int(true_type), int_profile
            )


def test_amd_witness_j_and_optimality_are_measured():
    """`amd_star_J` et `amd_star_J_optimal` : J = 2, et 2 est le maximum atteignable."""
    domain = amd_domain()
    star = amd_star_mechanism(domain)
    r = domain.profiles.index((1, 1))
    point = sum(domain.values[a][1][star.allocation[r]] for a in range(2))
    assert point == 2
    best = max(
        sum(domain.values[a][1][allocation[r]] for a in range(2))
        for allocation in itertools.product(range(2), repeat=len(domain.profiles))
    )
    assert best == 2


# ---------------------------------------------------------------------------
# Fixture exhaustive : le verificateur contre une condition derivee a la main
# ---------------------------------------------------------------------------


def test_dsic_of_the_16_zero_pay_mechanisms_matches_a_hand_derived_predicate():
    """Sur les 16 allocations a paiements nuls, DSIC est une condition de monotonie.

    A paiements nuls, l'utilite vaut `type * issue`. DSIC ancre au report sincere
    se reduit donc a : pour chaque agent, l'issue obtenue en rapportant `1` est au
    moins celle obtenue en rapportant `0`, l'autre agent restant sincere. Ecrit
    sur la table `a[profil]` avec les profils dans l'ordre (0,0), (0,1), (1,0), (1,1) :

        a[0,1] >= a[0,0] ; a[1,1] >= a[1,0] ; a[1,1] >= a[0,1] ; a[1,0] >= a[0,0]

    Le predicat est ecrit a la main ici ; l'oracle est `verify_dsic_sincere_anchored`.
    Les deux doivent selectionner EXACTEMENT le meme ensemble de mecanismes.
    """
    domain = amd_domain()
    profiles = domain.profiles
    oracle: set[tuple[int, ...]] = set()
    derived: set[tuple[int, ...]] = set()
    for allocation in itertools.product(range(2), repeat=len(profiles)):
        mechanism = Mechanism(
            allocation=allocation,
            payments=tuple((0, 0) for _ in profiles),
        )
        if not verify_dsic_sincere_anchored(domain, mechanism):
            oracle.add(allocation)
        a00, a01, a10, a11 = allocation
        if a01 >= a00 and a11 >= a10 and a11 >= a01 and a10 >= a00:
            derived.add(allocation)
    assert oracle == derived
    assert len(oracle) == 6


def test_zero_payments_are_always_ir_on_the_amd_domain():
    """`IR` avec paiements nuls se reduit a `type * issue >= 0` : les 16 tiennent."""
    domain = amd_domain()
    profiles = domain.profiles
    for allocation in itertools.product(range(2), repeat=len(profiles)):
        mechanism = Mechanism(allocation=allocation, payments=tuple((0, 0) for _ in profiles))
        assert verify_ir_sincere(domain, mechanism) == ()


# ---------------------------------------------------------------------------
# Instances du pont
# ---------------------------------------------------------------------------


def test_all_bridge_instances_conform_to_their_formal_statements():
    """Les quatre instances rendent le verdict de l'enonce qu'elles citent."""
    ensure_conforms(*all_instances())


def test_every_instance_cites_transcribed_theorems():
    """Une instance ne peut citer qu'un enonce present dans la transcription."""
    known = set(TRANSCRIPTION_AMD) | set(TRANSCRIPTION_GROVES)
    for instance in all_instances():
        assert instance.theorems, instance.name
        missing = [name for name in instance.theorems if name not in known]
        assert not missing, f"{instance.name} cite des enonces non transcrits : {missing}"


def test_every_instance_states_what_the_proof_does_not_certify():
    """Le critere 6 exige une limite explicite, pas une precaution de style."""
    for instance in all_instances():
        text = instance.not_certified
        assert len(text) > 40, f"{instance.name} : limite trop courte"
        assert "solveur" in text.lower(), f"{instance.name} : la limite doit nommer le solveur"
        assert any(
            marker in text for marker in ("ne certifie", "ne certifient", "ne prouve pas")
        ), f"{instance.name} : la limite doit etre negative"


def test_bridge_mismatch_is_raised_on_a_contradiction():
    """Une instance dont le verdict contredit l'enonce est refusee, et le point est nomme."""
    instance = bad_alloc_instance()
    contradictory = replace(
        instance,
        checks=instance.checks
        + (
            BridgeCheck(
                name="DSIC (enonce volontairement faux)",
                expected="aucune violation",
                measured="1 violation(s)",
            ),
        ),
    )
    assert not contradictory.conforms
    with pytest.raises(BridgeMismatch) as excinfo:
        ensure_conforms(contradictory)
    assert "DSIC (enonce volontairement faux)" in str(excinfo.value)


def test_ensure_conforms_does_not_raise_on_the_honest_instances():
    """Controle negatif du test precedent : sans contradiction, rien n'est leve."""
    ensure_conforms(*(replace(i) for i in all_instances()))


# ---------------------------------------------------------------------------
# Temoin AMD et impossibilite
# ---------------------------------------------------------------------------


def test_amd_witness_is_dsic_ir_and_point_welfare_two():
    """Le temoin `o_star` / paiements nuls passe le verificateur, J vaut 2 au profil (1, 1)."""
    domain = amd_domain()
    mechanism = amd_star_mechanism(domain)
    report = verify(domain, mechanism)
    assert report.ok, report.summary()
    assert report.welfare == 2  # le temoin ET ne contribue qu'en (1, 1)


def test_impossibility_instance_is_infeasible_and_empty_by_enumeration():
    """Deux mesures independantes du theoreme : CP-SAT et l'enumeration exhaustive."""
    instance = {i.name: i for i in all_instances()}["amd_impossibility_strict_payments"]
    assert instance.conforms
    result = synthesize(amd_domain(payment_bounds=(1, 4)), payments_at_least=1)
    assert result.status == "INFEASIBLE"
    assert result.mechanism is None


# ---------------------------------------------------------------------------
# Pivot de Clarke : table calculee a la main
# ---------------------------------------------------------------------------


def test_clarke_allocations_and_payments_match_the_hand_computed_table():
    """La table du pivot, calculee a la main, est celle que construit le pont.

    Profils dans l'ordre (0,0), (0,1), (1,0), (1,1). Valeurs :
    agent 0 : type 0 -> (0, 1), type 1 -> (0, 3) ; agent 1 : type 0 -> (2, 0),
    type 1 -> (1, 0). `aStar` maximise la somme, departage par le plus petit
    indice. Le paiement de Clarke est `max_a othersWelfare - othersWelfare(aStar)`.
    """
    domain = clarke_domain()
    mechanism = clarke_mechanism(domain)
    assert [(p, mechanism.allocation[r]) for r, p in enumerate(domain.profiles)] == [
        ((0, 0), 0),
        ((0, 1), 0),
        ((1, 0), 1),
        ((1, 1), 1),
    ]
    assert list(mechanism.payments) == [(0, 1), (0, 1), (2, 0), (1, 0)]


def test_clarke_pivot_is_dsic_ir_and_not_degenerate():
    """DSIC et IR tiennent, et au moins un agent paie un pivot strictement positif."""
    domain = clarke_domain()
    mechanism = clarke_mechanism(domain)
    report = verify(domain, mechanism)
    assert report.ok, report.summary()
    assert max(p for row in mechanism.payments for p in row) == 2


def test_clarke_payments_are_the_negated_groves_transfers():
    """`payment = -grovesPayment` est verifie sur toute la table, pas sur un exemple."""
    domain = clarke_domain()
    mechanism = clarke_mechanism(domain)
    values = domain.values
    a_star = welfare_maximiser(values, domain.n_outcomes)
    g = clarke_g(values)
    for r, profile in enumerate(domain.profiles):
        for agent in range(domain.n_agents):
            assert mechanism.payments[r][agent] == -groves_payment(values, a_star, g, profile, agent)


def test_groves_payoff_equals_the_verifier_utility_under_the_sign_flip():
    """L'identite qui fait le pont : `v + transfert` (Lean) = `v - paiement` (verificateur)."""
    domain = clarke_domain()
    mechanism = clarke_mechanism(domain)
    values = domain.values
    a_star = welfare_maximiser(values, domain.n_outcomes)
    g = clarke_g(values)
    for profile in domain.profiles:
        for agent in range(domain.n_agents):
            for true_type in range(domain.n_types):
                assert verify_utility(domain, mechanism, agent, true_type, profile) == groves_payoff(
                    values, a_star, g, agent, true_type, profile
                )


def test_welfare_helper_matches_the_domain():
    """`groves_welfare` et `groves_others_welfare` se scindent comme dans `Groves.lean`."""
    domain = clarke_domain()
    for profile in domain.profiles:
        for outcome in range(domain.n_outcomes):
            total = groves_welfare(domain.values, profile, outcome)
            for agent in range(domain.n_agents):
                others = groves_others_welfare(domain.values, profile, outcome, agent)
                own = domain.values[agent][profile[agent]][outcome]
                assert others + own == total


# ---------------------------------------------------------------------------
# Temoin negatif `badAlloc_violates_DSIC`
# ---------------------------------------------------------------------------


def test_bad_alloc_reproduces_the_exact_numbers_of_the_lean_proof():
    """Sincere 0 et deviation 2, agent 0 au profil (T, T) — les nombres de `Groves.lean`.

    La preuve Lean obtient ces deux valeurs par `simp` sur `payoff` ; le pont les
    obtient par le verificateur independant de `amd_synthesis`. Deux chemins de
    calcul distincts, memes nombres.
    """
    domain = bad_alloc_domain()
    violations = verify_dsic_sincere_anchored(domain, bad_alloc_mechanism())
    hits = [v for v in violations if (v.agent, v.profile, v.deviation) == (0, (1, 1), 0)]
    assert len(hits) == 1
    assert (hits[0].sincere_utility, hits[0].deviating_utility) == (0, 2)


def test_bad_alloc_is_ir_so_the_witness_isolates_dsic():
    """Le temoin ne viole que DSIC : IR tient, donc l'echec n'est pas un artefact."""
    assert verify_ir_sincere(bad_alloc_domain(), bad_alloc_mechanism()) == ()


def test_the_efficient_allocation_with_the_same_transfers_is_dsic():
    """Controle : ce n'est pas la forme de Groves qui casse, c'est l'allocation.

    Memes valorisations, memes transferts ; seule l'allocation passe de `badAlloc`
    au maximiseur de bien-etre. DSIC revient — donc l'echec est bien impute a
    l'hypothese `hStar` retiree, comme le dit `badAlloc_not_efficient`.
    """
    domain = bad_alloc_domain()
    a_star = welfare_maximiser(domain.values, domain.n_outcomes)
    payments = payments_from_groves(
        domain.values, a_star, lambda _agent, _reported: 0, domain.profiles
    )
    efficient = Mechanism(
        allocation=tuple(a_star(profile) for profile in domain.profiles),
        payments=payments,
    )
    assert verify_dsic_sincere_anchored(domain, efficient) == ()
    assert verify_ir_sincere(domain, efficient) == ()


# ---------------------------------------------------------------------------
# La convention de signe est necessaire (mesure, pas affirmation)
# ---------------------------------------------------------------------------


def test_the_naive_sign_loses_the_numbers_of_the_witness():
    """Sous le signe naif (`paiement = +transfert`), les nombres de la preuve disparaissent.

    C'est ce qui prouve que l'inversion de signe du pont n'est pas cosmetique.
    Le signe naif ne rend pas le mecanisme admissible — il produit d'autres
    violations, a d'autres profils, avec d'autres valeurs. Ce qui est mesure
    ici, c'est plus precisement : la violation nommee par `Groves.lean`
    (« agent 0, profil (T, T), deviation vers F, 0 -> 2 ») n'existe que sous la
    convention du fichier. Une traduction qui se tromperait de signe decrirait
    donc un autre temoin que celui de la preuve.
    """
    domain = bad_alloc_domain()
    profiles = domain.profiles
    a_star = lambda reported: 0 if reported[0] else 1  # noqa: E731 — badAlloc
    naive_payments = tuple(
        tuple(groves_payment(domain.values, a_star, lambda _a, _r: 0, profile, agent)
              for agent in range(domain.n_agents))
        for profile in profiles
    )
    naive = Mechanism(
        allocation=tuple(a_star(profile) for profile in profiles),
        payments=naive_payments,
    )

    def witness_triple(mechanism: Mechanism) -> list[tuple[int, tuple[int, ...], int | None, int, int]]:
        return [
            (v.agent, v.profile, v.deviation, v.sincere_utility, v.deviating_utility)
            for v in verify_dsic_sincere_anchored(domain, mechanism)
        ]

    correct = witness_triple(bad_alloc_mechanism())
    naive_triples = witness_triple(naive)

    assert (0, (1, 1), 0, 0, 2) in correct
    assert (0, (1, 1), 0, 0, 2) not in naive_triples
    assert naive_triples, "le signe naif ne rend pas le mecanisme admissible pour autant"
    assert set(naive_triples) != set(correct)


def test_bad_alloc_values_are_the_lean_ones():
    """`val i t a = 1 si t ET a` : la table du temoin, verifiee cellule par cellule."""
    for agent in range(2):
        for true_type in range(2):
            for outcome in range(2):
                expected = 1 if (true_type and outcome) else 0
                assert BAD_ALLOC_VALUES[agent][true_type][outcome] == expected
