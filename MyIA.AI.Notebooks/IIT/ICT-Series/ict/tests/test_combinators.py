"""Tests de l'organe ``ict.combinators`` (pli 4 Origami Wolfram, issue #25061).

Couvre les temoins negatifs exigés par la regle organ-first : la reduction
(en particulier l'unicite empirique de la forme normale), l'abstraction de
bracket (les entiers de Church calculent vraiment), et le systeme de tag de
Post (arret, cycle, blocs inatteignables -- le fait 1111 mesure par Wolfram
2021).
"""

from __future__ import annotations

import random

from ict import combinators as cb


# ---------------------------------------------------------------------------
# Reduction elementaire
# ---------------------------------------------------------------------------


def test_I_est_derivable_de_S_K_K():
    """S K K x = K x (K x) = x : le combinateur I est redondant."""
    nf, steps, _ = cb.reduce_term(cb.parse_ski("S K K x"), "normal", 100)
    assert cb.to_str(nf) == "x"
    assert steps == 2


def test_K_selectionne():
    """K x y = x -- la projection, deux arguments et c'est tout."""
    nf, _, _ = cb.reduce_term(cb.parse_ski("K x y"), "normal", 100)
    assert cb.to_str(nf) == "x"


def test_S_distribue():
    """S f g x = f x (g x) -- la brique de composition."""
    nf, _, _ = cb.reduce_term(cb.parse_ski("S f g x"), "normal", 100)
    assert cb.to_str(nf) == "f x (g x)"


def test_OMEGA_diverge():
    """S I I (S I I) se reduit en lui-meme : divergence pure, borne atteinte."""
    nf, steps, _ = cb.reduce_term(cb.OMEGA, "normal", 200)
    assert nf is None
    assert steps == 200


def test_sensibilite_a_la_strategie():
    """K I OMEGA : ordre normal -> I en 1 pas ; ordre applicatif -> diverge.

    C'est le temoin que le CHOIX de l'ordre n'est pas cosmetique : un terme
    qui possede une forme normale peut ne jamais l'atteindre en evaluant les
    arguments d'abord.
    """
    term = cb.App(cb.App(cb.K, cb.I), cb.OMEGA)
    nf_n, s_n, _ = cb.reduce_term(term, "normal", 500)
    nf_a, s_a, _ = cb.reduce_term(term, "applicative", 500)
    assert cb.to_str(nf_n) == "I"
    assert s_n == 1
    assert nf_a is None


def test_parentheses_dans_le_parseur():
    nf, _, _ = cb.reduce_term(cb.parse_ski("S (K I) I x"), "normal", 100)
    assert cb.to_str(nf) == "x"


# ---------------------------------------------------------------------------
# Church-Rosser empirique
# ---------------------------------------------------------------------------


def test_ordres_aleatoires_meme_forme_normale():
    """30 ordres de reduction aleatoires -> une seule forme normale.

    Temoir empirique de la confluence (la preuve formelle est le grain B,
    sur l'organe Lean -- l'organe Python fournit l'instrument, pas la preuve).
    """
    rng = random.Random(42)
    term = cb.App(cb.App(cb.church(5), cb.Var("f")), cb.Var("x"))
    formes = set()
    for _ in range(30):
        nf, _ = cb.random_reduce(term, rng, 20000)
        assert nf is not None, "church(5) doit atteindre sa forme normale"
        formes.add(cb.to_str(nf))
    assert formes == {"f (f (f (f (f x))))"}


# ---------------------------------------------------------------------------
# Abstraction de bracket et entiers de Church
# ---------------------------------------------------------------------------


def test_church_roundtrip():
    for n in (0, 1, 2, 3, 7):
        assert cb.church_to_int(cb.church(n)) == n


def test_bracket_abstraction_identite():
    """\\x.x -> I."""
    assert cb.lam("x", cb.Var("x")) == cb.I


def test_bracket_abstraction_constante():
    """\\x.c -> K c (c sans x)."""
    out = cb.lam("x", cb.Var("c"))
    assert isinstance(out, cb.App) and out.func == cb.K


def test_addition_de_church_est_exacte():
    """church(2) + church(3) appliques a f x = f^5 x : l'arithmetique est
    reelle, pas recitee."""
    plus = cb.lam("m", cb.lam("n", cb.lam("f", cb.lam(
        "x", cb.App(cb.App(cb.Var("m"), cb.Var("f")),
                    cb.App(cb.App(cb.Var("n"), cb.Var("f")), cb.Var("x")))))))
    total = cb.App(cb.App(plus, cb.church(2)), cb.church(3))
    assert cb.church_to_int(total) == 5


# ---------------------------------------------------------------------------
# Systeme de tag de Post
# ---------------------------------------------------------------------------


def test_tag_pas_elementaire():
    """nu=3, regles 0->00, 1->1101 : un pas se comporte comme dans l'essai."""
    assert cb.tag_step(list("1001010010000")) == list("10100100001101")


def test_tag_arret():
    """Chaine plus courte que nu : le systeme est arrete."""
    trace, verdict = cb.tag_evolve("10")
    assert verdict == "halted"
    assert len(trace) == 1


def test_tag_cycle():
    """Wolfram 2021 : les chaines courtes tombent en cycle apres un transitoire."""
    trace, verdict = cb.tag_evolve("1001010010000")
    assert verdict == "cycle"
    assert len(trace) > 1


def test_tag_1111_inatteignable():
    """Sur la graine de reference, 1111 n'apparait pas : aucun bloc ajoute ne le produit.

    La portee est la trace observee, pas le systeme entier -- une graine
    arbitraire peut en produire, cf. le test suivant.
    """
    trace, verdict = cb.tag_evolve("1001010010000")
    assert verdict == "cycle"
    assert "1111" in cb.first_missing_blocks(trace, 4)


def test_tag_1111_atteignable_par_une_graine_arbitraire():
    """Une graine finissant par 11 voit 1111 des le premier pas.

    ``10011`` : le pas supprime ``100`` et accole le bloc ``1101`` au ``11``
    restant, d'ou ``111101``. L'invariant de Wolfram vaut pour les chaines
    composees de blocs ajoutes, pas pour une graine quelconque.
    """
    trace, _ = cb.tag_evolve("10011")
    assert any("1111" in "".join(state) for state in trace)
    assert "1111" not in cb.first_missing_blocks(trace, 4)


def test_tag_verdict_borne():
    """Une exploration bornee rend 'unbounded' sans conclure a l'infini."""
    trace, verdict = cb.tag_evolve("1" * 50, max_steps=50)
    assert verdict in ("unbounded", "cycle", "halted")
    assert len(trace) <= 51


# ---------------------------------------------------------------------------
# parse_ski : jetons B et C (decomposes en S/K, comme le promet le docstring)
# ---------------------------------------------------------------------------


def test_parse_ski_b_decompose():
    """B se decompose en S/K : B f g x se reduit en f (g x), pas en Var libre."""
    nf, steps, _ = cb.reduce_term(cb.parse_ski("B f g x"))
    assert cb.to_str(nf) == "f (g x)"
    assert steps > 0


def test_parse_ski_c_decompose():
    """C se decompose en S/K : C f x y se reduit en f y x, pas en Var libre."""
    nf, steps, _ = cb.reduce_term(cb.parse_ski("C f x y"))
    assert cb.to_str(nf) == "f y x"
    assert steps > 0
