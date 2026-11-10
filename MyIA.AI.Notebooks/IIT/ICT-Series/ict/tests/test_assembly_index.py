"""Tests du module :mod:`ict.assembly_index` (case 20, veille #8182).

Le banc pre-enregistre (``docs/ict/assembly-theory-pre-enregistrement.md``)
mesure l'assembly index exact de chaines contre les proxys LZ (zlib, LZ76,
LZ78) -- la revendication d'Abrahao et al. 2024 que les methodes sont
« indistinguishable from each other ». Chaque test verrouille un invariant
falsifiable : valeurs certifiees de l'echelle periodique (``ai = log2 n``
exactement), borne de doublement jamais violee, accord des deux solveurs sur
tout l'espace binaire petit, replays de temoins, definitions LZ sur valeurs
calculees a la main, corpus deterministes, ajustements log-log et Spearman.

Pattern herite de ``test_compression.py`` : bootstrap ``sys.path``
module-level, sans fixtures. Module autonome (stdlib + numpy).
"""

from __future__ import annotations

import itertools
import os
import sys

import pytest

_HERE = os.path.dirname(os.path.abspath(__file__))
_ROOT = os.path.dirname(_HERE)
if _ROOT not in sys.path:
    sys.path.insert(0, _ROOT)

from ict import assembly_index as c  # noqa: E402


# --------------------------------------------------------------------------- #
#  ceil_log2 et valeurs certifiees du solveur exact
# --------------------------------------------------------------------------- #


def test_ceil_log2_powers_and_non_powers():
    """ceil(log2) entier : puissances de deux exactes, non-puissances arrondies
    vers le haut (12 -> 4 car 2^3 = 8 < 12 <= 16 = 2^4)."""
    assert c.ceil_log2(1) == 0
    assert c.ceil_log2(2) == 1
    assert c.ceil_log2(3) == 2
    assert c.ceil_log2(4) == 2
    assert c.ceil_log2(12) == 4
    assert c.ceil_log2(16) == 4
    assert c.ceil_log2(17) == 5


def test_exact_ai_periodic_is_log2_exact():
    """L'echelle periodique est certifiee des deux cotes : la construction de
    doublement atteint log2 n jointures et la borne de doublement exige
    ceil(log2 n) -- le solveur doit rendre exactement cette valeur, y compris
    hors puissances de deux (n=12 : 4, car 0101|0101 -> 01010101 -> x)."""
    assert c.exact_ai("01")["ai"] == 1
    assert c.exact_ai(c.periodic(4))["ai"] == 2
    assert c.exact_ai(c.periodic(8))["ai"] == 3
    assert c.exact_ai(c.periodic(12))["ai"] == 4  # ceil(log2 12) = 4
    assert c.exact_ai(c.periodic(16))["ai"] == 4
    for n in (4, 8, 12, 16, 18, 20):
        got = c.exact_ai(c.periodic(n))["ai"]
        assert got == c.ceil_log2(n), f"n={n}: {got} != {c.ceil_log2(n)}"


def test_exact_ai_two_blocks_and_examples():
    """0^m 1^m (7 jointures pour m=6 et m=8) et les deux exemples du pont :
    ABRACADABRA (7) et BANANA (4) -- valeurs mesurees par les deux solveurs
    en G1, verrouillees ici telles quelles."""
    assert c.exact_ai(c.zero_one_block(6))["ai"] == 7
    assert c.exact_ai(c.zero_one_block(8))["ai"] == 7
    assert c.exact_ai("ABRACADABRA")["ai"] == 7
    assert c.exact_ai("BANANA")["ai"] == 4


def test_doubling_bound_never_violated():
    """Porte G2 : ceil(log2 n) <= ai <= borne gloutonne, sur un echantillon
    structure ET aleatoire (graine fixe, deterministe)."""
    samples = [c.periodic(n) for n in (10, 12, 14, 18)]
    samples += [c.fibonacci_string(j) for j in (5, 6)]
    samples += [c.thue_morse(j) for j in (3, 4)]
    samples += [c.zero_one_block(m) for m in (5, 7)]
    samples += [c.half_ones(12, 6, s) for s in (0, 1, 7)]
    samples += ["ABRACADABRA", "BANANA"]
    for x in samples:
        r = c.exact_ai(x)
        assert r["lb"] <= r["ai"] <= r["ub"], f"{x!r}: {r['lb']} <= {r['ai']} <= {r['ub']}"


def test_reach_exceeded_is_declared_never_silent():
    """Porte G3 : un budget d'etats depasse rend reach_exceeded=True et
    ai=None -- jamais une approximation silencieuse."""
    r = c.exact_ai(c.half_ones(12, 6, 0), state_budget=3)
    assert r["reach_exceeded"] is True
    assert r["ai"] is None


# --------------------------------------------------------------------------- #
#  accord des deux solveurs (porte G1) et replay des temoins
# --------------------------------------------------------------------------- #


def test_solvers_agree_on_all_binary_strings_up_to_7():
    """Toutes les chaines binaires de n <= 7 (254) : le solveur a masques et
    le solveur multiensemble (espace d'etats different) rendent le meme
    assembly index. C'est la porte G1 en miniature."""
    for n in range(1, 8):
        for bits in itertools.product("01", repeat=n):
            s = "".join(bits)
            a = c.exact_ai(s)["ai"]
            b = c.brute_force_ai(s)["ai"]
            assert a == b, f"{s!r}: exact={a} brute={b}"


def test_solvers_agree_on_random_matched_strings():
    """Accord sur 12 chaines aleatoires appariees (n=11 et 12, graines
    fixes) -- la ou la recherche est la plus contrainte."""
    for k in range(6):
        for n in (11, 12):
            s = c.half_ones(n, n // 2, k)
            assert c.exact_ai(s)["ai"] == c.brute_force_ai(s)["ai"], f"n={n} k={k}"


def test_witness_replays_and_corrupted_fails():
    """Le temoin du solveur se rejoue piece par piece (chaque piece = deux
    pieces deja au pool) ; un temoin corrompu est rejete."""
    for x in (c.periodic(12), c.zero_one_block(6), "ABRACADABRA"):
        r = c.exact_ai(x)
        assert r["ai"] == len(r["witness"])
        assert c.validate_witness(x, r["witness"]) is True
    # corrompu : une piece intermediaire manquante
    assert c.validate_witness("01010101", ["01010101"]) is False
    # corrompu : la derniere piece n'est pas x
    assert c.validate_witness("0101", ["01", "10"]) is False


# --------------------------------------------------------------------------- #
#  definitions LZ (valeurs calculees a la main)
# --------------------------------------------------------------------------- #


def test_lz76_hand_computed_parses():
    """LZ76 (phrase = plus longue amorce reproductible + un caractere) :
    0101 -> 0|1|01 (3), 0000 -> 0|00|0 (3), abcd -> a|b|c|d (4),
    abababab -> a|b|aba|bab (4 : 'aba' et 'bab' sont reproductibles)."""
    assert c.lz76_count("0101") == 3
    assert c.lz76_count("0000") == 3
    assert c.lz76_count("abcd") == 4
    assert c.lz76_count("abababab") == 4
    assert c.lz76_count("") == 0
    assert c.lz76_count("a") == 1


def test_lz76_periodic_doubles():
    """Sur (01)^2^j, la phrase courante double a chaque pas (toute amorce est
    reproductible par decalage d'une periode) : compte = j + 1, croissance
    logarithmique -- le regime que la pente H2b mesure."""
    for j in (5, 6, 7, 8):
        assert c.lz76_count(c.periodic(2 ** j)) == j + 1, f"j={j}"


def test_lz78_hand_computed_parses():
    """LZ78 (dictionnaire) : 0101 -> 0|1|01 (3), abcd -> a|b|c|d (4),
    abababab -> a|b|ab|aba|b (5)."""
    assert c.lz78_count("0101") == 3
    assert c.lz78_count("abcd") == 4
    assert c.lz78_count("abababab") == 5
    assert c.lz78_count("") == 0


def test_zlib_periodic_grows_slowly_not_flat():
    """Sur l'echelle periodique (64 -> 16384, un facteur 256 en longueur),
    zlib croit lentement mais PAS a plat : bande basse 12-15 sur n <= 512,
    au plus ~12 octets gagnes par doublement, facteur total < 4x. C'est la
    mesure meme qui falsifie H2a (2/10 lignes non croissantes seulement) :
    le plat « repetition pure = O(1) octets » est faux a cette echelle, la
    longueur zlib suit la meme direction que l'index (log2 n) sans le
    calquer -- d'ou le verdict H2a FALSIFIEE et ce verrou sur la croissance
    lente, pas sur la constance."""
    vals = [c.zlib_len(c.periodic(2 ** j)) for j in range(5, 15)]
    assert max(vals) <= 64, f"zlib periodique hors bande scellee : {vals}"
    assert max(vals) < 4 * min(vals), f"croissance zlib trop rapide : {vals}"
    assert all(b - a <= 12 for a, b in zip(vals, vals[1:])), f"saut zlib : {vals}"
    low = vals[:4]  # j = 5..8 : bande basse mesuree 12-15 octets
    assert max(low) - min(low) <= 4, f"bande basse inattendue : {low}"


def test_zlib_periodic_shorter_than_random():
    """Le signal grossier : le periodique se compresse mieux que l'aleatoire
    de meme longueur (le sens de la correlation positive attendue en H3)."""
    per = c.zlib_len(c.periodic(64))
    rnd = c.zlib_len(c.half_ones(64, 32, 0))
    assert per < rnd


# --------------------------------------------------------------------------- #
#  corpus scelles et statistiques du banc
# --------------------------------------------------------------------------- #


def test_corpus_builders_deterministic_shapes():
    """Fibonacci (f_j = f_{j-1} f_{j-2}, longueurs 1,2,3,5,8,13,21 et
    propriete de prefixe), Thue-Morse (longueurs 2^j, 01101001...), appariement
    a comptes fixes, blocs 0^m 1^m."""
    lens = [len(c.fibonacci_string(j)) for j in range(1, 8)]
    assert lens == [1, 2, 3, 5, 8, 13, 21]
    assert c.fibonacci_string(6).startswith(c.fibonacci_string(5))
    assert len(c.thue_morse(4)) == 16
    assert c.thue_morse(3).startswith("011010")
    for n, ones in ((12, 6), (16, 8)):
        s = c.half_ones(n, ones, 0)
        assert len(s) == n and s.count("1") == ones
    assert c.zero_one_block(4) == "00001111"
    assert c.periodic(5) == "01010"


def test_h1_classes_share_shannon_entropy():
    """Toute la classe a comptes fixes a h0 = 1.000 bit exactement -- c'est
    le point de H1 : meme entropie de Shannon, assembly index differs."""
    for name, members in c.corpus_h1().items():
        assert len(members) == 7, f"{name}: 7 membres scelles"
        for _, x in members:
            assert c.h0(x) == pytest.approx(1.0)


def test_ladders_have_certified_envelopes():
    """P est certifie exact (lb = ub = log2 n) ; F et TM portent une enveloppe
    lb <= ub avec ub de construction par morphisme (j-1 pour f_j, 2j-1 pour
    tau_j, qui entretient aussi le complement)."""
    familles = c.corpus_ladders()
    assert len(familles["P"]) == 10
    assert len(familles["F"]) == 10
    assert len(familles["TM"]) == 10
    for r in familles["P"]:
        assert r["certified"] and r["lb_cert"] == r["ub_cert"]
        assert r["ub_cert"] == c.ceil_log2(len(r["x"]))
    for r in familles["F"]:
        assert r["lb_cert"] <= r["ub_cert"]
    for r in familles["TM"]:
        assert r["lb_cert"] <= r["ub_cert"]


def test_loglog_fit_recovers_power_law_and_constant():
    """La pente log-log retrouve une loi de puissance exacte (pente 2, R2=1)
    et rend pente 0 / R2 1 pour une serie constante (variance nulle :
    l'ajustement est exact, convention declaree pour le zlib constant)."""
    xs = [64, 128, 256, 512, 1024, 2048]
    fit = c.loglog_fit(xs, [x ** 2 for x in xs])
    assert fit["slope"] == pytest.approx(2.0, abs=1e-9)
    assert fit["r2"] == pytest.approx(1.0, abs=1e-9)
    cst = c.loglog_fit(xs, [13.0] * len(xs))
    assert cst["slope"] == pytest.approx(0.0, abs=1e-9)
    assert cst["r2"] == 1.0


def test_spearman_monotone_and_inverse_and_ties():
    """Spearman : +1 en monotone croissant, -1 en inverse, sensible aux ex
    aequo par rangs moyens."""
    assert c.spearman([1, 2, 3, 4], [2, 4, 6, 8]) == pytest.approx(1.0)
    assert c.spearman([1, 2, 3, 4], [8, 6, 4, 2]) == pytest.approx(-1.0)
    rho = c.spearman([1, 1, 2, 3], [1, 1, 2, 3])
    assert rho == pytest.approx(1.0)


def test_battery_smoke_small_config():
    """Le banc s'execute de bout en bout (portes, verdicts, controles) et rend
    les structures scellees ; les verdicts appartiennent a l'enumeration
    fermee du pre-enregistrement."""
    res = c.run_battery(g1=False)
    assert set(res["verdicts"].keys()) == {"H1", "H2a", "H2b", "H3", "global"}
    assert res["gates"]["G2"]["passed"] is True
    allowed = {"CONFIRMÉE", "FALSIFIÉE", "PARTIELLE", "NON_CONCLUSIF_INSTRUMENT"}
    for v in res["verdicts"].values():
        assert v in allowed or v in {"CONFIRMÉ", "PARTIEL", "FALSIFIÉ"}
    assert len(res["controls"]["permutations"]) == 10
    assert res["controls"]["pont"][0]["label"] == "ABRACADABRA"
