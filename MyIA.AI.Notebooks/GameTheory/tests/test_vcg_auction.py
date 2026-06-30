"""
Tests pour le module VCG (Vickrey-Clarke-Graves) — `examples/vcg_auction.py`.

Le module implement deux mecanismes d'enchere :
  - second_price_auction        : enchere de Vickrey (un seul item, 2e prix)
  - vcg_combinatorial_auction   : VCG combinatoire (plusieurs items avec
                                  complementarites, paiement = externalite de Clarke)

Ces tests assertent les **theoremes fondateurs du VCG**, pas seulement
l'absence de crash. Chaque propriete est verifiee sur des cas a resultat
CONNUS (calcules a la main) ET par recoupement independant (brute-force) :

  - **Veracite (truthfulness)**       : annoncer sa vraie valeur est faiblement
                                        dominant (Vickrey single-item).
  - **Efficacite (efficiency)**       : l'allocation maximise le bien-etre
                                        social (recoupement brute-force).
  - **Rationalite individuelle (IR)** : utilite >= 0 pour tout encherisseur.
  - **Paiement de Clarke**            : payment_i = (bien-etre des autres sans i)
                                        - (bien-etre des autres avec i dans
                                        l'allocation efficace). Recoupement
                                        independant via brute-force.
  - **Perdants paient 0**             : encherisseur sans lot -> payment 0.
  - **Pas de subvention**             : paiements >= 0 (pas de transfert vers
                                        les encherisseurs).

References : Vickrey 1961, Clarke 1971, Groves 1973.

Run with: pytest tests/test_vcg_auction.py -v
"""

import sys
from itertools import combinations, chain
from pathlib import Path

import numpy as np
import pytest

# Ajoute GameTheory/ au path pour importer le package examples.
sys.path.insert(0, str(Path(__file__).parent.parent))

from examples.vcg_auction import (  # noqa: E402
    second_price_auction,
    vcg_combinatorial_auction,
    demonstrate_truthfulness,
    combinatorial_example,
    main,
)


# ----------------------------------------------------------------------------
# Helper : brute-force INDEPENDANT du module, pour recouper efficacite +
# paiement de Clarke. On re-implémente l'enumeration des allocations sans
# reutiliser le code sous test -> le test est un vrai controles croise.
# ----------------------------------------------------------------------------

def _powerset(items):
    """Toutes les parties (sous-ensembles) d'une liste d'items."""
    return chain.from_iterable(
        combinations(items, r) for r in range(len(items) + 1)
    )


def brute_force_efficient_welfare(bidders, items, valuations):
    """Bien-etre social maximal sur toutes les allocations (independant).

    Reimplementation de l'enumeration SANS reutiliser le code sous test,
    pour que les tests d'efficacite et de paiement de Clarke soient de
    vrais controles croises.
    """
    best = 0.0

    def allocate(remaining_bidders, remaining_items, welfare):
        nonlocal best
        if not remaining_bidders:
            best = max(best, welfare)
            return
        bidder = remaining_bidders[0]
        rest = remaining_bidders[1:]
        for bundle in _powerset(list(remaining_items)):
            value = valuations.get((bidder, bundle), 0)
            allocate(rest, set(remaining_items) - set(bundle), welfare + value)

    allocate(list(bidders), set(items), 0.0)
    return best


def allocation_welfare(allocation, valuations):
    """Bien-etre d'une allocation donnee."""
    return float(sum(
        valuations.get((b, tuple(sorted(allocation[b]))), 0.0)
        for b in allocation
    ))


# ============================================================================
# second_price_auction : enchere de Vickrey (un seul item).
# ============================================================================

class TestSecondPriceAuction:
    """second_price_auction : le cas special single-item du VCG."""

    def test_empty_bidders(self):
        """Aucun encherisseur -> aucun gagnant, paiement 0."""
        assert second_price_auction([]) == (-1, 0)

    def test_single_bidder_pays_nothing(self):
        """Un seul encherisseur -> gagne et paie 0 (pas de 2e prix)."""
        winner, payment = second_price_auction([100])
        assert winner == 0
        assert payment == 0

    def test_highest_bidder_wins(self):
        winner, _ = second_price_auction([100, 80, 60])
        assert winner == 0

    def test_payment_is_second_highest(self):
        """INARIANT Vickrey : le gagnant paie le 2e prix, pas son propre prix."""
        winner, payment = second_price_auction([100, 80, 60])
        assert winner == 0
        assert payment == 80

    def test_winner_index_tracks_max_anywhere(self):
        """Le gagnant est l'argmax quelle que soit sa position."""
        winner, payment = second_price_auction([60, 100, 80])
        assert winner == 1
        assert payment == 80  # 2e plus haut

    def test_deterministic(self):
        """Meme entree -> meme sortie (reproductibilite)."""
        a = second_price_auction([42, 17, 99, 3])
        b = second_price_auction([42, 17, 99, 3])
        assert a == b


# ============================================================================
# Veracite (truthfulness) : annoncer sa vraie valeur est faiblement dominant
# dans l'enchere de Vickrey. C'est LE theoreme central.
# ============================================================================

class TestTruthfulness:
    """Veracite : bidder 0 ne gagne JAMAIS a devier de sa vraie valeur."""

    def test_truthful_is_weakly_dominant_grid(self):
        """Sur une grille de bids deviants, aucun n'ameliore strictement
        l'utilite du bidder 0 par rapport au bid truthful.

        Theoreme de Vickrey : annoncer sa vraie valeur est faiblement dominant.
        """
        v0, v1, v2 = 100.0, 80.0, 60.0  # vraies valeurs de 0, 1, 2
        # Utilite si 0 enchere truthful (b0 = v0).
        winner_t, payment_t = second_price_auction([v0, v1, v2])
        utility_truthful = (v0 - payment_t) if winner_t == 0 else 0.0

        best_deviant = -1.0
        for b0 in np.linspace(0, 200, 401):  # grille fine 0..200 par pas 0.5
            winner, payment = second_price_auction([b0, v1, v2])
            util = (v0 - payment) if winner == 0 else 0.0
            best_deviant = max(best_deviant, util)

        # Truthful >= tout deviat (faiblement dominant).
        assert utility_truthful >= best_deviant - 1e-9

    def test_overbidding_does_not_help(self):
        """Sur-encherir ne change ni le gain ni le paiement (on gagnait deja)."""
        truthful = second_price_auction([100, 80, 60])
        overbid = second_price_auction([150, 80, 60])
        # Meme gagnant, meme paiement (2e prix), meme utilite.
        assert overbid[0] == truthful[0]
        assert overbid[1] == truthful[1]

    def test_underbidding_can_only_hurt(self):
        """Sous-encherir en dessous du 2e prix fait perdre l'enchere."""
        # 0 vaut 100, sous-encherit a 70 (< 2e prix 80) -> perd.
        winner, payment = second_price_auction([70, 80, 60])
        assert winner != 0  # 0 perd l'enchere

    def test_truthful_winner_utility_nonnegative(self):
        """Rationalite individuelle : le gagnant truthful a une utilite >= 0."""
        winner, payment = second_price_auction([100, 80, 60])
        assert (100 - payment) >= 0


# ============================================================================
# VCG combinatoire : cas canonique Alice/Bob avec externalite (resultat
# calcule a la main, theorie de Clarke).
# ============================================================================

class TestVCGCanonicalCase:
    """Cas Alice/Bob (module example) : complementarite pour Alice.

    Alice : X=5, Y=5, XY=15 (synergie).  Bob : X=7, Y=7, XY=14 (pas de synergie).

    Allocation efficace : Alice prend {X,Y} (bien-etre 15 > 14 > 12).
    Paiement Alice (Clarke) = bien-etre sans Alice (Bob seul = 14)
                              - bien-etre de Bob avec Alice (0) = 14.
    Paiement Bob (perdant) = 0.
    """

    @pytest.fixture(scope="class")
    def alice_bob(self):
        bidders = ["Alice", "Bob"]
        items = ["X", "Y"]
        valuations = {
            ("Alice", ()): 0,
            ("Alice", ("X",)): 5,
            ("Alice", ("Y",)): 5,
            ("Alice", ("X", "Y")): 15,
            ("Bob", ()): 0,
            ("Bob", ("X",)): 7,
            ("Bob", ("Y",)): 7,
            ("Bob", ("X", "Y")): 14,
        }
        allocation, payments = vcg_combinatorial_auction(bidders, items, valuations)
        return allocation, payments, valuations

    def test_efficient_allocation(self, alice_bob):
        """L'allocation efficace donne {X,Y} a Alice (welfare 15, le max)."""
        allocation, _, _ = alice_bob
        assert set(allocation["Alice"]) == {"X", "Y"}
        assert set(allocation["Bob"]) == set()

    def test_alice_payment_is_clarke_externality(self, alice_bob):
        """Alice paie l'externalite qu'elle impose : 14 (Bob seul aurait eu 14)."""
        _, payments, _ = alice_bob
        assert payments["Alice"] == pytest.approx(14)

    def test_loser_pays_zero(self, alice_bob):
        """Bob (pas de lot) paie 0."""
        _, payments, _ = alice_bob
        assert payments["Bob"] == pytest.approx(0)

    def test_individual_rationality(self, alice_bob):
        """IR : utilite >= 0 pour chaque encherisseur."""
        allocation, payments, valuations = alice_bob
        for bidder in ("Alice", "Bob"):
            value = valuations.get((bidder, tuple(sorted(allocation[bidder]))), 0)
            utility = value - payments[bidder]
            assert utility >= -1e-9, f"IR violee pour {bidder}: utilite={utility}"

    def test_alice_utility_is_one(self, alice_bob):
        """Alice : valeur 15 - paiement 14 = utilite 1 (gain positif minimal)."""
        allocation, payments, valuations = alice_bob
        value = valuations[("Alice", tuple(sorted(allocation["Alice"])))]
        assert (value - payments["Alice"]) == pytest.approx(1)

    def test_total_welfare_is_maximal(self, alice_bob):
        allocation, _, valuations = alice_bob
        assert allocation_welfare(allocation, valuations) == pytest.approx(15)

    def test_revenue_equals_alice_payment(self, alice_bob):
        """Revenu total = 14 (Alice) + 0 (Bob)."""
        _, payments, _ = alice_bob
        assert sum(payments.values()) == pytest.approx(14)


# ============================================================================
# Invariants generaux du VCG, verifies par recoupement brute-force sur
# plusieurs instances (pas seulement le cas canonique).
# ============================================================================

# Plusieurs instances avec structures differentes (substituabilite,
# complementarite, asymetrie, nombre d'encherisseurs/items varies).
VCG_CASES = [
    # (id, bidders, items, valuations)
    ("complementarity", ["Alice", "Bob"], ["X", "Y"], {
        ("Alice", ()): 0, ("Alice", ("X",)): 5, ("Alice", ("Y",)): 5,
        ("Alice", ("X", "Y")): 15,
        ("Bob", ()): 0, ("Bob", ("X",)): 7, ("Bob", ("Y",)): 7,
        ("Bob", ("X", "Y")): 14,
    }),
    ("substitutable", ["A", "B"], ["X", "Y"], {
        ("A", ()): 0, ("A", ("X",)): 6, ("A", ("Y",)): 6, ("A", ("X", "Y")): 6,
        ("B", ()): 0, ("B", ("X",)): 4, ("B", ("Y",)): 4, ("B", ("X", "Y")): 4,
    }),
    ("three_bidders_one_item", ["A", "B", "C"], ["Z"], {
        ("A", ()): 0, ("A", ("Z",)): 10,
        ("B", ()): 0, ("B", ("Z",)): 8,
        ("C", ()): 0, ("C", ("Z",)): 5,
    }),
    ("asymmetric_two_items", ["P", "Q"], ["X", "Y"], {
        ("P", ()): 0, ("P", ("X",)): 12, ("P", ("Y",)): 3, ("P", ("X", "Y")): 13,
        ("Q", ()): 0, ("Q", ("X",)): 2, ("Q", ("Y",)): 9, ("Q", ("X", "Y")): 11,
    }),
]


@pytest.mark.parametrize("case_id,bidders,items,valuations", VCG_CASES)
class TestVCGGeneralInvariants:
    """Invariants du VCG recoupes par brute-force independant."""

    def test_efficiency_vs_bruteforce(self, case_id, bidders, items, valuations):
        """L'allocation retournée atteint le bien-etre social maximal."""
        allocation, _ = vcg_combinatorial_auction(bidders, items, valuations)
        achieved = allocation_welfare(allocation, valuations)
        optimal = brute_force_efficient_welfare(bidders, items, valuations)
        assert achieved == pytest.approx(optimal), (
            f"{case_id}: allocation non-efficace (achete={achieved}, optimal={optimal})"
        )

    def test_individual_rationality(self, case_id, bidders, items, valuations):
        """IR : utilite >= 0 pour tout encherisseur."""
        allocation, payments = vcg_combinatorial_auction(bidders, items, valuations)
        for bidder in bidders:
            value = valuations.get((bidder, tuple(sorted(allocation[bidder]))), 0)
            utility = value - payments[bidder]
            assert utility >= -1e-9, (
                f"{case_id}: IR violee pour {bidder} (utilite={utility})"
            )

    def test_payments_nonnegative(self, case_id, bidders, items, valuations):
        """Pas de subvention : tout paiement >= 0 (Clarke pivot, valuations >= 0)."""
        _, payments = vcg_combinatorial_auction(bidders, items, valuations)
        for bidder, p in payments.items():
            assert p >= -1e-9, f"{case_id}: paiement negatif pour {bidder} ({p})"

    def test_loser_pays_zero(self, case_id, bidders, items, valuations):
        """Tout encherisseur qui recoit un lot vide paie 0."""
        allocation, payments = vcg_combinatorial_auction(bidders, items, valuations)
        for bidder in bidders:
            if len(allocation[bidder]) == 0:
                assert payments[bidder] == pytest.approx(0), (
                    f"{case_id}: perdant {bidder} paie {payments[bidder]} != 0"
                )

    def test_clarke_payment_formula(self, case_id, bidders, items, valuations):
        """payment_i = (welfare sans i) - (welfare des autres avec i).

        Recoupement INDEPENDANT : on recalcule le welfare sans i via le
        brute-force, et le welfare des autres dans l'allocation efficace.
        """
        allocation, payments = vcg_combinatorial_auction(bidders, items, valuations)
        for bidder in bidders:
            others = [b for b in bidders if b != bidder]
            welfare_without = brute_force_efficient_welfare(others, items, valuations)
            others_welfare_actual = sum(
                valuations.get((b, tuple(sorted(allocation[b]))), 0)
                for b in others
            )
            expected_payment = welfare_without - others_welfare_actual
            assert payments[bidder] == pytest.approx(expected_payment), (
                f"{case_id}: paiement Clarke errone pour {bidder} "
                f"(actuel={payments[bidder]}, attendu={expected_payment})"
            )


# ============================================================================
# Cas limites et connexions entre les deux mecanismes.
# ============================================================================

class TestVCGEdgeAndConnections:
    def test_single_bidder_single_item_pays_zero(self):
        """1 encherisseur, 1 item -> recoit l'item, paie 0 (pas d'externalite)."""
        allocation, payments = vcg_combinatorial_auction(
            ["A"], ["X"], {("A", ()): 0, ("A", ("X",)): 10}
        )
        assert set(allocation["A"]) == {"X"}
        assert payments["A"] == pytest.approx(0)

    def test_single_item_combinatorial_matches_vickrey(self):
        """VCG combinatoire a 1 item == enchere de Vickrey (2e prix).

        Connexion fondamentale : second_price_auction est le cas special
        single-item de vcg_combinatorial_auction.
        """
        values = {"A": 10, "B": 8, "C": 5}
        valuations = {(b, ()): 0 for b in values}
        valuations.update({(b, ("Z",)): v for b, v in values.items()})
        allocation, payments = vcg_combinatorial_auction(
            list(values.keys()), ["Z"], valuations
        )
        # Vainqueur = argmax des valeurs.
        winner = max(values, key=lambda b: values[b])
        assert set(allocation[winner]) == {"Z"}
        # Paiement = 2e plus haute valeur (recoupement avec second_price_auction).
        _, vickrey_payment = second_price_auction(
            [values["A"], values["B"], values["C"]]
        )
        assert payments[winner] == pytest.approx(vickrey_payment)

    def test_substitutable_split(self):
        """Items substituables (pas de synergie) : split A.un_item + B.lautre = 10."""
        valuations = {
            ("A", ()): 0, ("A", ("X",)): 6, ("A", ("Y",)): 6, ("A", ("X", "Y")): 6,
            ("B", ()): 0, ("B", ("X",)): 4, ("B", ("Y",)): 4, ("B", ("X", "Y")): 4,
        }
        allocation, _ = vcg_combinatorial_auction(["A", "B"], ["X", "Y"], valuations)
        # Max : A prend un item (6) + B prend l'autre (4) = 10 (A tout = 6, B tout = 4).
        assert allocation_welfare(allocation, valuations) == pytest.approx(10)

    def test_payments_bounded_by_value(self):
        """Un encherisseur ne paie jamais plus que la valeur de son lot (IR forte)."""
        valuations = {
            ("A", ()): 0, ("A", ("X",)): 12, ("A", ("Y",)): 3, ("A", ("X", "Y")): 13,
            ("B", ()): 0, ("B", ("X",)): 2, ("B", ("Y",)): 9, ("B", ("X", "Y")): 11,
        }
        allocation, payments = vcg_combinatorial_auction(
            ["A", "B"], ["X", "Y"], valuations
        )
        for bidder in ("A", "B"):
            value = valuations.get((bidder, tuple(sorted(allocation[bidder]))), 0)
            assert payments[bidder] <= value + 1e-9, (
                f"{bidder} paie {payments[bidder]} > valeur {value}"
            )


# ============================================================================
# Fonctions demo : smoke tests (run sans exception).
# ============================================================================

class TestDemosRun:
    """Les fonctions de demonstration tournent sans erreur."""

    def test_demonstrate_truthfulness_runs(self, capsys):
        demonstrate_truthfulness()
        out = capsys.readouterr().out
        assert "Truthfulness" in out or "Truthful" in out

    def test_combinatorial_example_runs(self, capsys):
        combinatorial_example()
        out = capsys.readouterr().out
        assert "VCG" in out

    def test_main_runs(self, capsys):
        main()
        out = capsys.readouterr().out
        assert "VCG Mechanism" in out
