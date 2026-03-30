# -*- coding: utf-8 -*-
"""
VCG Mechanism - Truthful Auction Design
=======================================

Demonstrates the Vickrey-Clarke-Groves (VCG) mechanism.
Related to GameTheory-14-MechanismDesign.ipynb

The VCG mechanism is a generalization of the second-price auction
that achieves:
- Truthfulness (incentive compatibility)
- Efficiency (maximizes social welfare)
"""

import numpy as np
from typing import List, Tuple, Dict


def second_price_auction(bids: List[float]) -> Tuple[int, float]:
    """
    Vickrey (second-price) auction for a single item.

    - Highest bidder wins
    - Winner pays second-highest bid
    - Truthful: bidding your true value is a dominant strategy

    Returns:
        (winner_index, payment)
    """
    n = len(bids)
    if n == 0:
        return -1, 0
    if n == 1:
        return 0, 0  # Single bidder pays nothing

    # Find winner and second-highest bid
    sorted_indices = np.argsort(bids)[::-1]
    winner = sorted_indices[0]
    payment = bids[sorted_indices[1]]

    return winner, payment


def vcg_combinatorial_auction(
    bidders: List[str],
    items: List[str],
    valuations: Dict[Tuple[str, Tuple[str, ...]], float]
) -> Tuple[Dict[str, List[str]], Dict[str, float]]:
    """
    VCG mechanism for combinatorial auction.

    Args:
        bidders: List of bidder names
        items: List of item names
        valuations: Dict mapping (bidder, items_tuple) -> value

    Returns:
        (allocation, payments) where:
        - allocation[bidder] = list of items won
        - payments[bidder] = amount to pay
    """
    from itertools import combinations, chain

    def powerset(items):
        """Generate all subsets of items."""
        return chain.from_iterable(
            combinations(items, r) for r in range(len(items) + 1)
        )

    def get_value(bidder: str, bundle: Tuple[str, ...]) -> float:
        """Get valuation for a bundle."""
        return valuations.get((bidder, bundle), 0)

    def find_efficient_allocation(
        bidders_subset: List[str],
        available_items: List[str]
    ) -> Tuple[Dict[str, Tuple[str, ...]], float]:
        """
        Find allocation maximizing social welfare.
        Uses brute-force for small instances.
        """
        best_allocation = {b: () for b in bidders_subset}
        best_welfare = 0

        # Generate all possible allocations
        item_set = set(available_items)

        def allocate(remaining_bidders: List[str],
                     remaining_items: set,
                     current_allocation: Dict[str, Tuple[str, ...]],
                     current_welfare: float):
            nonlocal best_allocation, best_welfare

            if not remaining_bidders:
                if current_welfare > best_welfare:
                    best_welfare = current_welfare
                    best_allocation = current_allocation.copy()
                return

            bidder = remaining_bidders[0]
            rest_bidders = remaining_bidders[1:]

            # Try all subsets of remaining items for this bidder
            for bundle in powerset(list(remaining_items)):
                bundle_value = get_value(bidder, bundle)
                new_remaining = remaining_items - set(bundle)
                current_allocation[bidder] = bundle
                allocate(rest_bidders, new_remaining,
                        current_allocation, current_welfare + bundle_value)

            current_allocation[bidder] = ()

        allocate(bidders_subset, item_set, {b: () for b in bidders_subset}, 0)
        return best_allocation, best_welfare

    # Step 1: Find efficient allocation with all bidders
    allocation, total_welfare = find_efficient_allocation(bidders, items)

    # Step 2: Calculate VCG payments
    payments = {}

    for bidder in bidders:
        # Welfare without this bidder
        other_bidders = [b for b in bidders if b != bidder]
        _, welfare_without = find_efficient_allocation(other_bidders, items)

        # Welfare of others in the actual allocation
        others_welfare = sum(
            get_value(b, allocation[b])
            for b in other_bidders
        )

        # VCG payment = externality imposed on others
        payments[bidder] = welfare_without - others_welfare

    # Convert tuple bundles to lists for output
    allocation_lists = {b: list(bundle) for b, bundle in allocation.items()}

    return allocation_lists, payments


def demonstrate_truthfulness():
    """Show that VCG is truthful."""
    print("\n--- Truthfulness Demonstration ---")
    print("\nSingle-item Vickrey auction:")

    true_values = [100, 80, 60]
    print(f"True values: {true_values}")

    # Truthful bidding
    winner, payment = second_price_auction(true_values)
    print(f"\nTruthful bidding:")
    print(f"  Winner: Bidder {winner}, Payment: {payment}")
    print(f"  Winner's utility: {true_values[winner] - payment}")

    # What if winner overbids?
    overbid = [150, 80, 60]  # Bidder 0 overbids
    winner2, payment2 = second_price_auction(overbid)
    print(f"\nBidder 0 overbids to 150:")
    print(f"  Winner: Bidder {winner2}, Payment: {payment2}")
    print(f"  Utility unchanged (still wins, same payment)")

    # What if winner underbids?
    underbid = [70, 80, 60]  # Bidder 0 underbids
    winner3, payment3 = second_price_auction(underbid)
    print(f"\nBidder 0 underbids to 70:")
    print(f"  Winner: Bidder {winner3}, Payment: {payment3}")
    print(f"  Bidder 0's utility: 0 (lost the auction)")
    print(f"  Conclusion: Underbidding can only hurt you!")


def combinatorial_example():
    """Run a combinatorial VCG auction example."""
    print("\n--- Combinatorial VCG Auction ---")

    bidders = ["Alice", "Bob"]
    items = ["X", "Y"]

    # Valuations with complementarities
    valuations = {
        ("Alice", ()): 0,
        ("Alice", ("X",)): 5,
        ("Alice", ("Y",)): 5,
        ("Alice", ("X", "Y")): 15,  # Complementary!

        ("Bob", ()): 0,
        ("Bob", ("X",)): 7,
        ("Bob", ("Y",)): 7,
        ("Bob", ("X", "Y")): 14,  # No synergy
    }

    print(f"\nBidders: {bidders}")
    print(f"Items: {items}")
    print("\nValuations:")
    for (bidder, bundle), value in sorted(valuations.items()):
        if bundle:
            print(f"  {bidder} values {set(bundle)}: {value}")

    allocation, payments = vcg_combinatorial_auction(bidders, items, valuations)

    print("\n--- VCG Outcome ---")
    print(f"Allocation:")
    for bidder, bundle in allocation.items():
        value = valuations.get((bidder, tuple(sorted(bundle))), 0)
        print(f"  {bidder} gets {set(bundle) if bundle else 'nothing'}, value = {value}")

    print(f"\nPayments:")
    for bidder, payment in payments.items():
        bundle = allocation[bidder]
        value = valuations.get((bidder, tuple(sorted(bundle))), 0)
        utility = value - payment
        print(f"  {bidder} pays {payment:.2f}, utility = {utility:.2f}")

    total_welfare = sum(
        valuations.get((b, tuple(sorted(allocation[b]))), 0)
        for b in bidders
    )
    total_revenue = sum(payments.values())
    print(f"\nTotal welfare: {total_welfare}")
    print(f"Total revenue: {total_revenue:.2f}")


def main():
    print("=" * 60)
    print("VCG Mechanism - Truthful Auction Design")
    print("=" * 60)

    print("\nVCG Mechanism Properties:")
    print("  1. Truthfulness: Reporting true values is optimal")
    print("  2. Efficiency: Maximizes social welfare")
    print("  3. Individual Rationality: Non-negative utility")
    print("\nVCG Payment = Externality on others")
    print("  = (Welfare of others without you) - (Welfare of others with you)")

    demonstrate_truthfulness()
    combinatorial_example()


if __name__ == "__main__":
    main()
