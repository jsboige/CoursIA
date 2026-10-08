#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-2.0-or-later
"""
List the 92 admissible primes for the Cartier-Miller ground-truth 92
cross-check.

Definition (verbatim from upstream
Cartier_Miller_Benchmark/pilot.py line 139::

    checks['primes_all_indices'] = sum(is_prime(p) for p in range(7, 500))

range(7, 500) iterates 493 values; among them, is_prime() retains 92
primes. This is the count asserted by upstream
``harvey_validation.json`` field ``primes_all_indices: 92``. The lower
bound 7 (rather than 2) and upper bound 500 are a memory sweet-spot for
the validation harness; admissible primes between 7 and 499 inclusive.

Note: this is **distinct** from the range scanned by
``test_independent_point_counts_and_complete_sum`` which iterates
``range(13, 1000, 4)`` (primes ≡ 1 mod 4 only, yielding 79 candidates
in 13..997 — cf. test_validation.py). The 92 of ``primes_all_indices``
are simply *every* prime in [7, 499].

This script re-derives the list independently of any vendored upstream
source: it embeds the deterministic Miller-Rabin primality test used by
``Cartier_Miller_Benchmark/pilot.py`` (7 bases, n < 3.3 * 10**24) and
applies it to the same arithmetic range. No NTL, no Sage.

Usage::

    python scripts/cartier_miller/list_92_primes.py --print
    python scripts/cartier_miller/list_92_primes.py --count
    python scripts/cartier_miller/list_92_primes.py --assert-92

Reference : docs/research/cartier-miller-p1-plus-scoping.md §1.
"""
import argparse
import sys


# Deterministic Miller-Rabin for n < 3.3 * 10**24, mirrors
# upstream pilot.py is_prime().
def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n < 4:
        return True
    if n % 2 == 0:
        return False
    # Trial division by small primes
    small = (3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)
    for p in small:
        if n == p:
            return True
        if n % p == 0:
            return False
    # Write n-1 = 2^r * d with d odd
    r, d = 0, n - 1
    while d % 2 == 0:
        r += 1
        d //= 2
    # 7 deterministic bases cover n < 3.317 * 10**24
    for a in (2, 3, 5, 7, 11, 13, 17):
        if a % n == 0:
            continue
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        for _ in range(r - 1):
            x = (x * x) % n
            if x == n - 1:
                break
        else:
            return False
    return True


def list_92() -> list:
    """Return the 92 primes p in [7, 499] inclusive."""
    return [
        p for p in range(7, 500)
        if is_prime(p)
    ]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--print", action="store_true", help="Print all 92 primes")
    parser.add_argument("--count", action="store_true", help="Print count only")
    parser.add_argument(
        "--assert-92",
        action="store_true",
        help="Exit 0 iff count == 92 (matches upstream harvey_validation.json)",
    )
    args = parser.parse_args()

    primes = list_92()
    count = len(primes)

    if args.count or (not args.print and not args.assert_92):
        print(count)
        return 0
    if args.print:
        print(f"# {count} admissible primes in [7, 499] (per pilot.py:139)")
        for i, p in enumerate(primes, start=1):
            line = f"  {i:3d}. {p:4d} L = {(p - 1) // 4}"
            if i < count:
                print(line)
            else:
                print(line)  # last line same format
        return 0
    if args.assert_92:
        if count == 92:
            print(f"OK: {count} primes match upstream harvey_validation.json.")
            return 0
        else:
            print(f"MISMATCH: expected 92 primes, got {count}.", file=sys.stderr)
            return 1

    return 0


if __name__ == "__main__":
    sys.exit(main())