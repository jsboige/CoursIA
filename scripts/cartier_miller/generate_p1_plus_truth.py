#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-2.0-or-later
"""
Generate the Python ground-truth reference data for the 92 admissible
primes of the Cartier-Miller P1+ cross-check, and validate against the
upstream ``harvey_validation.json`` counts.

This is the **Python-only** portion of P1+ : it computes the reference
values (a, B, A, C, D, U) per stopping index using the upstream
recurrences (``original_values``, ``prefix_values`` from
``Cartier_Miller_Benchmark/pilot.py`` and ``quarter`` from
``elliptic_prefix.py``) — both vendored inline below under the
upstream GPL-2.0-or-later terms. It does **not** invoke the C++ Harvey
kernel (NTL/Sage absent locally per RÈGLE F, RECOVERABLE-MACHINE
preferred route : myia-po-2027 :CoursIA-2 or myia-ai-01 :CoursIA).

For each of the 92 primes p in [7, 499] :
- Compute ``prefix_values(p)`` and ``original_values(p)`` for all
  L in [0, (p-1)//2].
- Cross-check ``p <= 199`` exact_binomial identity : a == C(2L,L) * 8^-L mod p.
- For p ≡ 1 mod 4 : compute ``quarter(p)`` and assert (a, B, U)
  coherence with prefix_values[(p-1)//4].

Output :
- ``example_results/p1_plus_python_validation.json`` (schema compatible
  with upstream ``harvey_validation.json`` : status / checks / metadata).
- ``example_results/p1_plus_python_truth.csv`` : one row per prime with
  counts of stopping indices, exact_binomial_checks, and
  quarter_cross_checks.

Usage::

    python scripts/cartier_miller/generate_p1_plus_truth.py
    python scripts/cartier_miller/generate_p1_plus_truth.py --verify-counts

Reference : docs/research/cartier-miller-p1-plus-scoping.md §3.
"""


import argparse
import csv
import json
import math
import sys
from datetime import datetime, timezone
from math import isqrt
from pathlib import Path


# ----------------------------- Vendored upstream (verbatim from pin 37a9b72) ---


def is_prime(n: int) -> bool:
    """Deterministic Miller-Rabin (7 bases) for n < 3.3 * 10**24.

    Source : upstream pilot.py is_prime().
    """
    if n < 2:
        return False
    if n < 4:
        return True
    if n % 2 == 0:
        return False
    for p in (3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n == p:
            return True
        if n % p == 0:
            return False
    r, d = 0, n - 1
    while d % 2 == 0:
        r += 1
        d //= 2
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
    """92 primes in [7, 499] (upstream pilot.py:139)."""
    return [p for p in range(7, 500) if is_prime(p)]


def original_values(p: int):
    """The original t_i, U recurrence (upstream pilot.py:41-47)."""
    h = (p - 1) // 2
    t = 1
    U = 0
    values = [0]
    for i in range(h):
        U = (U + (h + 1 + i) * t) % p
        values.append(U)
        t = t * (h + 2 + i) * pow(2 * i + 2, -1, p) % p
    return values


def prefix_values(p: int):
    """The telescoping (a, B, A, C, D) recurrence (upstream pilot.py:49-57)."""
    h = (p - 1) // 2
    a = 1
    B = 0
    D = 1
    values = []
    for L in range(h + 1):
        values.append({"a": a, "B": B, "A": a * D % p, "C": B * D % p, "D": D})
        if L < h:
            B = (B + a) % p
            a = a * (2 * L + 1) * pow(4 * (L + 1), -1, p) % p
            D = D * 4 * (L + 1) % p
    return values


# ---- Vendored from upstream elliptic_prefix.py (verbatim) ------------------


class SplitRoot(Exception):
    def __init__(self, root):
        self.root = root


class Quadratic:
    def __init__(self, p, root=None):
        self.p, self.root = p, root

    def elt(self, a, b=0):
        return ((a + b * self.root) % self.p, 0) if self.root is not None else (a % self.p, b % self.p)

    def add(self, u, v):
        return ((u[0] + v[0]) % self.p, (u[1] + v[1]) % self.p)

    def neg(self, u):
        return (-u[0] % self.p, -u[1] % self.p)

    def sub(self, u, v):
        return self.add(u, self.neg(v))

    def mul(self, u, v):
        return ((u[0] * v[0] + 2 * u[1] * v[1]) % self.p, (u[0] * v[1] + u[1] * v[0]) % self.p)

    def div(self, u, v):
        norm = (v[0] * v[0] - 2 * v[1] * v[1]) % self.p
        if norm == 0:
            if v == (0, 0):
                raise ZeroDivisionError("zero algebra element")
            raise SplitRoot(v[0] * pow(v[1], -1, self.p) % self.p)
        ni = pow(norm, -1, self.p)
        return self.mul(u, (v[0] * ni % self.p, -v[1] * ni % self.p))


class Elliptic:
    def __init__(self, field, a, b):
        self.k, self.a, self.b = field, field.elt(a), field.elt(b)
        self.calls = self.verticals = self.identities = 0

    def add(self, P, Q):
        self.calls += 1
        k = self.k
        if P is None or Q is None:
            self.identities += 1
            return (Q if P is None else P), k.elt(0)
        x, y = P
        u, v = Q
        if x == u:
            if k.add(y, v) == k.elt(0):
                self.verticals += 1
                return None, k.elt(0)
            if y != v:
                k.div(k.elt(1), k.sub(y, v))
                raise AssertionError("incompatible points at the same x")
            slope = k.div(k.add(k.mul(k.elt(3), k.mul(x, x)), self.a), k.mul(k.elt(2), y))
        else:
            slope = k.div(k.sub(v, y), k.sub(u, x))
        X = k.sub(k.sub(k.mul(slope, slope), x), u)
        Y = k.sub(k.mul(slope, k.sub(x, X)), y)
        return (X, Y), slope

    def on_curve(self, P):
        if P is None:
            return True
        x, y = P
        k = self.k
        return k.mul(y, y) == k.add(k.add(k.mul(k.mul(x, x), x), k.mul(self.a, x)), self.b)


def miller_constant(E, P, M, normalize=True):
    assert M > 0 and E.on_curve(P)
    k = E.k
    if normalize and M % k.p == 0:
        raise ValueError("M must be prime to p")
    Q, alpha = None, k.elt(0)
    for j in range(M.bit_length() - 1, -1, -1):
        Q, slope = E.add(Q, Q)
        alpha = k.add(k.add(alpha, alpha), slope)
        if (M >> j) & 1:
            Q, slope = E.add(Q, P)
            alpha = k.add(alpha, slope)
    assert Q is None, "M does not annihilate P"
    assert E.calls <= 2 * M.bit_length()
    return k.div(alpha, k.elt(M)) if normalize else alpha


def legendre2(p):
    return 1 if p % 8 in (1, 7) else -1


def cornacchia_quarter(p, rng=None):
    assert p % 4 == 1
    c, trials = 2, 0
    while True:
        if rng is not None:
            c = rng.randrange(1, p)
        trials += 1
        if pow(c, (p - 1) // 2, p) == p - 1:
            break
        c += 1
    root = pow(c, (p - 1) // 4, p)
    u, v = p, root
    while v * v > p:
        u, v = v, u % v
    w = isqrt(p - v * v)
    assert v * v + w * w == p
    r, s = (v, w) if v % 2 else (w, v)
    if r % 4 != 1:
        r = -r
    return r, s, trials


def _elliptic_e(p, kind, M):
    root = None
    restarts = 0
    while True:
        k = Quadratic(p, root)
        s = k.elt(0, 1)
        if kind == "quarter":
            E = Elliptic(k, 2, 0)
            P = (k.sub(k.elt(2), s), k.sub(k.elt(4), k.mul(k.elt(2), s)))
        else:
            E = Elliptic(k, 0, pow(4, -1, p))
            P = (k.elt(-pow(2, -1, p)), k.mul(s, k.elt(pow(4, -1, p))))
        try:
            A = miller_constant(E, P, M)
            value = k.mul(s, k.sub(k.elt(1), A)) if kind == "quarter" else k.add(k.elt(1), k.mul(s, A))
            assert value[1] == 0, "coefficient did not descend to F_p"
            return value[0], {"M": M, "bits_M": M.bit_length(), "curve_calls": E.calls,
                              "identity_calls": E.identities, "vertical_calls": E.verticals,
                              "split_restarts": restarts}
        except SplitRoot as err:
            assert root is None and err.root * err.root % p == 2
            root = err.root
            restarts += 1


def quarter(p, rng=None, trace=None):
    """Return (B, a, U) at L = (p-1)/4 for p ≡ 1 mod 4.

    Source : upstream elliptic_prefix.py quarter() (verbatim vendored).
    """
    assert p >= 13 and p % 4 == 1
    n = (p - 1) // 4
    if trace is None:
        r, s, trials = cornacchia_quarter(p, rng)
        boundary = 2 * r * pow(pow(8, n, p), -1, p) % p
        trace = boundary if boundary % 2 == 0 else boundary - p
    else:
        boundary = trace % p
        r = s = None
        trials = 0
    assert trace % 2 == 0 and trace * trace <= 4 * p
    chi = legendre2(p)
    M = p + 1 - trace if chi == 1 else (p + 1) ** 2 - trace * trace
    e, info = _elliptic_e(p, "quarter", M)
    B = e * (chi - boundary) % p
    U = (4 * B + 9 * pow(4, -1, p) * boundary) % p
    return {"a": boundary, "B": B, "U": U, "trace": trace, "r": r, "s": s, "root_trials": trials, **info}


# ----------------------------- Main driver ----------------------------------


def generate_truth(primes: list) -> dict:
    """Compute the Python ground-truth reference data per prime.

    Returns a dict with counts and per-prime breakdowns.
    """
    checks = {
        "all_stopping_indices": 0,
        "exact_binomial_checks": 0,
        "miller_cross_checks": 0,
        "quarter_cross_checks": 0,
        "quarter_skipped_p_mod4": 0,
        "primes_all_indices": len(primes),
        "primes_<=199": sum(1 for p in primes if p <= 199),
        "primes_quarter_applicable": sum(1 for p in primes if p % 4 == 1),
        "status": "passed",
    }
    per_prime = []

    for p in primes:
        h = (p - 1) // 2
        prefix = prefix_values(p)
        original = original_values(p)
        refs = {}
        for L, pref in enumerate(prefix):
            ref = {**pref, "U": original[L]}
            refs[L] = ref
        for L in range(h + 1):
            checks["all_stopping_indices"] += 1
        if p <= 199:
            for L, ref in enumerate(prefix):
                a = math.comb(2 * L, L) * pow(pow(8, L, p), -1, p) % p
                if ref["a"] != a:
                    checks["status"] = "FAIL"
                    raise AssertionError(f"exact_binomial mismatch at p={p}, L={L}")
                checks["exact_binomial_checks"] += 1
        if p % 4 == 1 and p >= 13:
            m = quarter(p)
            L = (p - 1) // 4
            ref = refs[L]
            for k in ("a", "B", "U"):
                if m[k] != ref[k]:
                    checks["status"] = "FAIL"
                    raise AssertionError(
                        f"quarter mismatch at p={p}, key={k}, "
                        f"got {m[k]}, expected {ref[k]}"
                    )
            checks["miller_cross_checks"] += 1
            checks["quarter_cross_checks"] += 1
        else:
            checks["quarter_skipped_p_mod4"] += 1
        per_prime.append(
            {
                "p": p,
                "L_max": h,
                "stopping_indices": h + 1,
                "exact_binomial": 1 if p <= 199 else 0,
                "quarter_applicable": 1 if (p % 4 == 1 and p >= 13) else 0,
            }
        )

    return {"checks": checks, "per_prime": per_prime}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument(
        "--out-dir",
        default="example_results",
        help="Output directory for JSON and CSV (default: example_results)",
    )
    parser.add_argument(
        "--verify-counts",
        action="store_true",
        help="Exit 0 iff primary counts match harvey_validation.json (miller_cross_checks differs by design)",
    )
    args = parser.parse_args()

    primes = list_92()
    assert len(primes) == 92, f"expected 92 primes, got {len(primes)}"

    print(f"# primes: {len(primes)} (range(7, 500) ∩ is_prime)")
    result = generate_truth(primes)
    checks = result["checks"]
    print(
        f"# stopping_indices: {checks['all_stopping_indices']}\n"
        f"# exact_binomial_checks: {checks['exact_binomial_checks']}\n"
        f"# miller_cross_checks: {checks['miller_cross_checks']} (subset of upstream 328)\n"
        f"# quarter_cross_checks: {checks['quarter_cross_checks']}\n"
        f"# quarter_skipped_p_mod4: {checks['quarter_skipped_p_mod4']}\n"
        f"# status: {checks['status']}"
    )

    upstream_full = {
        "all_stopping_indices": 10809,
        "exact_binomial_checks": 2130,
        "primes_all_indices": 92,
    }
    upstream_subset_documented_diff = {
        "miller_cross_checks": 328,  # upstream = range(13, 5000) ∩ (p ≡ 1 mod 4); subset = [7, 499] ∩ (p ≡ 1 mod 4)
    }

    diffs = []
    for k, v in upstream_full.items():
        if checks.get(k) != v:
            diffs.append(f"  {k}: expected {v}, got {checks.get(k)}")
    for k, v in upstream_subset_documented_diff.items():
        if checks.get(k) > v:
            diffs.append(
                f"  {k}: SUBSET expected <= {v}, got {checks.get(k)} (upstream spans range(13, 5000))"
            )

    if args.verify_counts:
        if not diffs:
            print("OK: Python ground truth matches upstream counts.")
            return 0
        else:
            print("DIFF:", file=sys.stderr)
            for d in diffs:
                print(d, file=sys.stderr)
            return 1

    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)

    metadata = {
        "utc_started": datetime.now(timezone.utc).isoformat(),
        "platform": "Python-only ground truth (no NTL, no Harvey C++)",
        "python": ".".join(map(str, sys.version_info[:3])),
        "upstream_pin": "37a9b72",
        "upstream_reference": "harvey_validation.json",
        "validation": checks,
        "subset_documented_diff": upstream_subset_documented_diff,
        "diff_vs_upstream": diffs if diffs else "match",
    }
    json_path = out_dir / "p1_plus_python_validation.json"
    json_path.write_text(json.dumps(metadata, indent=2) + "\n")
    print(f"# wrote {json_path}")

    csv_path = out_dir / "p1_plus_python_truth.csv"
    with csv_path.open("w", newline="") as f:
        writer = csv.DictWriter(
            f, fieldnames=["p", "L_max", "stopping_indices", "exact_binomial", "quarter_applicable"]
        )
        writer.writeheader()
        writer.writerows(result["per_prime"])
    print(f"# wrote {csv_path}")

    if diffs:
        print(
            f"# WARNING: Python ground truth DIFFERS from upstream on "
            f"{len(diffs)} field(s); see diff_vs_upstream in JSON.",
            file=sys.stderr,
        )
        return 2

    return 0


if __name__ == "__main__":
    sys.exit(main())