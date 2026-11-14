"""Tests de l'oracle P3 quarter-point Cartier-Miller (#19452).

Couverture :

- le cas chiffre du manuscrit (p=97) est reproduit exactement par le code
  vendorié : a_n=79, B_n=33, U_p(n)=43 — valeurs lues dans le PDF archive,
  non derivees du code teste ;
- l'identite (36) tient au point de quart sur des premiers representatifs de
  chaque classe (13 le plus petit applicable, 41, 97 le cas du papier, 449 le
  plus grand applicable du ground truth) ;
- la mutation « (35) sans terme correctif » est refutee : il existe des
  indices ou U_p(L) != 4 B_L, sinon l'instrument ne discriminerait pas ;
- le premier 7 (p = 3 mod 4) n'a pas de point de quart : le compteur eq36
  reste a zero pour lui, sans echec ;
- le script entier sort en code 0 et rend status passed.
"""

from __future__ import annotations

import importlib.util
import sys
from pathlib import Path

_SCRIPT = (
    Path(__file__).resolve().parents[1]
    / "cartier_miller"
    / "verify_quarter_point_identities.py"
)


def _load():
    spec = importlib.util.spec_from_file_location("vq_quarter_point", _SCRIPT)
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


vq = _load()


def test_paper_example_p97_reproduced_exactly():
    res = vq.check_prime(97)
    n = 24
    prefixes = vq.prefix_values(97)
    us = vq.original_values(97)
    assert prefixes[n]["a"] == 79
    assert prefixes[n]["B"] == 33
    assert us[n] == 43
    assert res["failures"] == []


def test_eq36_holds_at_quarter_point_representative_primes():
    # 13 = plus petit applicable ; 41, 97 (cas du papier) ; 449 = plus grand
    # applicable du ground truth (499 = 3 mod 4 n'a pas de point de quart).
    for p in (13, 41, 97, 449):
        h = (p - 1) // 2
        n = (p - 1) // 4
        prefixes = vq.prefix_values(p)
        us = vq.original_values(p)
        lhs = us[n]
        rhs = (4 * prefixes[n]["B"] + 9 * pow(4, -1, p) * prefixes[n]["a"]) % p
        assert lhs == rhs, f"p={p}: U_p({n})={lhs}, attendu {rhs}"
        assert n <= h


def test_mutation_without_correction_is_refuted():
    """U_p(L) != 4 B_L pour au moins un indice : sinon l'instrument est aveugle."""
    found = False
    for p in (13, 29, 97):
        us = vq.original_values(p)
        prefixes = vq.prefix_values(p)
        for L in range(len(us)):
            if us[L] != 4 * prefixes[L]["B"] % p:
                found = True
                break
        if found:
            break
    assert found, "la mutation (35)-sans-correction n'est refutee nulle part"


def test_prime_3_mod_4_has_no_quarter_point_but_no_failure():
    res = vq.check_prime(7)  # 7 = 3 mod 4
    assert res["failures"] == []
    assert res["counters"]["eq36"] == 0
    assert res["counters"]["eq35"] == 4  # h = 3, L in [0,3]


def test_full_run_passes(tmp_path):
    import json

    out = tmp_path / "run.json"
    rc = 0
    import contextlib
    import io

    argv_backup = sys.argv[:]
    try:
        sys.argv = ["verify", "--json-out", str(out), "--quiet"]
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            rc = vq.main()
    finally:
        sys.argv = argv_backup
    assert rc == 0
    report = json.loads(out.read_text(encoding="utf-8"))
    assert report["status"] == "passed"
    assert report["failures_count"] == 0
    assert report["primes_checked"] == 92
    assert report["controls"]["positive_paper_example"]["passed"] is True
    assert report["controls"]["instrument_discriminates"] is True
