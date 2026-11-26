#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-2.0-or-later
"""
Verifie les identites de la section « Application to the original quarter
point sum » du manuscrit Cartier-Miller (pin d'amont ``37a9b72``), sur les
92 premiers du ground truth P1+, avec les recurrences vendoriées.

Ce que ce script mesure, et ce qu'il ne mesure pas
--------------------------------------------------
Le manuscrit etablit (§7 du PDF archive) quatre enonces articules :

- (32) definitions : ``t_0 = 1``, ``t_{i+1} = t_i (h+2+i)/(2i+2)``,
  ``U_p(L) = sum_{i<L} (h+1+i) t_i``, ``a_i = C(2i,i) 8^-i``,
  ``B_L = sum_{i<L} a_i`` ;
- (33) ``t_i = 2^-i C(h+1+i,i) = (2i+1) C(2i,i) 8^-i = (2i+1) a_i`` ;
- (34) certificat de telescopage
  ``((2i+1)^2 - 8) a_i = -4(i+1)(2i+7) a_{i+1} + 4i(2i+5) a_i`` ;
- (35) ``U_p(L) = 4 B_L - 2L(2L+5) a_L`` ;
- (36) pour ``p = 4n+1 >= 13`` : ``U_p(n) = 4 B_n + (9/4) a_n``,
  avec ``n = (p-1)/4`` le point de quart.

Le script confronte ces enonces a une **execution** : les valeurs ``a_L``,
``B_L`` et ``U_p(L)`` sont produites par les recurrences vendoriées de
``generate_p1_plus_truth.py`` (amont ``pilot.py:41-57``), et chaque enonce
est teste sur **tous** les indices ``L in [0, h]`` et les **92 premiers**.

Portee honnete : ceci etablit que l'execution **exhibe** ces congruences et
que le code les respecte. Ce n'est **pas** une preuve. La preuve formelle
reste le livrable Lean de la brique P3 (voir
``docs/research/cartier-miller-p2-mathlib-survey.md`` §3), pour laquelle ce
script fournit l'**oracle numerique independant** que le P2 nomme.

Ce que P1 ne mesurait pas : la tranche P1+ (``p1_plus_results.md``) compare
deux chemins de calcul de la **meme** quantite (``quarter()`` de
Cornacchia/Miller contre les recurrences telescopantes) au seul indice
``n``. Les enonces (33)-(36) du manuscrit, eux, n'avaient jamais ete
confrontes a une execution.

Controles
---------
Un instrument qui ne peut pas echouer ne mesure rien. Trois controles :

- **Positif** — le cas chiffre du manuscrit : ``p = 97``, ``n = 24``,
  ``B_n = 33``, ``a_n = 79``, ``U_p(n) = 43``. Les quatre valeurs sont
  lues dans le PDF archive, pas recalculees par le meme chemin.
- **Negatifs** — deux mutations doivent echouer : (35) privee de son terme
  correctif ``-2L(2L+5) a_L``, et (33) avec ``(2i+2)`` au lieu de
  ``(2i+1)``. Si une mutation passe, l'instrument ne discrimine pas et le
  script sort en code 2.

Usage::

    python scripts/cartier_miller/verify_quarter_point_identities.py
    python scripts/cartier_miller/verify_quarter_point_identities.py --json-out /tmp/x.json
"""

from __future__ import annotations

import argparse
import json
import sys
from datetime import datetime, timezone
from math import comb
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from generate_p1_plus_truth import list_92, original_values, prefix_values  # noqa: E402

# Cas chiffre du manuscrit (§7, PDF archive, pin 37a9b72) : lu, non recalcule.
PAPER_EXAMPLE = {"p": 97, "n": 24, "a_n": 79, "B_n": 33, "U_p_n": 43}

DEFAULT_JSON_OUT = (
    Path(__file__).resolve().parent / "example_results" / "p3_quarter_point_identities.json"
)


def _fail(failures: list, identity: str, p: int, index, detail: str) -> None:
    """Consigne un echec ; n'en garde que les premiers pour le rapport."""
    if len(failures) < 50:
        failures.append({"identity": identity, "p": p, "index": index, "detail": detail})


def check_prime(p: int) -> dict:
    """Teste les enonces (32)-(36) sur un premier ; rend les compteurs."""
    h = (p - 1) // 2
    us = original_values(p)
    prefixes = prefix_values(p)

    counters = {
        "def_a": 0,
        "eq33": 0,
        "eq34": 0,
        "eq35": 0,
        "eq36": 0,
        "nc35": 0,
        "nc33": 0,
        "counterexample": 0,
    }
    failures: list = []
    negatives: list = []

    # (32) definition independante de a_i : a_i = C(2i,i) 8^-i
    for i in range(h + 1):
        want = comb(2 * i, i) * pow(8, -i, p) % p
        got = prefixes[i]["a"]
        if got != want:
            _fail(failures, "def_a", p, i, f"a_{i}={got} attendu {want}")
        else:
            counters["def_a"] += 1

    # (33) t_i == (2i+1) a_i ; t recalcule independamment de prefix_values
    t = 1
    for i in range(h + 1):
        lhs = t % p
        rhs = (2 * i + 1) * prefixes[i]["a"] % p
        if lhs != rhs:
            _fail(failures, "eq33", p, i, f"t_{i}={lhs} attendu {rhs}")
            negatives.append({"identity": "eq33_mutation", "p": p, "index": i})
        else:
            counters["eq33"] += 1
        # mutation : (2i+2) au lieu de (2i+1) — doit diverger au moins une fois
        if lhs == (2 * i + 2) * prefixes[i]["a"] % p:
            counters["nc33"] += 1
        if i < h:
            t = t * (h + 2 + i) * pow(2 * i + 2, -1, p) % p

    # (34) certificat de telescopage, sur tous les i < h
    for i in range(h):
        lhs = ((2 * i + 1) ** 2 - 8) * prefixes[i]["a"] % p
        rhs = (
            -4 * (i + 1) * (2 * i + 7) * prefixes[i + 1]["a"]
            + 4 * i * (2 * i + 5) * prefixes[i]["a"]
        ) % p
        if lhs != rhs:
            _fail(failures, "eq34", p, i, f"lhs={lhs} rhs={rhs}")
        else:
            counters["eq34"] += 1

    # (35) U_p(L) == 4 B_L - 2L(2L+5) a_L, sur tous les L
    for L in range(h + 1):
        lhs = us[L]
        rhs = (4 * prefixes[L]["B"] - 2 * L * (2 * L + 5) * prefixes[L]["a"]) % p
        if lhs != rhs:
            _fail(failures, "eq35", p, L, f"U_p({L})={lhs} attendu {rhs}")
        else:
            counters["eq35"] += 1
        # mutation : terme correctif retire — doit diverger au moins une fois
        if lhs == 4 * prefixes[L]["B"] % p:
            counters["nc35"] += 1
            negatives.append({"identity": "eq35_mutation", "p": p, "index": L})

    # (36) au point de quart n = (p-1)/4, pour p = 4n+1 >= 13
    if p % 4 == 1 and p >= 13:
        n = (p - 1) // 4
        lhs = us[n]
        rhs = (4 * prefixes[n]["B"] + 9 * pow(4, -1, p) * prefixes[n]["a"]) % p
        if lhs != rhs:
            _fail(failures, "eq36", p, n, f"U_p({n})={lhs} attendu {rhs}")
        else:
            counters["eq36"] += 1
        if p == PAPER_EXAMPLE["p"]:
            ok = (
                prefixes[n]["a"] == PAPER_EXAMPLE["a_n"]
                and prefixes[n]["B"] == PAPER_EXAMPLE["B_n"]
                and us[n] == PAPER_EXAMPLE["U_p_n"]
            )
            if ok:
                counters["counterexample"] += 1
            else:
                _fail(
                    failures,
                    "paper_example",
                    p,
                    n,
                    f"a={prefixes[n]['a']} B={prefixes[n]['B']} U={us[n]}",
                )

    return {
        "p": p,
        "h": h,
        "counters": counters,
        "failures": failures,
        "mutations_detected": len(negatives),
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[1] if __doc__ else "")
    parser.add_argument("--json-out", type=Path, default=DEFAULT_JSON_OUT)
    parser.add_argument("--quiet", action="store_true")
    args = parser.parse_args()

    primes = list_92()
    if len(primes) != 92:
        print(f"ERREUR: {len(primes)} premiers, 92 attendus", file=sys.stderr)
        return 1

    totals = {
        "def_a": 0,
        "eq33": 0,
        "eq34": 0,
        "eq35": 0,
        "eq36": 0,
        "nc35": 0,
        "nc33": 0,
        "counterexample": 0,
    }
    failures: list = []
    mutations = {"eq35_mutation": 0, "eq33_mutation": 0}

    for p in primes:
        res = check_prime(p)
        for key in totals:
            totals[key] += res["counters"][key]
        failures.extend(res["failures"])
        for item in res["failures"]:
            if item["identity"] in mutations:
                mutations[item["identity"]] += 1

    # Une mutation n'est refutee que si elle est FAUSSE au moins une fois ;
    # une mutation qui tiendrait partout signerait un instrument aveugle.
    holds_mutated_eq35 = totals["nc35"]
    holds_mutated_eq33 = totals["nc33"]
    total_eq35 = totals["eq35"]
    total_eq33 = totals["eq33"]

    verdict = {}
    for name, holds, total in (
        ("eq35_without_correction", holds_mutated_eq35, total_eq35),
        ("eq33_with_2i_plus_2", holds_mutated_eq33, total_eq33),
    ):
        # la mutation est refutee si elle est fausse au moins une fois
        verdict[name] = {"holds": holds, "checked": total, "refuted": holds < total}

    instrument_discriminates = all(v["refuted"] for v in verdict.values())

    report = {
        "utc_started": datetime.now(timezone.utc).isoformat(),
        "python": ".".join(map(str, sys.version_info[:3])),
        "upstream_pin": "37a9b72",
        "manuscript": "Cartier-Miller, section 'Application to the original quarter point sum'",
        "primes_checked": len(primes),
        "primes_quarter_applicable": sum(1 for p in primes if p % 4 == 1 and p >= 13),
        "identities": {
            "def_a_binomial": {"checks": totals["def_a"], "statement": "(32) a_i = C(2i,i) 8^-i"},
            "eq33": {"checks": totals["eq33"], "statement": "(33) t_i = (2i+1) a_i"},
            "eq34": {"checks": totals["eq34"], "statement": "(34) certificat de telescopage"},
            "eq35": {"checks": totals["eq35"], "statement": "(35) U_p(L) = 4 B_L - 2L(2L+5) a_L"},
            "eq36": {"checks": totals["eq36"], "statement": "(36) U_p(n) = 4 B_n + (9/4) a_n"},
        },
        "controls": {
            "positive_paper_example": {
                "case": PAPER_EXAMPLE,
                "passed": totals["counterexample"] == 1,
            },
            "negative_mutations": verdict,
            "instrument_discriminates": instrument_discriminates,
        },
        "failures_count": len(failures),
        "failures": failures,
        "status": "passed" if (not failures and instrument_discriminates) else "failed",
        "scope": (
            "Verifie que l'execution exhibe (32)-(36) sur les 92 premiers du "
            "ground truth P1+. Ne prouve pas (35) : la preuve reste la brique "
            "Lean P3. Oracle numerique independant, jamais preuve."
        ),
    }

    args.json_out.parent.mkdir(parents=True, exist_ok=True)
    args.json_out.write_text(json.dumps(report, indent=2, ensure_ascii=True) + "\n")

    if not args.quiet:
        print(f"# primes: {report['primes_checked']} (quarter: {report['primes_quarter_applicable']})")
        for name, data in report["identities"].items():
            print(f"# {name:<16} checks={data['checks']:<6} {data['statement']}")
        print(f"# papier p=97      passed={report['controls']['positive_paper_example']['passed']}")
        for name, data in verdict.items():
            print(f"# mutation {name:<26} refuted={data['refuted']} (tient {data['holds']}/{data['checked']})")
        print(f"# failures: {len(failures)}")
        print(f"# status: {report['status']}")
        print(f"# wrote {args.json_out}")

    if report["status"] != "passed":
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())