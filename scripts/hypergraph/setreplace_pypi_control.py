"""Controle de correction du paquet PyPI `setreplace` (kovasb/setreplace-py).

Pourquoi ce fichier existe
--------------------------
Le pli 5 de l'Epic Origami-Wolfram (#19742, issue #23093) exige un **verdict
d'outil ecrit** avant toute mesure. La branche « alternative ouverte » se heurte
a un piege : `pip install setreplace` installe une **reimplementation tierce en
Rust**, et non le paquet officiel de Wolfram Research (`maxitg/SetReplace`,
MIT, 252 etoiles). Le resume PyPI annonce « SetReplace-exact » ; un resume n'est
pas une mesure, donc on mesure ici.

Semantique attendue, citee de la source officielle
--------------------------------------------------
`Kernel/SetReplace.m`, docstring de `SetReplace` :

    les elements les plus proches du debut de l'ensemble sont remplaces, et les
    elements de la sortie sont ajoutes a la fin  (traduction de l'anglais)

Trois consequences, qui sont les attendus des cas C8 :
  (a) l'appariement part du debut de la liste ;
  (b) la sortie est ajoutee en fin de liste (la liste est reordonnee) ;
  (c) ce n'est pas un ensemble : deux aretes egales peuvent coexister.

Historique honnete
------------------
La premiere version de ce controle rendait 3/12. Les neuf echecs venaient tous
de valeurs attendues fausses de ma part, pas du paquet : `events` compte des
SUBSTITUTIONS (une arete reecrite par evenement, ce n'est pas une generation),
et la graine {{1,1}} ne porte qu'UN atome, pas deux. Un temoin peut etre le bug.
La version retenue ci-dessous est celle dont les attendus sont rederives a la
main et justifies cas par cas.

Usage :
    python setreplace_pypi_control.py            # imprime, exit 1 si un cas echoue
    python setreplace_pypi_control.py --json out.json
"""
from __future__ import annotations

import argparse
import json
import sys

try:
    import setreplace as sr
except ImportError:
    print("setreplace absent : python -m pip install setreplace==0.2.0", file=sys.stderr)
    raise SystemExit(2)

RULE_INVERT = "{{x1, x2}} -> {{x2, x1}}"
RULE_CHAIN = "{{x1, x2}, {x2, x3}} -> {{x1, x3}}"
RULE_LINE = "{{x1, x2}} -> {{x1, x2}, {x2, y}}"
RULE_FRESH = "{{x1, x2}} -> {{x1, x2}, {x1, y}}"

_CASES: list[dict] = []


def _parse(rule: str):
    return sr.Rule.parse(rule)


def _norm(state) -> list[tuple[int, ...]]:
    return sorted(tuple(int(a) for a in edge) for edge in state)


def _run(state, rule: str, events: int) -> list[tuple[int, ...]]:
    """Etat brut, ordre preserve : la semantique documentee est ordonnee."""
    return [tuple(int(a) for a in e) for e in sr.set_replace(state, [_parse(rule)], events)]


def _atoms(state) -> list[int]:
    return sorted({a for edge in _norm(state) for a in edge})


def check(name: str, passed: bool, expected, obtained, why: str) -> None:
    _CASES.append({"case": name, "ok": bool(passed),
                   "expected": expected, "obtained": obtained, "why": why})
    print(("PASS " if passed else "FAIL ") + name)
    print("   attendu : %r" % (expected,))
    print("   obtenu  : %r" % (obtained,))
    print("   motif   : %s" % why)


def c1_semantique_des_evenements() -> None:
    """`events` = substitutions, pas generations (SetReplaceAll fait cela)."""
    one = _norm(_run([(1, 2), (3, 4)], RULE_INVERT, 1))
    inverted = [e for e in one if e[0] > e[1]]
    check("C1a 1 evenement reecrit UNE arete",
          len(one) == 2 and len(inverted) == 1,
          "2 aretes dont 1 inversee", one, "events = substitutions")

    two = _norm(_run([(1, 2), (3, 4)], RULE_INVERT, 2))
    check("C1b 2 evenements reecrivent les DEUX aretes",
          two == [(2, 1), (4, 3)], [(2, 1), (4, 3)], two, "deux substitutions disjointes")

    allm = _norm(sr.set_replace_all([(1, 2), (3, 4)], [_parse(RULE_INVERT)], 1))
    check("C1c SetReplaceAll = toutes les correspondances d'une generation",
          allm == [(2, 1), (4, 3)], [(2, 1), (4, 3)], allm,
          "confirme que l'ecart avec C1a est bien generations vs evenements")


def c2_appariement_force() -> None:
    """Chaine 1-2-3-4 : seul (1,2)+(2,3) peut s'apparier, (3,4) reste seul."""
    got = _norm(_run([(1, 2), (2, 3), (3, 4)], RULE_CHAIN, 1))
    check("C2 chaine, appariement force", got == [(1, 3), (3, 4)],
          [(1, 3), (3, 4)], got, "appariement unique, donc attendu unique")


def c3_regle_de_la_ligne() -> None:
    """Depuis {{1,1}} : n evenements donnent n+1 aretes et n+1 atomes distincts.

    La graine ne porte qu'un atome (1,1 est une boucle) ; chaque evenement ajoute
    exactement une arete et un atome neuf, donc les deux compteurs valent n+1.
    """
    for n in range(0, 7):
        got = _norm([(1, 1)]) if n == 0 else _norm(_run([(1, 1)], RULE_LINE, n))
        ok = len(got) == n + 1 and len(_atoms(got)) == n + 1
        check("C3 ligne n=%d" % n, ok,
              "%d aretes / %d atomes" % (n + 1, n + 1),
              "%d aretes / %d atomes" % (len(got), len(_atoms(got))),
              "un evenement ajoute une arete et un atome")


def c4_fraicheur() -> None:
    """Deux atomes neufs doivent etre distincts : jamais partages."""
    got = _run([(1, 2), (3, 4)], RULE_FRESH, 2)
    fresh = [a for a in _atoms(got) if a not in (1, 2, 3, 4)]
    check("C4 fraicheur : 2 atomes neufs distincts",
          len(fresh) == 2 and len(set(fresh)) == 2, 2, fresh,
          "deux evenements donnent deux atomes neufs, non confondus")


def c5_complements_api() -> None:
    states = sr.set_replace_list([(1, 1)], [_parse(RULE_LINE)], 4)
    check("C5 set_replace_list rend n+1 etats", len(states) == 5, 5, len(states),
          "l'etat initial compte, donc 0..n")

    fixed = _norm(sr.set_replace_fixed_point([(1, 2), (2, 3), (3, 4)], [_parse(RULE_CHAIN)]))
    check("C6 point fixe converge vers l'arete unique",
          fixed == [(1, 4)], [(1, 4)], fixed, "la chaine se contracte jusqu'a (1,4)")


def c7_determinisme() -> None:
    a = _run([(1, 2), (2, 3), (3, 4), (4, 5)], RULE_CHAIN, 3)
    b = _run([(1, 2), (2, 3), (3, 4), (4, 5)], RULE_CHAIN, 3)
    check("C7 determinisme sur deux executions", a == b, "etats identiques",
          "identiques" if a == b else "DIVERGENTS", "pas d'aleatoire dans le choix")


def c8_semantique_documentee() -> None:
    """Les trois proprietes du docstring officiel (voir en-tete)."""
    got = _run([(1, 2), (3, 4)], RULE_INVERT, 1)
    check("C8a sortie ajoutee en fin de liste", got == [(3, 4), (2, 1)],
          [(3, 4), (2, 1)], got, "l'arete la plus proche du debut part, sa sortie va a la fin")

    got = _run([(1, 2), (2, 1)], RULE_INVERT, 1)
    check("C8b doublons non fondus : ce n'est pas un ensemble",
          got == [(2, 1), (2, 1)], [(2, 1), (2, 1)], got,
          "coherent avec un decalage de liste, pas avec une fusion d'ensemble")

    got = _run([(1, 2), (2, 3), (3, 4)], RULE_CHAIN, 1)
    check("C8c appariement depuis le debut", got == [(3, 4), (1, 3)],
          [(3, 4), (1, 3)], got, "(1,2)+(2,3) consommees, (1,3) ajoutee en fin")

    got = _run([(1, 2), (3, 4)], RULE_INVERT, 2)
    check("C8d deux evenements sur une liste reordonnee", got == [(2, 1), (4, 3)],
          [(2, 1), (4, 3)], got, "apres 1 evenement la liste est [(3,4),(2,1)]")


def main() -> int:
    ap = argparse.ArgumentParser(description="Controle de correction de setreplace (PyPI)")
    ap.add_argument("--json", metavar="PATH", help="ecrit le rapport JSON a ce chemin")
    args = ap.parse_args()

    for fn in (c1_semantique_des_evenements, c2_appariement_force, c3_regle_de_la_ligne,
               c4_fraicheur, c5_complements_api, c7_determinisme, c8_semantique_documentee):
        fn()

    passed = sum(1 for c in _CASES if c["ok"])
    total = len(_CASES)
    print()
    print("RESUME: %d/%d cas PASS" % (passed, total))

    if args.json:
        payload = {
            "package": "setreplace",
            "version": getattr(sr, "__version__", None),
            "origin": "PyPI, reimplementation tierce (github.com/kovasb/setreplace-py)",
            "reference": "maxitg/SetReplace (Wolfram Research, MIT)",
            "passed": passed,
            "total": total,
            "cases": _CASES,
        }
        with open(args.json, "w", encoding="utf-8") as fh:
            json.dump(payload, fh, indent=1, ensure_ascii=False)
            fh.write("\n")
        print("rapport ecrit : %s" % args.json)

    return 0 if passed == total else 1


if __name__ == "__main__":
    raise SystemExit(main())
