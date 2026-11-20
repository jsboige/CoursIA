"""Oracle des paquets : vote à la carte contre vote sur paquets.

Un profil associe à chaque issue (ensemble de mesures adoptées) un vecteur de gains,
un par agent. Les premiers agents votent ; les suivants (non-votants) ne votent pas
et sont seulement comptés par l'oracle. Cinq profils construits pour l'enseignement
servent de référence :

    P1   compromis : chaque mesure rapporte 5 à une cohorte et coûte 1 aux deux autres ;
    P1B  le même, où chaque mesure adoptée est payée 3 par un non-votant ;
    T    témoin, transferts purs : aucun paquet n'améliore chacun ;
    E    extraction à deux contre un ;
    P2   dépense D et financement F non séparables, affichés sur des comptes disjoints.

Trois procédures sont comparées : vote mesure par mesure sincère, le même avec des
votants qui anticipent la suite, et vote sur un paquet contre le statu quo.

Usage, depuis la racine du dépôt :

    python -X utf8 MyIA.AI.Notebooks/GameTheory/examples/oracle_paquets.py

Les libellés affichés sont en ASCII pour rester lisibles dans toute console.
"""
from __future__ import annotations

from itertools import combinations

Issue = frozenset[str]
Gains = tuple[int, ...]
Profil = dict[Issue, Gains]

STATU_QUO: Issue = frozenset()


def issues(mesures: list[str]) -> list[Issue]:
    """Toutes les issues : chaque sous-ensemble de mesures adoptées, statu quo compris."""
    return [frozenset(c) for r in range(len(mesures) + 1) for c in combinations(mesures, r)]


def nom(issue: Issue) -> str:
    """Nom lisible d'une issue : « A+B », ou « statu quo » si aucune mesure n'est adoptée."""
    return "+".join(sorted(issue)) if issue else "statu quo"


def additif(gains: dict[str, Gains]) -> Profil:
    """Profil à gains additifs : le gain d'une issue est la somme des gains de ses mesures."""
    n = len(next(iter(gains.values())))
    return {
        s: tuple(sum(gains[m][i] for m in s) for i in range(n))
        for s in issues(sorted(gains))
    }


def domine(x: Gains, y: Gains, agents: list[int]) -> bool:
    """x domine y au sens de Pareto sur les agents donnés."""
    return all(x[i] >= y[i] for i in agents) and any(x[i] > y[i] for i in agents)


def pareto(profil: Profil, agents: list[int]) -> list[Issue]:
    """Issues qu'aucune autre ne domine sur les agents donnés."""
    return [
        s for s in profil
        if not any(domine(profil[t], profil[s], agents) for t in profil if t != s)
    ]


def majorite(x: Gains, y: Gains, votants: list[int]) -> int:
    """Strictement positif si x bat y à la majorité des votants non indifférents."""
    pour = sum(1 for i in votants if x[i] > y[i])
    contre = sum(1 for i in votants if x[i] < y[i])
    return pour - contre


def carte_sincere(
    profil: Profil,
    ordre: list[str],
    votants: list[int],
    affiche: dict[str, Gains] | None = None,
) -> Issue:
    """Vote mesure par mesure : chaque votant compare l'état courant avec et sans la mesure.

    affiche : gains marginaux AFFICHÉS par mesure (comptabilité disjointe) ;
    None = le votant lit le vrai gain consolidé.
    """
    etat: Issue = STATU_QUO
    for m in ordre:
        avec = etat | {m}
        if affiche is None:
            score = majorite(profil[avec], profil[etat], votants)
        else:
            zero = tuple(0 for _ in affiche[m])
            score = majorite(affiche[m], zero, votants)
        if score > 0:
            etat = avec
    return etat


def carte_sophistiquee(profil: Profil, ordre: list[str], votants: list[int]) -> Issue:
    """Même procédure, avec des votants qui anticipent la suite (induction à rebours)."""

    def finale(etat: Issue, k: int) -> Issue:
        if k == len(ordre):
            return etat
        oui = finale(etat | {ordre[k]}, k + 1)
        non = finale(etat, k + 1)
        return oui if majorite(profil[oui], profil[non], votants) > 0 else non

    return finale(STATU_QUO, 0)


def battent_le_statu_quo(profil: Profil, votants: list[int]) -> list[Issue]:
    """Paquets qui battent le statu quo à la majorité des votants."""
    return [s for s in profil if s and majorite(profil[s], profil[STATU_QUO], votants) > 0]


def gagnants_pour_tous(profil: Profil, votants: list[int]) -> list[Issue]:
    """Issues strictement meilleures que le statu quo pour chaque votant."""
    return [s for s in profil if all(profil[s][i] > profil[STATU_QUO][i] for i in votants)]


def battu_par(profil: Profil, issue: Issue, votants: list[int]) -> list[Issue]:
    """Issues qui battent `issue` à la majorité des votants."""
    return [t for t in profil if majorite(profil[t], profil[issue], votants) > 0]


def invaincues(profil: Profil, votants: list[int]) -> list[Issue]:
    """Issues qu'aucune autre ne bat à la majorité (ordre du jour ouvert) ; vide = cycle."""
    return [s for s in profil if not battu_par(profil, s, votants)]


V3 = [0, 1, 2]
TOUS4 = [0, 1, 2, 3]

# P1 -- compromis à intensités : chaque mesure rapporte 5 à une cohorte, coûte 1 aux deux autres.
P1: Profil = additif({"A": (5, -1, -1), "B": (-1, 5, -1), "C": (-1, -1, 5)})

# P1B -- même profil chez les votants, mais chaque mesure est payée 3 par un non-votant.
P1B: Profil = additif({"A": (5, -1, -1, -3), "B": (-1, 5, -1, -3), "C": (-1, -1, 5, -3)})

# T -- témoin : transferts purs, aucun paquet n'est un gain pour tous.
T: Profil = additif({"A": (2, -1, -1), "B": (-1, 2, -1), "C": (-1, -1, 2)})

# E -- extraction à deux contre un.
E: Profil = additif({"A": (3, -2, -2), "B": (-2, 3, -2)})

# P2 -- comptabilité disjointe : D = dépense, F = son financement ; gains NON séparables.
D, F = "D", "F"
P2: Profil = {
    frozenset(): (0, 0, 0),
    frozenset({D}): (-1, -1, -1),      # dépense non financée : +2 affiché, -3 d'ajustement différé
    frozenset({F}): (-1, -1, -1),      # prélèvement sans contrepartie
    frozenset({D, F}): (1, 1, 1),      # dépense financée
}
AFFICHE_P2: dict[str, Gains] = {D: (2, 2, 2), F: (-1, -1, -1)}


def rapport(
    titre: str,
    profil: Profil,
    votants: list[int],
    tous: list[int],
    ordre: list[str],
    affiche: dict[str, Gains] | None = None,
) -> None:
    """Affiche, pour un profil, l'issue de chaque procédure et les ensembles de référence."""
    print(f"\n=== {titre} ===")
    for s in profil:
        print(f"  {nom(s):12s} {profil[s]}")
    po_votants = pareto(profil, votants)
    po_tous = pareto(profil, tous)
    print("  Pareto (votants)      :", ", ".join(nom(s) for s in po_votants))
    if tous != votants:
        print("  Pareto (avec non-votants) :", ", ".join(nom(s) for s in po_tous))
    sinc = carte_sincere(profil, ordre, votants)
    soph = carte_sophistiquee(profil, ordre, votants)
    print(f"  a la carte, sincere, comptes consolides : {nom(sinc)} {profil[sinc]}"
          f" | Pareto votants : {sinc in po_votants}")
    print(f"  a la carte, sophistique                 : {nom(soph)} {profil[soph]}"
          f" | Pareto votants : {soph in po_votants}")
    if affiche is not None:
        myope = carte_sincere(profil, ordre, votants, affiche)
        print(f"  a la carte, comptes disjoints affiches  : {nom(myope)} {profil[myope]}"
              f" | Pareto votants : {myope in po_votants}")
    gagne_tous = gagnants_pour_tous(profil, votants)
    passe = battent_le_statu_quo(profil, votants)
    print("  paquets battant le statu quo (majorite)  :", ", ".join(nom(s) for s in passe) or "aucun")
    print("  paquets gagnants pour tous les votants   :", ", ".join(nom(s) for s in gagne_tous) or "aucun")
    print("  issues invaincues a la majorite (ordre du jour ouvert) :",
          ", ".join(nom(s) for s in invaincues(profil, votants)) or "aucune (cycle)")
    for s in gagne_tous:
        print(f"    {nom(s)} est battu par :",
              ", ".join(nom(t) for t in battu_par(profil, s, votants)) or "personne")
    if tous != votants:
        for s in gagne_tous:
            total = sum(profil[s][i] for i in tous)
            print(f"    {nom(s)} : somme tous agents = {total},"
                  f" non-votants = {[profil[s][i] for i in tous if i not in votants]}")


def main() -> None:
    rapport("P1 compromis (gain reel)", P1, V3, V3, ["A", "B", "C"])
    rapport("P1b dette cachee (non-votant paie)", P1B, V3, TOUS4, ["A", "B", "C"])
    rapport("T temoin transferts purs", T, V3, V3, ["A", "B", "C"])
    rapport("E extraction deux contre un", E, V3, V3, ["A", "B"])
    rapport("P2 comptabilite disjointe, ordre D puis F", P2, V3, V3, [D, F], AFFICHE_P2)
    rapport("P2 comptabilite disjointe, ordre F puis D", P2, V3, V3, [F, D], AFFICHE_P2)


if __name__ == "__main__":
    main()
