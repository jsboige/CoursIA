"""Oracle de la retouche croisée sur les 576 jeux 2x2 ordinaux stricts.

Chaque joueur classe les quatre cases (CC, CD, DC, DD) par un rang strict de 1 à 4.
Une retouche est une suite d'échanges de rangs voisins (k et k+1, k = 1, 2, 3) dans
une table ; sa taille est le nombre minimal d'échanges. Le carnet GameTheory-03e
étudie le cas où chacun ne retouche que SA table. Ici, l'éditeur retouche la table
de L'AUTRE joueur, puis le jeu retouché est joué.

Comparaison retenue : jeux à équilibre pur unique avant et après la retouche.

    variation de l'éditeur = rang à l'équilibre d'arrivée - rang à l'équilibre de
                             départ - coût de la retouche (lu dans sa table, inchangée)
    variation de l'autre   = rang à l'équilibre d'arrivée - rang à l'équilibre de départ

Le rang d'arrivée de l'autre se lit dans deux livres de comptes :

    lecture R (règle)      : dans sa table retouchée, la retouche change ce que
                             les cases lui rapportent ;
    lecture I (incitation) : dans sa table d'origine, la retouche change ce qu'il
                             est poussé à jouer, pas ce que les cases valent pour lui.

Les rangs sont ordinaux : on lit des signes (qui monte, qui descend), pas un total.

Usage, depuis la racine du dépôt :

    python -X utf8 MyIA.AI.Notebooks/GameTheory/examples/oracle_derivation.py

Les libellés affichés sont en ASCII pour rester lisibles dans toute console.
"""
from __future__ import annotations

from collections import Counter
from itertools import permutations
from typing import Literal

CASES = ("CC", "CD", "DC", "DD")  # (coup de Ligne, coup de Colonne)
Table = tuple[int, int, int, int]
Jeu = tuple[Table, Table]
Lecture = Literal["R", "I"]
LECTURES: tuple[Lecture, Lecture] = ("R", "I")
Temoin = tuple[Jeu, int, int, str, str, int, int]

PD: Jeu = ((3, 1, 4, 2), (3, 4, 1, 2))


def tous_les_jeux() -> list[Jeu]:
    """Les 576 jeux : toutes les paires de classements stricts des quatre cases."""
    tables = list(permutations((1, 2, 3, 4)))
    return [(r, c) for r in tables for c in tables]


def equilibres_purs(jeu: Jeu) -> list[int]:
    """Indices des cases où aucun joueur ne gagne à dévier seul."""
    ligne, colonne = jeu
    eq = []
    for i in range(4):
        a, b = divmod(i, 2)  # a = coup de Ligne, b = coup de Colonne (0 = C, 1 = D)
        autre_ligne = (1 - a) * 2 + b
        autre_colonne = a * 2 + (1 - b)
        if ligne[i] > ligne[autre_ligne] and colonne[i] > colonne[autre_colonne]:
            eq.append(i)
    return eq


def swap(table: Table, k: int) -> Table:
    """Échange les rangs k et k+1 dans une table."""
    a, b, c, d = (k + 1 if v == k else k if v == k + 1 else v for v in table)
    return (a, b, c, d)


def remplace(jeu: Jeu, joueur: int, table: Table) -> Jeu:
    """Le jeu obtenu en donnant `table` au joueur indiqué (0 = Ligne, 1 = Colonne)."""
    return (table, jeu[1]) if joueur == 0 else (jeu[0], table)


def effet(
    jeu: Jeu,
    editeur: int,
    cible: Table,
    cout_total: int,
    lecture: Lecture = "R",
) -> tuple[int, int, int, int] | None:
    """Effet d'une retouche croisée : l'éditeur donne la table `cible` à l'autre joueur.

    Rend (case de départ, case d'arrivée, variation de l'éditeur, variation de l'autre),
    ou None si le jeu n'a pas un équilibre pur unique avant et après (hors comparaison).
    """
    autre = 1 - editeur
    arrivee = remplace(jeu, autre, cible)
    avant = equilibres_purs(jeu)
    apres = equilibres_purs(arrivee)
    if len(avant) != 1 or len(apres) != 1:
        return None
    e0, e1 = avant[0], apres[0]
    d_editeur = jeu[editeur][e1] - jeu[editeur][e0] - cout_total
    reference = arrivee if lecture == "R" else jeu
    d_autre = reference[autre][e1] - jeu[autre][e0]
    return e0, e1, d_editeur, d_autre


def classe(d_editeur: int, d_autre: int) -> str:
    """Classement par signes, cinq classes (retouches d'un pas)."""
    if d_editeur > 0 and d_autre < 0:
        return "derivation (editeur monte, autre descend)"
    if d_editeur > 0 and d_autre > 0:
        return "creation (les deux montent)"
    if d_editeur > 0:
        return "gain sans effet sur l'autre"
    if d_editeur == 0:
        return "neutre pour l'editeur"
    return "perte pour l'editeur"


def retouches_croisees(
    jeux: list[Jeu], cout: int
) -> tuple[Counter[str], Counter[str], list[Temoin]]:
    """Toutes les retouches d'un pas (jeu, éditeur, k), en lecture R.

    Rend le statut de chaque retouche, le classement de celles qui ont un équilibre
    unique avant et après, et jusqu'à trois témoins de dérivation.
    """
    statut: Counter[str] = Counter()
    classes: Counter[str] = Counter()
    temoins: list[Temoin] = []
    for jeu in jeux:
        for editeur in (0, 1):  # 0 = Ligne retouche la table de Colonne, 1 = l'inverse
            autre = 1 - editeur
            for k in (1, 2, 3):
                resultat = effet(jeu, editeur, swap(jeu[autre], k), cout)
                if resultat is None:
                    statut["hors comparaison (0 ou 2 equilibres purs avant ou apres)"] += 1
                    continue
                e0, e1, d_editeur, d_autre = resultat
                if e0 == e1:
                    # le rang de l'autre peut quand même changer : sa table a été retouchée
                    statut["equilibre inchange"] += 1
                else:
                    statut["equilibre deplace"] += 1
                c = classe(d_editeur, d_autre)
                classes[c] += 1
                if c.startswith("derivation") and len(temoins) < 3:
                    temoins.append((jeu, editeur, k, CASES[e0], CASES[e1], d_editeur, d_autre))
    return statut, classes, temoins


def meilleure_retouche(jeux: list[Jeu], cout: int) -> Counter[str]:
    """Par (jeu à équilibre unique, éditeur) : la meilleure retouche d'un pas est-elle profitable ?"""
    bilan: Counter[str] = Counter()
    for jeu in jeux:
        if len(equilibres_purs(jeu)) != 1:
            continue
        for editeur in (0, 1):
            autre = 1 - editeur
            meilleur: tuple[int, int] | None = None
            for k in (1, 2, 3):
                resultat = effet(jeu, editeur, swap(jeu[autre], k), cout)
                if resultat is None:
                    continue
                _, _, d_editeur, d_autre = resultat
                if meilleur is None or d_editeur > meilleur[0]:
                    meilleur = (d_editeur, d_autre)
            if meilleur is None or meilleur[0] <= 0:
                bilan["aucune retouche croisee profitable"] += 1
            elif meilleur[1] < 0:
                bilan["profitable, aux depens de l'autre"] += 1
            elif meilleur[1] > 0:
                bilan["profitable, l'autre monte aussi"] += 1
            else:
                bilan["profitable, autre inchange"] += 1
    return bilan


def retouche_de_soi(jeux: list[Jeu], cout: int) -> Counter[str]:
    """Témoin : même classement quand l'éditeur retouche SA table (périmètre de GT-03e).

    Convention de GT-03e : l'éditeur est payé au rang du jeu d'arrivée, moins le coût.
    """
    classes: Counter[str] = Counter()
    for jeu in jeux:
        avant = equilibres_purs(jeu)
        if len(avant) != 1:
            continue
        for editeur in (0, 1):
            autre = 1 - editeur
            for k in (1, 2, 3):
                arrivee = remplace(jeu, editeur, swap(jeu[editeur], k))
                apres = equilibres_purs(arrivee)
                if len(apres) != 1:
                    continue
                e0, e1 = avant[0], apres[0]
                d_editeur = arrivee[editeur][e1] - jeu[editeur][e0] - cout
                d_autre = jeu[autre][e1] - jeu[autre][e0]
                classes[classe(d_editeur, d_autre)] += 1
    return classes


def tables_par_distance(table: Table, dmax: int) -> dict[Table, int]:
    """Tables atteignables depuis `table` et leur nombre minimal d'échanges (parcours en largeur)."""
    vues = {table: 0}
    front = [table]
    for d in range(1, dmax + 1):
        suivant = []
        for t in front:
            for k in (1, 2, 3):
                u = swap(t, k)
                if u not in vues:
                    vues[u] = d
                    suivant.append(u)
        front = suivant
    return vues


def classe_fine(d_editeur: int, d_autre: int) -> str:
    """Classement par signes, sept classes (retouches de toute taille)."""
    if d_editeur > 0:
        if d_autre < 0:
            return "derivation (editeur +, autre -)"
        if d_autre > 0:
            return "creation (editeur +, autre +)"
        return "gain, autre ="
    if d_editeur == 0:
        if d_autre < 0:
            return "nuisance gratuite (editeur =, autre -)"
        if d_autre > 0:
            return "cadeau (editeur =, autre +)"
        return "decorative (editeur =, autre =)"
    return "perte pour l'editeur"


def par_taille(
    jeux: list[Jeu], cout: int, dmax: int = 3
) -> dict[tuple[Lecture, int], tuple[Counter[str], int]]:
    """Classement des retouches croisées par taille, sous les deux lectures.

    Rend, pour chaque (lecture, taille), le compteur des classes fines sur les retouches
    comparables et le nombre de retouches hors comparaison. Le coût est compté par échange.
    """
    classes: dict[tuple[Lecture, int], Counter[str]] = {
        (lecture, d): Counter() for lecture in LECTURES for d in range(1, dmax + 1)
    }
    hors: dict[tuple[Lecture, int], int] = {cle: 0 for cle in classes}
    for jeu in jeux:
        for editeur in (0, 1):
            for cible, d in tables_par_distance(jeu[1 - editeur], dmax).items():
                if d == 0:
                    continue
                for lecture in LECTURES:
                    resultat = effet(jeu, editeur, cible, cout * d, lecture)
                    if resultat is None:
                        hors[(lecture, d)] += 1
                        continue
                    _, _, d_editeur, d_autre = resultat
                    classes[(lecture, d)][classe_fine(d_editeur, d_autre)] += 1
    return {cle: (classes[cle], hors[cle]) for cle in classes}


def paires_exposees(jeux: list[Jeu], cout: int, dmax: int, lecture: Lecture) -> tuple[int, int]:
    """Nombre de (jeu à équilibre unique, éditeur) où une dérivation de taille <= dmax existe.

    Rend (couples exposés, couples examinés).
    """
    exposees = 0
    total = 0
    for jeu in jeux:
        if len(equilibres_purs(jeu)) != 1:
            continue
        for editeur in (0, 1):
            total += 1
            for cible, d in tables_par_distance(jeu[1 - editeur], dmax).items():
                if d == 0:
                    continue
                resultat = effet(jeu, editeur, cible, cout * d, lecture)
                if resultat is not None and resultat[2] > 0 and resultat[3] < 0:
                    exposees += 1
                    break
    return exposees, total


def dilemme_un_pas() -> dict[tuple[int, int], list[str]]:
    """Dilemme du prisonnier : équilibres purs après chaque retouche croisée d'un pas.

    Clé : (éditeur, k) ; valeur : les cases d'équilibre du jeu retouché.
    """
    apres: dict[tuple[int, int], list[str]] = {}
    for editeur in (0, 1):
        autre = 1 - editeur
        for k in (1, 2, 3):
            arrivee = remplace(PD, autre, swap(PD[autre], k))
            apres[(editeur, k)] = [CASES[i] for i in equilibres_purs(arrivee)]
    return apres


def affiche(titre: str, c: Counter[str]) -> None:
    """Affiche un compteur, classes les plus fréquentes d'abord."""
    total = sum(c.values())
    print(f"\n{titre} (total {total})")
    for cle, n in sorted(c.items(), key=lambda kv: -kv[1]):
        print(f"  {n:5d}  {100 * n / total:5.1f} %  {cle}")


def affiche_par_taille(
    resultats: dict[tuple[Lecture, int], tuple[Counter[str], int]], cout: int, dmax: int = 3
) -> None:
    """Affiche le classement par taille rendu par `par_taille`."""
    for lecture in LECTURES:
        print(f"\n--- Lecture {lecture}, cout par swap = {cout} ---")
        for d in range(1, dmax + 1):
            classes, hors = resultats[(lecture, d)]
            total = sum(classes.values())
            print(f"  taille {d} : {total} retouches comparables, {hors} hors comparaison")
            for cle, n in sorted(classes.items(), key=lambda kv: -kv[1]):
                print(f"    {n:5d}  {100 * n / total:5.1f} %  {cle}")


def main() -> None:
    jeux = tous_les_jeux()
    dist = Counter(len(equilibres_purs(j)) for j in jeux)
    print("Jeux :", len(jeux), "| equilibres purs par jeu :", dict(sorted(dist.items())))
    assert len(jeux) == 576
    assert dict(dist) == {0: 72, 1: 432, 2: 72}, dist
    assert [CASES[i] for i in equilibres_purs(PD)] == ["DD"]
    assert swap((3, 1, 4, 2), 3) == (4, 1, 3, 2)  # R3 : PD -> table de Ligne du Cerf
    print("Controles : 576 jeux, {0: 72, 1: 432, 2: 72}, equilibre du PD = DD, swap R3 conforme.")

    for cout in (0, 1):
        print(f"\n=== Retouche de la table de l'autre, cout = {cout} ===")
        statut, classes, temoins = retouches_croisees(jeux, cout)
        affiche("Statut des retouches (jeu, editeur, k)", statut)
        affiche("Classement par signes, retouches a equilibre unique avant et apres", classes)
        affiche("Meilleure retouche croisee par (jeu a equilibre unique, editeur)",
                meilleure_retouche(jeux, cout))
        for jeu, editeur, k, e0, e1, d_e, d_a in temoins[:2]:
            qui = "Ligne" if editeur == 0 else "Colonne"
            print(f"  temoin : jeu {jeu}, {qui} echange les rangs {k}/{k + 1} chez l'autre, "
                  f"{e0} -> {e1}, editeur {d_e:+d}, autre {d_a:+d}")

    print("\n=== Temoin : retouche de SA propre table (perimetre de GT-03e), cout = 1 ===")
    affiche("Classement par signes", retouche_de_soi(jeux, 1))

    assert Counter(tables_par_distance((1, 2, 3, 4), 3).values()) == {0: 1, 1: 3, 2: 5, 3: 6}
    for cout in (0, 1):
        print(f"\n=== Par taille de retouche (table de l'autre), cout par swap = {cout} ===")
        affiche_par_taille(par_taille(jeux, cout), cout)
        for lecture in LECTURES:
            for dmax in (1, 2, 3):
                n, tot = paires_exposees(jeux, cout, dmax, lecture)
                print(f"  lecture {lecture}, taille <= {dmax} : {n} / {tot} (jeu, editeur) "
                      f"exposes a une derivation")

    # Le dilemme : que peut une retouche croisée d'un seul pas ?
    print("\n=== Dilemme du prisonnier, retouches croisees d'un pas, cout = 0 ===")
    for (editeur, k), cases in dilemme_un_pas().items():
        qui = "Ligne" if editeur == 0 else "Colonne"
        print(f"  {qui} echange {k}/{k + 1} chez l'autre -> equilibres {cases}")


if __name__ == "__main__":
    main()
