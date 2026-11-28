"""Analyse le journal d'etiquettes que le binaire patche ecrit avec
`--dir-label-boxes FICHIER` pendant un rendu.

Le journal compte, top d'horloge interne par top d'horloge interne, ce que la
selection des noms de repertoires a devant elle et ce qu'elle en garde :

    F  index  candidats  retenus  paires_candidates  paires_retenues

  une ligne par top : le nombre de noms candidats, le nombre de noms retenus,
  le nombre de paires de boites qui se chevauchent avant la selection et apres.

    L  index  texte  profondeur  alpha  x  y  largeur  hauteur  garde  contre  groupe  id

  une ligne par nom candidat, aux tops que `--dir-label-boxes-every` choisit
  (30 par defaut, soit une lecture par demi-seconde de film). `y` est le haut
  de la ligne telle qu'elle est dessinee : `draw(x, y)` pose la ligne de base a
  `y + getHeight()` (`align_top`), et `getHeight()` vaut `ceil(asc + desc)`.
  `garde` vaut 1 pour un nom dessine, 0 pour un nom ecarte ; `contre` nomme le
  nom deja retenu dont la boite chevauche la sienne, `-` sinon ; `groupe` vaut
  0 pour un repertoire en changement hors hub, 1 pour une etiquette de hub, 2
  pour un nom place sous un hub nomme ; `id` identifie le nom d'un top a
  l'autre, ce qui permet de suivre un meme nom sans appariement approximatif.

Le rendu est lance a 30 images par seconde et Gource simule alors a 60 Hz,
une image exportee sur deux tops : le top d'indice i tombe a la i / 60 seconde
du film, soit l'image i / 2. Une image tiree a une image par seconde pour la
seconde s n'est donc PAS le top 60*s : c'est l'image 30*s+14, soit le top
60*s+28 (mesure sur le film v3, ou la trame 152 est l'image 4544). Le journal
ne dit rien de la taille des noms dans une image reduite : il mesure la
selection, pas la lisibilite d'une trame.

Usage :
    python analyse_journal.py <journal> [seconde ...]

Les secondes nommees en argument sont imprimees en detail.
"""
from __future__ import annotations

import sys
from collections import Counter
from pathlib import Path

TOPS_PAR_SECONDE = 60
SECONDES_PAR_TRANCHE = 10
# Une image tiree a une par seconde tombe a mi-seconde : top 60*s + 28.
DECALAGE_TRAME = 28
GROUPES = {0: "hors hub", 1: "hub", 2: "sous hub nomme"}


def quantile(tries: list[int], q: float) -> float:
    """Quantile empirique d'une liste d'entiers deja triee, interpolee."""
    if not tries:
        return 0.0
    pos = q * (len(tries) - 1)
    bas = int(pos)
    haut = min(bas + 1, len(tries) - 1)
    return tries[bas] + (tries[haut] - tries[bas]) * (pos - bas)


def main() -> int:
    if len(sys.argv) < 2:
        print("usage: analyse_journal.py <journal> [seconde ...]", file=sys.stderr)
        return 2
    journal = Path(sys.argv[1])
    focus = sorted({int(a) for a in sys.argv[2:]})

    # index -> (candidats, retenus, paires candidates, paires retenues)
    tops: dict[int, tuple[int, int, int, int]] = {}
    # index -> liste de (texte, profondeur, alpha, garde, contre, groupe, id)
    etiquettes: dict[int, list[tuple[str, int, float, int, str, int, int]]] = {}
    for raw in journal.read_text(encoding="utf-8", errors="replace").splitlines():
        parts = raw.split("\t")
        if parts[0] == "F" and len(parts) == 6:
            tops[int(parts[1])] = (int(parts[2]), int(parts[3]),
                                   int(parts[4]), int(parts[5]))
        elif parts[0] == "L" and len(parts) == 12:
            raise SystemExit(
                f"{journal.name} : journal a 12 colonnes, ecrit par un binaire "
                f"anterieur -- son ordonnee est 28 px trop haut et il ne porte "
                f"pas l'identite des noms. Regenerer le journal avec le binaire "
                f"courant, ou lire l'ancien avec l'instrument de son epoque.")
        elif parts[0] == "L" and len(parts) == 13:
            etiquettes.setdefault(int(parts[1]), []).append(
                (parts[2], int(parts[3]), float(parts[4]), int(parts[9]),
                 parts[10], int(parts[11]), int(parts[12])))

    indices = sorted(tops)
    if not indices:
        print("aucune ligne F exploitable", file=sys.stderr)
        return 1
    dernier = indices[-1]
    pas = sorted({b - a for a, b in zip(indices, indices[1:])})
    print(f"# journal     : {journal.name}")
    print(f"# tops        : {len(indices)} (de {indices[0]} a {dernier}), "
          f"soit {dernier / TOPS_PAR_SECONDE:.1f} s de film a "
          f"{TOPS_PAR_SECONDE} tops par seconde, "
          f"{dernier // 2 + 1} images")
    print(f"# lectures    : ecart(s) entre deux lectures de noms : {pas}")

    candidats = sorted(tops[i][0] for i in indices)
    retenus = sorted(tops[i][1] for i in indices)
    paires_avant = sum(tops[i][2] for i in indices)
    paires_apres = sum(tops[i][3] for i in indices)

    # --- 1. chevauchements ---------------------------------------------------
    print("\n## Chevauchement des etiquettes (toutes les lignes F)")
    print(f"paires de boites en chevauchement avant selection : {paires_avant}")
    print(f"paires de boites en chevauchement apres selection : {paires_apres}")
    print(f"tops avec au moins une paire retenue : "
          f"{sum(1 for i in indices if tops[i][3] > 0)}")
    print(f"tops sans aucune paire candidate    : "
          f"{sum(1 for i in indices if tops[i][2] == 0)}")

    # --- 2. densite par top --------------------------------------------------
    print("\n## Densite par top")
    print("  %-12s %8s %8s %6s %8s" % ("", "moyenne", "mediane", "p95", "maximum"))
    for nom, serie in (("candidats", candidats), ("retenus", retenus)):
        print("  %-12s %8.2f %8.0f %6.0f %8d"
              % (nom, sum(serie) / len(serie), quantile(serie, 0.5),
                 quantile(serie, 0.95), serie[-1]))
    print(f"tops sans aucun nom retenu : {sum(1 for v in retenus if v == 0)}")

    print(f"\n  profil par tranches de {SECONDES_PAR_TRANCHE} s :")
    for debut in range(0, dernier // TOPS_PAR_SECONDE + 1, SECONDES_PAR_TRANCHE):
        fen = [tops[i] for i in indices
               if debut * TOPS_PAR_SECONDE <= i
               < (debut + SECONDES_PAR_TRANCHE) * TOPS_PAR_SECONDE]
        if not fen:
            continue
        print("    %3d-%3d s  candidats moy %7.2f  retenus moy %6.2f  "
              "retenus max %3d  paires candidats %9d  paires retenues %d"
              % (debut, debut + SECONDES_PAR_TRANCHE - 1,
                 sum(t[0] for t in fen) / len(fen),
                 sum(t[1] for t in fen) / len(fen),
                 max(t[1] for t in fen),
                 sum(t[2] for t in fen), sum(t[3] for t in fen)))

    # --- 3. etiquettes echantillonnees ---------------------------------------
    echantillons = sorted(etiquettes)
    toutes = [e for i in echantillons for e in etiquettes[i]]
    gardees = [e for e in toutes if e[3] == 1]
    par_groupe = Counter(e[5] for e in gardees)
    print("\n## Etiquettes echantillonnees")
    print(f"lectures           : {len(echantillons)}")
    print(f"noms candidats     : {len(toutes)}, dont retenus {len(gardees)} "
          f"({100.0 * len(gardees) / len(toutes):.1f} %) et ecartes "
          f"{len(toutes) - len(gardees)}")
    if toutes:
        for groupe in sorted(GROUPES):
            n = par_groupe.get(groupe, 0)
            print(f"  retenus, {GROUPES[groupe]:14s}: {n:5d} "
                  f"({100.0 * n / len(gardees):.1f} % des retenus)")

    # --- 4. stabilite du jeu retenu ------------------------------------------
    # Un nom suit par son `id` : retenu a une lecture, l'est-il encore a la
    # suivante ? Un nom ecarte alors qu'il est toujours candidat a cede sa place
    # a un concurrent -- c'est le clignotement, invisible dans une seule lecture.
    print("\n## Stabilite du jeu retenu (d'une lecture a la suivante)")
    reste = deplace = disparu = gagne = 0
    alpha_deplaces: list[float] = []
    ecarts = Counter()
    for top, suivant in zip(echantillons, echantillons[1:]):
        ecarts[suivant - top] += 1
        avant = {e[6]: e for e in etiquettes[top]}
        apres = {e[6]: e for e in etiquettes[suivant]}
        garde_avant = {i for i, e in avant.items() if e[3] == 1}
        garde_apres = {i for i, e in apres.items() if e[3] == 1}
        for ident in garde_avant:
            if ident not in apres:
                disparu += 1
            elif ident in garde_apres:
                reste += 1
            else:
                deplace += 1
                alpha_deplaces.append(avant[ident][2])
        gagne += len(garde_apres - garde_avant)
    total = reste + deplace + disparu
    if total:
        print(f"  ecart(s) entre deux lectures : {dict(sorted(ecarts.items()))}")
        print(f"  noms retenus puis encore candidats : {total}")
        print(f"    restent retenus   : {reste:7d} ({100.0 * reste / total:5.1f} %)")
        print(f"    deplaces          : {deplace:7d} ({100.0 * deplace / total:5.1f} %)")
        print(f"    disparus          : {disparu:7d} "
              f"({100.0 * disparu / total:5.1f} %)")
        print(f"  noms qui gagnent une place : {gagne}")
        if alpha_deplaces:
            alpha_deplaces.sort()
            print(f"  alpha d'un nom deplace : moyen {sum(alpha_deplaces) / len(alpha_deplaces):.3f}"
                  f" ; median {quantile(alpha_deplaces, 0.5):.3f}")
        print("  duree de vie d'un nom retenu, en plages de tops consecutifs :")
        plages: list[int] = []
        for tops_du_nom in _tops_par_nom(etiquettes).values():
            debut = precedent = tops_du_nom[0]
            for top in tops_du_nom[1:]:
                if top != precedent + 1:
                    plages.append(precedent - debut + 1)
                    debut = top
                precedent = top
            plages.append(precedent - debut + 1)
        plages.sort()
        print(f"    {len(plages)} plages ; moyenne {sum(plages) / len(plages):.2f} tops, "
              f"mediane {quantile(plages, 0.5):.0f} tops, plus longue {plages[-1]} tops")
        for seuil in (1, 2, 6, 12, 30):
            n = sum(1 for v in plages if v <= seuil)
            print(f"    plages <= {seuil:2d} tops : {n:7d} "
                  f"({100.0 * n / len(plages):5.1f} %)")

    # --- 5. les trames intermediaires ----------------------------------------
    # Les trames d'une par seconde que lit l'OCR sont prises a mi-seconde :
    # l'image 30*s+14, soit le top 60*s+28. On relit le journal a ces tops la,
    # pour que les deux instruments portent sur les memes images.
    print(f"\n## Les trames intermediaires (une par seconde, top 60*s+{DECALAGE_TRAME})")
    trames = [s for s in range(dernier // TOPS_PAR_SECONDE + 1)
              if s * TOPS_PAR_SECONDE + DECALAGE_TRAME in tops]
    if trames:
        avant = {s: tops[s * TOPS_PAR_SECONDE + DECALAGE_TRAME][2] for s in trames}
        apres = {s: tops[s * TOPS_PAR_SECONDE + DECALAGE_TRAME][3] for s in trames}
        avec_avant = [s for s in trames if avant[s] > 0]
        avec_apres = [s for s in trames if apres[s] > 0]
        pire = max(trames, key=lambda s: avant[s])
        print(f"trames lues                        : {len(trames)} "
              f"(secondes {trames[0]} a {trames[-1]})")
        print(f"paires avant selection             : {sum(avant.values())}")
        print(f"paires apres selection             : {sum(apres.values())}")
        print(f"trames avec au moins une paire, avant : {len(avec_avant)} "
              f"({100.0 * len(avec_avant) / len(trames):.1f} %)")
        print(f"trames avec au moins une paire, apres  : {len(avec_apres)} "
              f"({100.0 * len(avec_apres) / len(trames):.1f} %)")
        print(f"maximum avant selection            : {avant[pire]} (seconde {pire})")
        print(f"\n  profil par tranches de {SECONDES_PAR_TRANCHE} s :")
        for debut in range(0, trames[-1] + 1, SECONDES_PAR_TRANCHE):
            fen = [s for s in trames if debut <= s < debut + SECONDES_PAR_TRANCHE]
            if not fen:
                continue
            print("    %3d-%3d s  paires avant %7d (max %4d, %2d trames sur %2d)  "
                  "paires apres %d"
                  % (debut, debut + SECONDES_PAR_TRANCHE - 1,
                     sum(avant[s] for s in fen), max(avant[s] for s in fen),
                     sum(1 for s in fen if avant[s] > 0), len(fen),
                     sum(apres[s] for s in fen)))
        plus_denses = sorted(trames, key=lambda s: -avant[s])[:12]
        print("\n  douze trames intermediaires les plus chevauchees avant selection :")
        for s in plus_denses:
            c, r, pa, pr = tops[s * TOPS_PAR_SECONDE + DECALAGE_TRAME]
            print(f"    seconde {s:3d} (top {s * TOPS_PAR_SECONDE + DECALAGE_TRAME:5d})  "
                  f"{c:3d} candidats  {r:3d} retenus  {pa:4d} paires avant  {pr} apres")

    # --- 6. secondes demandees ----------------------------------------------
    for seconde in focus:
        top = seconde * TOPS_PAR_SECONDE + DECALAGE_TRAME
        if top not in tops:
            print(f"\n  seconde {seconde} : hors journal (top {top})")
            continue
        c, r, pa, pr = tops[top]
        print(f"\n  seconde {seconde} (trame d'une par seconde, top {top}, image {top // 2}) : "
              f"{c} candidats, {r} retenus, {pa} paires candidates, {pr} retenues")
        presentes = etiquettes.get(top)
        if presentes is None:
            print("    aucune lecture de noms a ce top")
            continue
        for groupe in sorted(GROUPES):
            noms = sorted((e for e in presentes if e[3] == 1 and e[5] == groupe),
                          key=lambda e: (e[1], e[0]))
            if noms:
                print(f"    retenus, {GROUPES[groupe]} :")
                for texte, profondeur, _alpha, _g, _c, _gr, _id in noms:
                    print(f"      prof. {profondeur}  {texte}")
        ecartes = Counter(e[4] for e in presentes if e[3] == 0)
        print(f"    ecartes : {sum(ecartes.values())} ; les cinq noms retenus "
              f"qui font le plus lever d'autres : {ecartes.most_common(5)}")

    return 0


def _tops_par_nom(etiquettes: dict[int, list[tuple]]) -> dict[int, list[int]]:
    """id -> tops ou ce nom est retenu, croissants."""
    par_nom: dict[int, list[int]] = {}
    for top in sorted(etiquettes):
        for e in etiquettes[top]:
            if e[3] == 1:
                par_nom.setdefault(e[6], []).append(top)
    return par_nom


if __name__ == "__main__":
    raise SystemExit(main())
