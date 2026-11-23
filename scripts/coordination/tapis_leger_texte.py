#!/usr/bin/env python3
"""La SORTIE TEXTE de la voie legere du tirage.

Extraite de ``tapis_leger.py`` pour tenir son plafond de lignes (#21067 :
la greffe du cap de livraisons s'y paye en extraction, comme chaque
extension avant elle -- cf. l'historique du plafond dans
``test_tapis_rapide.py::test_plafonds_de_lignes``). ``tapis_leger``
re-exporte ``texte`` : les appelants (``tapis_voie_leger``, tests) ne
changent pas.
"""


def texte(r: dict) -> str:
    """La sortie courte de la voie leger : l'etat de chaque grain et l'action.

    Elle dit ce que le chemin lourd dit, et une chose de plus : **ou** se
    qualifie un grain, et **quand** (avant l'action).
    """
    lu = r["lecture"]
    lignes = [f"Tapis leger -- lane {r['lane']} -- {r['maintenant']} "
              f"-- source : GitHub + origin/main local (rotation universelle)"]
    lignes.append(f"{lu['issues']} issues ouvertes ; rotation sur metadonnees seules "
                  f"(selection {lu['selection_s']} s, citations {lu['phases'].get('citations_s')} s, "
                  f"PRs {lu['phases'].get('prs_s')} s, budget {lu['budget_s']} s) ; "
                  f"file de {len(r['grains'])} grain(s)")
    fen = r.get("fenetre") or {}
    if fen.get("ordre") == "age":
        seuil = (fen.get("age") or {}).get("seuil_h", 72)
        lignes.append(f"Selection par AGE (mandat du 22/11) : les issues "
                      f"anciennes d'abord ; une issue de moins de {seuil} h "
                      f"va en fin de file ; "
                      f"{(fen.get('age') or {}).get('exclus', 0)} issue(s) "
                      f"deja servie(s) en attente de verdict, laisses de cote.")
    if fen.get("blocs", 1) > 1:
        lignes.append(f"Fenetre : bloc {fen['bloc']}/{fen['blocs']} du pool classe "
                      f"(taille {fen['taille']}) -- la fenetre avance d'un bloc par "
                      f"tranche de 4 h : le pool entier est couvert en "
                      f"{fen['blocs']} tranches.")
    non_visites = fen.get("non_visites") or []
    if non_visites:
        apercu = ", ".join(f"#{n}" for n in non_visites[:12])
        suite = " ..." if len(non_visites) > 12 else ""
        lignes.append(f"Fenetre : {len(non_visites)} numero(s) du pool non visite(s) "
                      f"a cette tranche -- delai max de requalification "
                      f"{fen.get('delai_max_h')} h : {apercu}{suite}.")
    elif fen.get("delai_max_h"):
        lignes.append(f"Fenetre : pool entier visite -- delai max de "
                      f"requalification {fen.get('delai_max_h')} h.")
    lignes.append(f"\nVos PRs ouvertes ({len(r['vos_prs'])}) -- traitez d'abord leurs nits :")
    lignes += [f"  #{p['numero']}  {p['age_j']} j  {p['titre'][:90]}"
               for p in r["vos_prs"]]
    lignes.append("\nGrains -- qualifier avant action, puis servir :")
    for g in r["grains"]:
        lignes.append(f"  #{g['numero']}  {g['titre'][:80]}")
        lignes.append(f"      {g['action']}")
    q = r["qualification"]
    lignes.append(f"\nQualification : {q['organe']} -- {q['quand']} ; {q['ecarts']}.")
    cap = r.get("cap_livraisons") or {}
    if cap.get("ecartes"):
        for t in cap["ecartes"]:
            lignes.append(f"\nCap livraisons EPIC (#21067) : #{t['numero']} ecarte -- "
                          f"{t['motif']}")
    return "\n".join(lignes)
