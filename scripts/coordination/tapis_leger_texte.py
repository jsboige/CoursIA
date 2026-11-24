#!/usr/bin/env python3
"""La SORTIE TEXTE de la voie legere du tirage.

Extraite de ``tapis_leger.py`` pour tenir son plafond de lignes (#21067 :
la greffe du cap de livraisons s'y paye en extraction, comme chaque
extension avant elle -- cf. l'historique du plafond dans
``test_tapis_rapide.py::test_plafonds_de_lignes``). ``tapis_leger``
re-exporte ``texte`` : les appelants (``tapis_voie_leger``, tests) ne
changent pas.

Les blocs de la **fenetre** et de la **qualification** vivent dans
``tapis_leger_fenetre`` : meme raison -- la fonction ``texte`` tient sous
60 lignes, et le refus d'un grain s'affiche avec son code et son motif.
"""
from coordination import tapis_leger_fenetre as lq


def texte(r: dict) -> str:
    """La sortie courte de la voie leger : l'etat de chaque grain et l'action.

    Elle dit ce que le chemin lourd dit, et deux choses de plus : **ou** se
    qualifie un grain, et **quand** (avant l'action).
    """
    lu = r["lecture"]
    lignes = [f"Tapis leger -- lane {r['lane']} -- {r['maintenant']} "
              f"-- source : GitHub + origin/main local (rotation universelle)"]
    lignes.append(f"{lu['issues']} issues ouvertes ; rotation sur metadonnees seules "
                  f"(selection {lu['selection_s']} s, citations {lu['phases'].get('citations_s')} s, "
                  f"PRs {lu['phases'].get('prs_s')} s, budget {lu['budget_s']} s) ; "
                  f"file de {len(r['grains'])} grain(s)")
    lignes += lq.texte_fenetre(r.get("fenetre") or {})
    lignes.append(f"\nVos PRs ouvertes ({len(r['vos_prs'])}) -- traitez d'abord leurs nits :")
    lignes += [f"  #{p['numero']}  {p['age_j']} j  {p['titre'][:90]}"
               for p in r["vos_prs"]]
    lignes.append("\nGrains -- deja qualifies sur leur fil complet, a claimer puis servir :")
    for g in r["grains"]:
        lignes.append(f"  #{g['numero']}  {g['titre'][:80]}")
        lignes.append(f"      {g['action']}")
    lignes += lq.texte_qualification(r["qualification"])
    cap = r.get("cap_livraisons") or {}
    if cap.get("ecartes"):
        for t in cap["ecartes"]:
            lignes.append(f"\nCap livraisons EPIC (#21067) : #{t['numero']} ecarte -- "
                          f"{t['motif']}")
    return "\n".join(lignes)
