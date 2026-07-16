# Search — phase 1 : analyse de cohérence narrative (#5081)

Deuxième série analysée pour l'EPIC #5081 (après [Probas/Infer](infer-renumbering-phase1.md), verdict « no-defect-found »).
Contrairement à Probas/Infer, **Search présente un défaut de navlink résiduel** — mais **pas de renumérotation** nécessaire.

## Méthode

Les notebooks Search portent un bloc **Navigation** en cellule 0 (et pied de page) :

```
**Navigation** : [<< Précédent](X.ipynb) | [Index](../README.md) | [Suivant >>](Y.ipynb)
```

Le lien `[<< Précédent]` encode le **prédécesseur narratif déclaré** (le vrai prereq de la
colonne vertébrale), pas simplement un « see-also ». J'ai extrait ces `<<`/`>>` pour
reconstruire la chaîne narrative déclarée, puis scanné les **navlinks arrières**
(`<<` cible dans la même série avec un numéro `>=` au numéro courant) — signature d'un
**résidu de réorganisation périmé** : la cible a été renommée pendant la reorg Part1-4,
le lien conceptuel a cassé, le navlink n'a pas été mis à jour.

## Résultat du scan (firsthand, 112 notebooks, 4 sous-dossiers)

| Métrique | Valeur |
|----------|--------|
| Notebooks scannés | 112 (Part1-Foundations, Part2-CSP, Part3-Advanced, Applications) |
| Navlinks cassés (404) | **0** (`check_notebook_navlinks.py --family Search`) — déjà réparés par la vague #6801/#6809/#6821/#6827/#6859 |
| Navlinks arrières bruts | 9 |
| — dont jumeaux C# (`b`) vers l'original Python | 5 (légitimes : le port C# précède son original Python) |
| — dont sous-série Search-11b-Deep (Part2/3/4) | 3 (légitimes : parties séquentielles) |
| — dont **vraie cible périmée** | **1** : `Search-8-DancingLinks << Search-11-Metaheuristics` |

## Le défaut (confirmé firsthand)

`Search-8-DancingLinks.ipynb` (cellule 0 + cellule 56) déclarait :

```
[<< Metaheuristiques](Search-11-Metaheuristics.ipynb)
```

**Pourquoi c'est un résidu périmé** : pendant la reorg Part1-4, `Search-11-SimulatedAnnealing`
a été absorbé dans `Search-11-Metaheuristics` (SA plié dans le notebook métaheuristique plus
large). Le `<<` pointait originellement vers SA (lien local-search ↔ exact-cover défensible) ;
après rename, il pointe vers « Métaheuristiques » au sens large (PSO/ABC/SA…) — Dancing Links
(algorithme X de Knuth, exact-cover) n'a **aucun lien conceptuel** avec les métaheuristiques.

**Pourquoi le checker 404 ne l'a pas vu** : la cible `Search-11-Metaheuristics.ipynb`
**existe** (elle résout) — le checker de la vague #6801 ne catche que les 404, pas les
cibles « résout-vers-existant mais conceptuellement cassées ».

## Correctif appliqué (cette PR)

Restauration de la **symétrie de la colonne vertébrale** : `Search-7-MCTS-And-Beyond >>`
pointe déjà vers `Search-8-DancingLinks`, donc `Search-8 <<` doit pointer vers
`Search-7-MCTS-And-Beyond`. Remplacement des 2 occurrences (en-tête cellule 0 + pied de
page cellule 56) :

```
[<< MCTS](Search-7-MCTS-And-Beyond.ipynb)
```

Diff +2/−2, markdown-only (C.2-safe, pas de re-exécution — #6722/#6796). Post-fix :
`check_notebook_navlinks` = 0 cassé, `check_docs_links` = 0/3968 maintenu.

## Verdict — pas de renumérotation

Les autres « écarts structurels » observés sont **défendables par design**, pas des défauts :

- `Search-11 << Search-4` (gap 4→11) : les métaheuristiques bâtissent sur la recherche locale
  (Search-4), le saut sur la branche adversarielle/MCTS est intentionnel.
- `Search-6 << Search-3` : la recherche adversarielle (minimax) nécessite les heuristiques
  (Search-3 Informed), fourche légitime après les fondations.
- `Search-12/13/14` dans Part3-Advanced : collection « techniques avancées » **intentionnellement
  séparée** (cf blockquote intro Search-12 : « Partie 3 — Recherche avancée, au-delà des
  fondations de la Partie 1 »). Pas sur la colonne vertébrale Part1 par design.
- `Search-15 << Search-11`, `Search-10/16` sans `<<` : sujets autonomes (graphes, automates).

**Conclusion** : la série Search ne souffre pas de « numérotation d'opportunité » — la structure
Part1 (fondations) / Part2-CSP / Part3-Advanced (blockquotes explicites) / Applications est
cohérente. Le seul défaut était un navlink périmé (résidu de reorg), désormais réparé.

À comparer :
- **Probas/Infer** : no-defect-found (ordre 1→19 déjà tri topo valide du DAG).
- **Search** : 1 défaut de navlink (résidu périmé), 0 défaut de numérotation.

## Hors scope (transparence)

- **Applications/{CSP,Hybrid,Search}** : ensemble d'exercices capstone plat, pas une progression
  narrative — la numérotation y est un index d'exercices, pas un ordre pédagogique.
- **Jumeaux C# (`-Csharp` / suffixe `b`)** : ports miroirs des notebooks Python, même
  numérotation par construction.

See #5081.
