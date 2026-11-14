# Metajeux — modifier l'espace des jeux plutôt qu'y jouer

Sous-dossier de la série [GameTheory](../README.md). Les carnets qui y vivent ne résolvent pas un
jeu donné : chacun isole un **geste sur la représentation** — composer des jeux ouverts, abstraire
un jeu trop grand, témoigner qu'un chemin existe ou ne peut pas exister. Le voisin d'amont dans la
navigation est [GameTheory-17 — RL multi-agents](../GameTheory-17-MultiAgent-RL-Python.ipynb) :
la marche 01 s'y chaîne, et l'escalier se lit **après** le parcours principal, jamais à sa place.
[19b — Co-design bilevel](../GameTheory-19b-Bilevel-PPO-Python.ipynb) reste en racine (extension
autonome, voir la [section Escaliers](../README.md#escaliers) du README racine).

Note de conception : [commentaire `6712250655` sur #20316](https://github.com/jsboige/CoursIA/issues/20316#issuecomment-6712250655) —
table de mapping (règle notebook-accretion-numbering §5.5) et hypothèses consignées ; cette page
en est la mise en étalage.

## Les marches — composer, casser, abstraire, témoigner

| # | Carnet | Le geste | Ex-racine |
|---|--------|----------|-----------|
| 01 | [Open games et lentilles](Metajeux-01-Open-Games-Lentilles-Python.ipynb) | **Composer** : une représentation locale (lentille) qui modifie le global dont elle est issue — les open games de Hedges et la propriété de composition des équilibres | 18 |
| 02 | [Casser la composition](Metajeux-02-Casser-la-Composition-Python.ipynb) | **Casser** : contre-exemples mesurés à la compositionnalité (sélection multivoque, paiements couplés) et frontière de contraction coïncidant avec la borne de Banach | 18b |
| 03 | [Abstraction à dette](Metajeux-03-Abstraction-a-Dette-Python.ipynb) | **Abstraire** : résoudre un jeu abstrait plus petit, relever la stratégie, chiffrer l'exploitabilité dans le jeu d'origine — la courbe de dette est le livrable | 19 |
| 04 | [Chemin minimal](Metajeux-04-Chemin-Minimal-Robinson-Goforth-Python.ipynb) | **Témoigner** : un constructeur produit le chemin minimal (Robinson-Goforth 2×2), un vérificateur séparé re-dérive validité et minimalité | 20 |
| 05 | [Témoins d'impossibilité](Metajeux-05-Temoins-Impossibilite-Python.ipynb) | **Réfuter** : prouver qu'aucun chemin plus court n'existe, par la structure produit des chambres | 20b |
| 06 | [Chemin minimal 3×2](Metajeux-06-Chemin-Minimal-3x2-Ordinal-Python.ipynb) | **Transposer** : sur un second substrat, le verdict 2×2 tombe — 15,0 % des paires raccourcissent en traversant les murs, le diamètre se contracte de 15 à 10 | 20c |

Ordre de lecture interne : `01 → 02 → 03 → 04 → 05 → 06` — la marche 02 casse ce que 01 pose,
la marche 06 casse ce que 04-05 avaient attesté sur le premier substrat.

## Compagnon formel (lake)

| Module du lake [`game_theory_lean`](../game_theory_lean/README.md) | Rôle dans l'escalier |
|---|---|
| [`Abstraction`](../game_theory_lean/Abstraction/Basic.lean) | **Marche 03** : le carnet importe le module et fait élaborer ses théorèmes — la courbe de dette mesurée recoupe une preuve (le 03e de la racine le présente aussi) |

## Départs vers d'autres séries

Deux carnets nés dans la strate 18-20 de la racine ont rejoint d'autres séries et ne comptent pas
comme marches : [GOL-08](../../SymbolicAI/Lean/GOL/GOL-08-Loi-II-Translateur-Life.ipynb) (ex-20d)
et GOL-09 (ex-20e), tous deux dans la [sous-série GOL](../../SymbolicAI/Lean/GOL/README.md) de la
série Lean (réorg #20204) — la marche « traduire » de la carte y vit désormais.
