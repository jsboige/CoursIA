# EDITORIAL_REVIEW_CARD — Template de revue éditoriale

**Statut** : template canonique (c.764)
**Usage** : copié/adapté par chaque reviewer qui ajoute une entrée à [editorial-review-registry.md](editorial-review-registry.md)
**Référence scope** : [editorial-review-registry.md §3.1](editorial-review-registry.md#3-curation-rules-hard)

---

## Identification du notebook

- **Chemin relatif** : `MyIA.AI.Notebooks/<serie>/<notebook>.ipynb`
- **Titre** : `<titre du notebook>`
- **Owner logique** : `<po-XXXX ou alias>`
- **Dernière exécution vérifiée** : `<YYYY-MM-DD>`

## Portée de la revue

Cocher la portée effectivement couverte par la PR de revue (cf registre §3.1 #5) :

- [ ] **typo** — corrections orthographiques/typographiques uniquement (NE promeut PAS `BETA → FINAL`, cf §3.2)
- [ ] **factual** — corrections factuelles vérifiables (chiffres, dates, noms propres, théorèmes, références bibliographiques)
- [ ] **pedagogie** — restructuration pédagogique (ordre cellules, transitions markdown, ajout d'indices)
- [ ] **substance** — corrections de fond (algorithme, équation, raisonnement, démonstration)
- [ ] **full** — les 4 dimensions couvertes

> **Note promote** : seuls `factual`, `substance`, `full` permettent la promotion `BETA → FINAL`. Les `typo` et `pedagogie` sont cumulables mais insuffisants seuls.

## Constats

Liste des findings significatifs (1 ligne chacun) :

1. `<constat factuel 1 — ex: cell[37] prétendait "BDD reduction 10× speedup" mais commit af9b0cccc mesure 4.2×>`
2. `<constat factuel 2>`
3. ...

## Verdict

- [ ] **PROMOTE** — la revue justifie `editorial_reviewed_by = "<reviewer>"` et promeut `BETA → FINAL`
- [ ] **DO_NOT_PROMOTE** — la revue est légitime mais scope insuffisant (typo/pedagogie seule) ou auto-review
- [ ] **DEFER** — la revue nécessite une seconde passe (par exemple, parce que les corrections factuelles touchent à la substance algorithmique)

## Preuves (G.1 obligatoires)

- **PR de revue** : `#NNNN` (URL GitHub)
- **Commit de merge** : `<sha 7-char>` vérifié via `git log --grep="#NNNN"`
- **Diff excerpt** (1-3 lignes du diff, cellule touchée + correction) :

```
<extrait verbatim du diff git show>
```

- **Vérification croisée** : `<comment le reviewer a vérifié que la correction est vraie (ex: re-execution, calcul manuel, cross-ref manuel)>`

## Signature du reviewer

- **Reviewer** : `<login GitHub ou email>` (DOIT ≠ owner_logique du notebook)
- **Date de revue** : `<YYYY-MM-DD>` (ISO 8601)
- **Notes** : `<libre, max 200 chars>`

---

## Exemple rempli (issu du pilote Sudoku c.764)

Pour référence, voici à quoi ressemble une carte remplie pour l'entrée `Sudoku-12-Z3-Csharp.ipynb` :

```markdown
## Identification du notebook
- Chemin relatif : `MyIA.AI.Notebooks/Sudoku/Sudoku-12-Z3-Csharp.ipynb`
- Titre : `Sudoku-12 : Résolution avec Z3 (C#)`
- Owner logique : `po-2023`
- Dernière exécution vérifiée : 2026-07-22

## Portée de la revue
- [x] factual

## Constats
1. cell[37] prétendait "Z3 entier plus rapide que backtracking sur les grilles faciles" — mesure commit 15b855bb6 montre contraire
2. cell[40] prétendait "Z3 et backtracking se valent sur les grilles dures" — alignement OK après correction

## Verdict
- [x] PROMOTE

## Preuves
- PR de revue : #7801
- Commit de merge : 15b855bb6
- Diff excerpt : `docs(sudoku): reconcile 'entier plus rapide facile' + 'se valent' with committed benchmark`
- Vérification croisée : re-execution de la cellule benchmark par reviewer, sortie confirme

## Signature
- Reviewer : `jsboigeEpita`
- Date : 2026-07-22
- Notes : `fix(sudoku,#3801): reconcile 'entier plus rapide facile' + 'se valent'`
```
