# SCIENTIFIC_REVIEW_CARD — Template de revue scientifique

**Statut** : template canonique (c.997)
**Usage** : copié/adapté par chaque reviewer qui ajoute une entrée à [scientific-review-registry.md](scientific-review-registry.md)
**Référence scope** : [scientific-review-registry.md §3.2](scientific-review-registry.md#32-portée-de-la-revue)

---

## Identification du notebook

- **Chemin relatif** : `MyIA.AI.Notebooks/<serie>/<notebook>.ipynb`
- **Titre** : `<titre du notebook>`
- **Owner logique** : `<po-XXXX ou alias>`
- **Dernière exécution vérifiée** : `<YYYY-MM-DD>`

## Portée de la revue

Cocher la portée effectivement couverte par la PR de revue (cf registre §3.2) :

- [ ] **factual** — corrections factuelles vérifiables (chiffres, dates, noms propres, théorèmes, références bibliographiques)
- [ ] **algo** — corrections algorithmiques (pseudo-code, complexité, structure)
- [ ] **proba** — corrections probabilistes (modèles, axiomes, hypothèses)
- [ ] **demo** — corrections de démonstrations mathématiques ou logiques
- [ ] **correctness** — corrections de bugs d'implémentation (off-by-one, edge case)
- [ ] **full** — toutes dimensions ci-dessus

> **Note promote** : tous les scopes ci-dessus promeuvent vers `AUTHOR_REVIEWED` si le reviewer == last_validator, ou `PEER_REVIEWED` si le reviewer ≠ last_validator (cf `classify_scientific_review` l.802-808).

## Constats

Liste des findings significatifs (1 ligne chacun) :

1. `<constat 1 — ex: cell[37] prétendait "réduction 10× speedup" mais commit af9b0cccc mesure 4.2×>`
2. `<constat 2>`
3. ...

## Verdict

- [ ] **PROMOTE_AUTHOR** — la revue justifie `scientific_reviewed_by = "<reviewer>"` et promeut `UNREVIEWED → AUTHOR_REVIEWED`
- [ ] **PROMOTE_PEER** — la revue est par un tiers distinct, promeut `UNREVIEWED → PEER_REVIEWED`
- [ ] **DEFER** — la revue nécessite une seconde passe

## Preuves (G.1 obligatoires)

- **PR de revue** : `#NNNN` (URL GitHub)
- **Commit de merge** : `<sha 7-char>` vérifié via `git log --grep="#NNNN"`
- **Diff excerpt** (1-3 lignes du diff, cellule touchée + correction) :

```
<extrait verbatim du diff git show>
```

- **Vérification croisée** : `<comment le reviewer a vérifié que la correction est vraie (ex: re-execution, calcul manuel, cross-ref manuel)>`

## Signature du reviewer

- **Reviewer** : `<login GitHub ou email>` (DOIT permettre `AUTHOR_REVIEWED` si == last_validator, ou `PEER_REVIEWED` si ≠)
- **Date de revue** : `<YYYY-MM-DD>` (ISO 8601)
- **Notes** : `<libre, max 200 chars>`

---

**Note** : ce registre est volontairement plus restrictif que `EDITORIAL_REVIEW_CARD.md` — il exige une preuve de fond technique (algo/proba/demo/correctness), pas seulement pédagogique.
