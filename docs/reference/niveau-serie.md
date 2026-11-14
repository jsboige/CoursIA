# Règle de niveau de série — quand un dossier mérite d'exister

> REFERENCE — vivante — dernière révision 2026-11-14

**S'applique à** : toute création, suppression ou renommage d'un dossier porteur de carnets sous `MyIA.AI.Notebooks/`.
**Origine** : issue #24197 (« Curriculum : consistance et clarté des séries », mandat direct du mainteneur du 2026-11-02), sections B et C. Son livrable 2 demande « une règle de niveau, courte et citable, pour B et pour C ».
**Voisins** : [finition-de-serie.md](finition-de-serie.md) (quand une série cesse de grossir) · [catalog_markers.md](catalog_markers.md) (les marqueurs de catalogue ne se réécrivent pas à la main).

## Le flou que la règle tranche

Trois formes de flou se ressemblent et n'appellent pas le même remède :

1. **un dossier qui se présente comme une série et ne contient qu'un carnet** — il faut dire pourquoi il existe, ou le replier ;
2. **un carnet posé à la racine d'une série, sans dossier** — il faut dire à quel arc il appartient, ou lui donner son niveau ;
3. **deux séries jumelles** (le même plan enseigné sur deux moteurs) — il faut dire laquelle est canonique et laquelle est une variante déclarée.

## Règle 1 — le dossier qui ne contient qu'un carnet

Un tel dossier **est conservé** si, et seulement si, l'une de ces trois choses est écrite dans **son propre README** :

- un **plan daté** — les carnets suivants sont nommés (titre et sujet), même sans date de livraison ;
- une **raison de niveau** — le carnet porte un sujet, un jeu de données ou un moteur qui n'appartient à aucune sous-série existante, et cette raison tient en une phrase ;
- un **statut de pas** — le dossier est déclaré comme une étape d'un parcours, et son README renvoie à l'arc qui l'ordonne au lieu de se présenter comme une série.

Sinon, le carnet **replie** : il rejoint la sous-série ou la racine qui l'accueille, et le dossier disparaît.

Le test est volontairement peu coûteux : trois phrases suffisent à garder un dossier. Ce qui est refusé, c'est le **silence** — un dossier qui a l'air d'une série sans jamais dire pourquoi.

## Règle 2 — le carnet qui n'a pas de dossier

Un carnet posé à la racine d'une série est **légitime** quand le README de cette série le cite dans son arborescence et l'inscrit dans un arc ; sinon il est replié dans la sous-série qui l'accueille.

Une série **plate** — tous ses carnets à la racine, sans dossier intermédiaire — n'est pas un défaut : c'est un choix de niveau, et il se dit. Le README de la série annonce que la série est plate et dit pourquoi (le sujet est commun, la numérotation est continue, aucun sous-arc ne se dessine).

> État (mesuré sur `origin/main` au 2026-11-13) : les séries plates sont **Sudoku** (39/39 carnets à la racine), **Complexity** (26/26) et **NLP** (12/12) ; les trois déclarent leur platitude dans leur README. RL (29/40 à la racine + sous-série PostTraining) et GameTheory (101/142 + sous-séries) ne sont pas plates — leur structure est déclarée par leurs sous-séries, la règle 2 ne leur demande rien.

## Règle 3 — la série jumelle

Deux séries qui enseignent le même plan sur deux moteurs ne sont pas une duplication tant que le dépôt **le déclare** : le README de chacune nomme **la série canonique** et **la variante déclarée**, et dit en une phrase ce qui diffère (le moteur, le format des entrées, l'API).

Sans cette déclaration, un correcteur qui touche une jumelle ne sait pas qu'il doit toucher l'autre, et un lecteur croit à une duplication.

## La mesure, et pourquoi le compte dépend de la convention

Le recensement est une **mesure**, pas un littéral : il se recalcule avec la commande ci-dessous, et le résultat dépend de ce qu'on appelle « dossier feuille ». Trois conventions coexistent et ne donnent pas le même chiffre pour la même question — c'est la première chose à écrire quand on annonce un compte.

```bash
git ls-tree -r origin/main --name-only -- MyIA.AI.Notebooks/ \
  | grep -E '\.ipynb$' | grep -v '_output\.ipynb$'
```

Sur `origin/main` au 2026-11-03, avec cet instrument :

| convention | ce qu'elle compte | résultat |
|---|---|---|
| dossier porteur | un dossier qui contient au moins un carnet | 257 |
| dossier feuille | un dossier porteur **sans** sous-dossier porteur | 233 |
| dossier feuille à un seul carnet | parmi les précédents, ceux qui n'en tiennent qu'un | 105 |

L'issue #24197 annonce « 35 répertoires feuilles à un carnet » avec cet instrument : le même instrument sur l'arbre courant ne produit pas ce chiffre, et aucune des trois conventions ci-dessus n'y conduit. Les candidats qu'elle liste sont les **sous-séries de premier niveau** (plus les carnets à la racine d'une série), c'est-à-dire un **sous-ensemble filtré**, et non l'inventaire que l'instrument produit. **La règle ci-dessus ne dépend d'aucun compte** : elle se tranche dossier par dossier, par lecture.

## Les décisions de la section B de #24197

État au 2026-11-03, décisions écrites dossier par dossier. Le « pourquoi » tient dans la colonne « raison de niveau » ; le « où » est la destination du déplacement.

| cas | décision | destination | raison de niveau | état |
|---|---|---|---|---|
| `Probas/Probas-CLT-Theoreme-Central-Limite.ipynb` | promouvoir | `Probas/Fondations/` | le théorème central limite est la base mathématique **commune** aux deux stacks ; il n'appartient ni à `Infer/` ni à `PyMC/` | fait (PR section B #24197, 2026-11-07) |
| `Probas/Probas-MCMC-Echantillonnage-Metropolis-Python.ipynb` | promouvoir | `Probas/Fondations/` | l'échantillonnage est le socle commun des deux stacks, pas un carnet de moteur | fait (PR section B #24197, 2026-11-07) |
| `Probas/Probas-KLS-Concentration.ipynb` | replier | `Probas/Applications/` | application autonome de la géométrie log-concave, sœur de `Quotients-Fibres-Recollement-Python` ; ses prérequis (`Infer-03`, `PyMC-14`) en font un carnet d'application, pas un socle | fait (PR section B #24197, 2026-11-07) |
| `Probas/Applications/Quotients-Fibres-Recollement-Python.ipynb` | requalifier | reste à la racine d'`Applications/` | le README de `Probas/` le nomme déjà comme application autonome ; la règle 2 s'applique | sans blocker |
| `Probas/Applications/Pyro_RSA_Hyperbole.ipynb` | requalifier | reste à la racine d'`Applications/` | idem ; l'absorption d'audit est en cours | PR #24328 ouverte |

Une décision qui n'est pas encore prise s'écrit **comme telle** — elle ne se laisse pas implicite. Le tableau ci-dessus est la source de vérité de l'avancement de la section B ; il se met à jour au fil des tranches.

## Ce qui ne change pas

- **Aucun renommage de carnet sans argument pédagogique écrit** ([notebook-accretion-numbering](../../.claude/rules/notebook-accretion-numbering.md)).
- **Le catalogue appartient à l'automatisation** : `COURSE_CATALOG.generated.*` et les blocs `CATALOG-STATUS` ne se réécrivent jamais à la main sur une branche.
- **Les README de séries se mettent à jour dans la même PR** que le rangement, sinon la navigation pointe vers un dossier qui n'existe plus.
- **Un déplacement de carnet impose la ré-exécution** à l'emplacement nouveau : il change la résolution `cwd` des chemins relatifs et les déclarations de chemin.
