# Preuve de rendu — issue #22286 (classes `dense-list` / `xl-dense` / `img-fit`)

Ce dossier est la **jambe de rendu** de l'issue #22286 : la consolidation CSS
est sur `main` (#22318), il manquait la preuve visuelle que les classes portent
au rendu des decks `02-resolution-problemes`, `06-apprentissage`, `S3-acculturation`
et `S8-semantic-web`.

## Méthode

1. **Sélection par le DOM rendu**, pas par le source : un deck Slidev est parcouru
   par `window.__slidev__.nav.go(i)` et une diapositive est retenue si sa page
   `.slidev-page[data-slidev-no]` contient l'un des sélecteurs. L'indexation du
   markdown est décalée (frontmatter par diapositive, fences) — mesurée : 99
   diapositives au split naïf contre 88 rendues pour le deck 02.
2. **Capture au canvas déclaré** (980×552, lu dans le headmatter du deck) : c'est
   la taille à laquelle `scan_slidev_composition.py` mesure les débordements.
   Une capture à 1440×900 (le défaut historique de l'outil) ne prouve rien sur
   le débordement.
3. **Mesure du style calculé** : la présence d'une classe dans le DOM ne prouve
   pas qu'elle est effective — une règle ultérieure peut la neutraliser. La
   taille de police de la liste ciblée est donc relevée au rendu.
4. **Comparaison à l'original PPTX** par **titre** (jamais par un décalage
   supposé) : les titres de l'original sont lus dans
   `extracted/inventory.json` (deck 02) ou dans le PDF de référence (decks 06, S3).
5. **Scan de composition** (`scan_slidev_composition.py`) sur les quatre decks.

Instrument : `slides/_tools/render_deck.py` (mode `--match`, `--manifest`).

## Résultat — les classes portent-elles au rendu ?

Oui, sur les 52 diapositives capturées : `dense-list` est portée par 49
d'entre elles, `xl-dense` par 5 (deck 06), `img-fit` par 6 — 3 diapositives
ne portent qu'`img-fit`. Les tailles de police relevées au rendu sont celles des
déclarations mesurées : 14,76 px pour la liste dense du theme (0,82 em),
12,96 px pour `xl-dense` (0,72 em), 12,30 px et 15,48 px pour S3 dont les
déclarations propres priment sur celles du theme.

## Résultat — la comparaison à l'original PPTX

| Deck | Diapositives capturées | Original PPTX trouvé | Sans original (ajout du port) |
|---|---|---|---|
| 02 — Résolution de problèmes | 9 | 9 | 0 |
| 06 — Apprentissage | 32 | 29 | 3 |
| S3 — Acculturation | 2 | 2 | 0 |
| S8 — Web sémantique | 9 | 0 | 9 |

Le deck **S8 n'a pas de référence PPTX** (pas de dossier `pptx-reference`) : ses
diapositives sont capturées et contrôlées, mais sans comparaison possible.
Les diapositives du deck 06 listées « sans original » sont des ajouts du port
(le PDF de référence ne contient pas ces titres).

## Résultat — débordements au canvas déclaré

Le scan de composition donne, sur la tête courante :

| Deck | Diapositives | HORS_CANVAS | CHEVAUCHEMENT | OCCUPATION | RECOUVREMENT |
|---|---|---|---|---|---|
| 02 — Résolution de problèmes | 88 | 1 | 0 | 24 | 0 |
| 06 — Apprentissage | 124 | 13 | 0 | 10 | 0 |
| S3 — Acculturation | 105 | 0 | 0 | 5 | 0 |
| S8 — Web sémantique | 28 | 1 | 0 | 0 | 0 |

Parmi les diapositives capturées, celles qui débordent **réellement** du canvas
(les constats dont le conteneur n'est pas la seule cause sont comptés) :

| Deck | Diapositive | Titre | Constats |
|---|---|---|---|
| 02 | 48 | Exploration locale d’espaces continus | 5 |
| 06 | 34 | Méthodes d’ensemble | 2 |
| 06 | 40 | Réseaux feed-forward multi-couches | 5 |
| 06 | 42 | Mise en œuvre de la rétropropagation | 2 |
| 06 | 53 | Graphs Neural Networks (GNNs) | 8 |
| 06 | 103 | Apprentissage des différences temporelles | 5 |
| 06 | 112 | Minimisation de regret hypothétique | 4 |
| S8 | 16 | SW-8 — SHACL : Validation des Données RDF | 4 |

Ces débordements sont **préexistants** : #22318 mesurait, sur les mêmes decks et
au même canvas, HORS = 3 (02), 13 (06), 0 (S3), 2 (S8). La mesure à la tête
courante donne 1, 13, 0, 1 — **aucun deck n'en gagne** (06 : compte identique ;
02 et S8 : compte plus faible, l'écart venant des PRs qui ont modifié ces decks
depuis). #22318 documente par ailleurs que l'aggravation de 2 à 10 px sur trois
diapositives du deck 06, détectée pendant la consolidation, a été **corrigée**
par report des interlignes dans le thème, et que la diapositive 48 du deck 02
a été **améliorée** (bloc 599 → 585 px, débordement 57 → 48 px).

Le compteur `n_occupation_flagged` (24 pour 02, 5 pour S3) est **advisory** :
le scanner le signale sans le compter dans son code retour. Il valait 23 (02)
et 3 (S3) dans #22318 ; l'écart porte sur un indicateur que le scanner déclare
lui-même bruité d'un run à l'autre.

## Contenu du dossier

```
manifest.json   mesures brutes (une entrée par diapositive capturée)
<deck>/         captures PNG, 980x552, une par diapositive capturée
contact-*.png   planches de comparaison : rendu Slidev | original PPTX
```

Les planches de comparaison associent chaque diapositive à son original par
titre ; l'en-tête de chaque paire porte les deux index.

