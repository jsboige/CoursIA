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
2. **Capture au canvas du scanner** (980 × 552) : c'est la taille à laquelle
   `scan_slidev_composition.py` mesure les débordements. 980 × 552 est la valeur
   **par défaut** de l'outil (`CANVAS_DEFAULT`) : aucun des quatre decks ne déclare
   `canvasWidth`, `canvasHeight` ni `aspectRatio` dans son headmatter (grep : 0
   occurrence sur les quatre `slides.md`), et `parse_headmatter_canvas` rend
   `(980, 552)` pour les quatre. Une capture à 1440 × 900 (le défaut historique
   de l'outil) ne prouve rien sur le débordement.
3. **Mesure du style calculé** : la présence d'une classe dans le DOM ne prouve
   pas qu'elle est effective — une règle ultérieure peut la neutraliser. La
   taille de police de la liste ciblée est donc relevée au rendu.
4. **Comparaison à l'original PPTX** par **titre** (jamais par un décalage
   supposé) : les titres de l'original sont lus dans
   `extracted/inventory.json` (deck 02) ou dans le PDF de référence (decks 06, S3).
5. **Scan de composition** (`scan_slidev_composition.py`) sur les quatre decks.

### Instruments — la chaîne est entière et rejouable

| Étape | Instrument | Sortie |
|---|---|---|
| 1. parcours du DOM rendu | `slides/_tools/render_deck.py --match --manifest` | `match3/<deck>.json` |
| 2. association à l'original PPTX | `slides/_tools/map_pptx.py` | `match2/<deck>.map.json` |
| 3. scan de composition | `scripts/notebook_tools/scan_slidev_composition.py` | `composition-<deck>.json` |
| 4. assemblage | `slides/_tools/build_capture_manifest.py` | `manifest.json` + ce README |

`manifest.json` n'est donc pas produit à la main : c'est la sortie de l'étape 4,
qui se rejoue sur les mêmes entrées — et le rejeu restitue le fichier commité
**à l'octet près** :

```
python slides/_tools/build_capture_manifest.py --sp <repertoire-de-travail> \
       --out docs/captures/22286
```

## Résultat — les classes portent-elles au rendu ?

Oui, sur les 52 diapositives capturées : `dense-list` est portée par 49
d'entre elles, `xl-dense` par 5 (deck 06), `img-fit` par 6 — 3 diapositives
ne portent qu'`img-fit`. Les tailles relevées au rendu se lisent ainsi :

- **14,76 px** (interligne 18,01 px) — la liste dense du thème (0,82 em sur une
  base de 18 px) ;
- **12,96 px** (interligne 14,52 px) — `xl-dense` du thème (0,72 em) ;
- **12,30 px** (interligne 15,01 px) — 0,82 em sur une base de 15 px : c'est la
  **valeur du thème**, relevée sur six diapositives du deck 06 (34, 59, 70, 71,
  73, 109), et non une mesure du deck S3 ;
- **12,04 px** (diapositive 23) et **15,48 px** (diapositive 41) — les deux
  seules diapositives mesurées du deck S3, à **0,86 em** : la déclaration propre
  de `slides/S3-acculturation/style.css` prime sur celle du thème (chargée après,
  à spécificité égale), ce que confirme le rapport 12,04 / 0,86 = 14 px et
  15,48 / 0,86 = 18 px.

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

## Résultat — débordements au canvas du scanner

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

### Comparaison avec #22318 (2026-10-25)

#22318 mesurait les mêmes decks, au même canvas, avec HORS = 3 (02), 13 (06),
0 (S3), 2 (S8) ; la mesure portée ici donne 1, 13, 0, 1.

| Deck | #22318 | Ici | Écart | Cause |
|---|---|---|---|---|
| 02 — Résolution de problèmes | 3 | 1 | 3 → 1 | Contenu |
| 06 — Apprentissage | 13 | 13 | 13 → 13 | Aucun écart |
| S3 — Acculturation | 0 | 0 | 0 → 0 | Aucun écart |
| S8 — Web sémantique | 2 | 1 | 2 → 1 | Non expliqué par l'arbre |

- **02 — Résolution de problèmes** — Contenu : `slides/02-resolution-problemes/slides.md` a été réparé après #22318 (#11508 le 2026-10-29, puis #23183 le 2026-10-30).

**Deck S8 — l'écart 2 → 1 n'est pas imputable au contenu.** Mesuré à la source :

- `slides/S8-semantic-web/slides.md` : dernier commit `ad8b546e` (2026-08-28) ;
- `slides/S8-semantic-web/style.css` : dernier commit `f1f9e29a` (2026-08-25) ;
- le thème (`slides/theme-ia101/styles/index.css`) : dernier commit `3f95ed405`
  (2026-10-25), c'est-à-dire #22318 lui-même ;
- l'instrument (`scripts/notebook_tools/scan_slidev_composition.py`) : dernier
  commit `77e987e17` (2026-09-15), donc antérieur à #22318.

Aucune de ces modifications n'explique 2 → 1, et le scan rejoué sur cette machine
redonne **1** (diapositive 16), identique au scan archivé dans `manifest.json`.
À l'inverse, le « 2 » de #22318 n'est **ni reproductible ici ni décomposable** :
#22318 ne commite aucun relevé de scan, et son corps ne nomme, pour S8, que la
diapositive 22 — qu'il déclare à *zéro* élément hors canvas au relevé DOM.

La variable restante est **l'environnement de mesure** : les deux relevés n'ont pas
été produits sur la même machine (#22318 par la lane `myia-ai-01`, celui-ci par la
lane `myia-po-2028`), et le rendu Slidev ne dépend que des polices **système**
(`font-family: 'Segoe UI', 'Calibri', Arial, sans-serif`, aucune `@font-face`
dans `slides/`), donc les métriques de texte diffèrent d'une machine à l'autre.
Un compteur de débordement n'est ainsi **pas opposable d'une machine à l'autre** :
la conclusion « aucun deck n'en gagne » ne vaut que pour les decks dont l'écart
est content-expliqué, et **le seul chiffre opposable aujourd'hui est celui mesuré
sur cette machine** : un débordement réel sur S8 (diapositive 16, 4 constats).

Le compteur `n_occupation_flagged` (24 pour 02, 5 pour S3) est **advisory** :
le scanner le signale sans le compter dans son code retour. Il valait 23 (02)
et 3 (S3) dans #22318 ; l'écart porte sur un indicateur que le scanner déclare
lui-même bruité d'un run à l'autre.

## Suite — le relevé devenu opposable (#24171)

Le point ci-dessus — *un compteur n'est pas opposable d'une machine à l'autre* —
n'a pas reçu de réponse par l'embarquement de polices dans le dépôt (choix de
licence qui dépasse ce lot), mais par l'**artefact versionné** : le scanner
`scripts/notebook_tools/scan_slidev_overflow.py` sait désormais écrire son
relevé sous forme d'artefact (hash de chaque image mesurée, empreinte de la
machine, empreinte de contenu) et **comparer deux artefacts** au lieu de
rejouer un compteur. Le premier relevé de rendu produit sous cette forme, sur
le deck `06-apprentissage`, est dans [`docs/captures/24171/`](../24171/README.md)
— avec les **deux contraintes d'export** que cette documentation ne portait pas
et qui font échouer une mesure deck par deck (`--range` obligatoire ;
`--output` effacé à chaque invocation).

## Contenu du dossier

```
manifest.json   mesures brutes (une entrée par diapositive capturée)
<deck>/         captures PNG, 980x552, une par diapositive capturée
contact-*.png   planches de comparaison : rendu Slidev | original PPTX
```

Les planches de comparaison associent chaque diapositive à son original par
titre ; l'en-tête de chaque paire porte les deux index.
