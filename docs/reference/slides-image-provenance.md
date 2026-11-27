# Provenance des images des decks Slidev — census (étape 0 de #28828)

REFERENCE — page **générée** : ne pas l'éditer à la main. Régénérer par

```bash
python slides/_tools/image_provenance.py
```

La table complète, une ligne par image, est dans
[`slides-image-provenance.tsv`](slides-image-provenance.tsv) ; les jugements s'écrivent dans
`slides/_tools/image_provenance_declarations.tsv`, que l'organe relit et refuse dès qu'une
ligne contredit l'arbre.

## Ce que mesure ce census

L'univers est **l'image qu'un lecteur voit** : tout fichier d'image qu'un `slides.md`
référence. Une image présente sur le disque mais montrée par aucun deck n'est pas une ligne
du census ; elle est comptée par deck, pour qu'une tranche sache ce qu'elle laisse dehors.

Sept colonnes, celles que l'EPIC demande :

| Colonne | Mesuré ou déclaré | Ce qu'elle dit |
|---|---|---|
| `image`, `deck` | mesuré | le fichier et son deck |
| `diapositive_slidev` | mesuré | les diapositives du deck qui montrent l'image |
| `diapositive_pptx` | reconstitué | la diapositive du PPTX d'origine, quand le cumul tient |
| `porteur` | mesuré | par quelle voie le fichier est entré dans l'arbre |
| `origine` | déclaré | la source nommée par le deck (texte `alt`) ou par une déclaration |
| `licence_etablie` | déclaré | `oui` seulement sur déclaration ; `non` par défaut |
| `remplacable` | déclaré | `oui` / `non` / `nc` (non tranché), jamais déduit |

## Méthode — et ce qu'elle ne mesure pas

Un `img_NNN` est un **média embarqué du PPTX**, copié par le convertisseur
`slides/_tools/pptx_to_marp.py` (retiré en #21361) depuis les médias extraits par
`slide_tools.extract_images`, lors d'un seul commit, la baseline `29531827cf9`
(679 ajouts, par aucun autre commit). Cinq `img_*` au nom descriptif sont
entrés plus tard par quatre commits (`img_pptx_52_aspirateur.png`, `img_pptx_53_belief.png`,
`img_043_local_search.png`, `img_robot_extracted.png`, `img_ga_8queens_solution.png`) :
l'organe les classe `nomme`, jamais `PPTX-media`. Ce n'est pas une découpe de page : aucun
`img_*` du deck 06 ne s'apparie aux rendus `pptx-reference/` (corrélation normalisée
maximale 0,89 sur 12 images essayées à sept échelles, pour un seuil de 0,98).

La diapositive PPTX d'origine se reconstitue en cumulant les `image_count` de
`extracted/inventory.json`. Elle n'est publiée que jusqu'au premier rang manquant sur le
disque — un fichier retiré décale tous les suivants, et l'organe préfère ne rien dire
plutôt que déplacer une image sur une mauvaise diapositive. Un deck est dit **certifié**
quand il porte exactement les `total_images` rangs de son inventaire.

**Pourquoi un deck est partiel.** Des médias sont sortis du dossier `images/` depuis la
baseline. Mesure du 27 novembre 2026 (`git ls-tree -r` de la baseline contre l'arbre) : 56 des
679 chemins ont quitté `images/`, 42 vers un autre nom à blob identique (40 du deck 01 sous
`public/images/`, 2 du deck 07 renommés), 14 retirés sans descendant (02 : 1, 08 : 3, S3 : 10).

Dans l'arbre courant, `01-introduction` en manque 2, `02-resolution-problemes` en manque 1,
`08-ia-generative` en manque 3, `S3-acculturation` en manque 12 : rangs annoncés par
l'inventaire qu'aucun fichier `img_NNN` ne porte. `rang_manquant` mesure un retrait dans l'arbre
(ou un rang jamais extrait), pas une erreur de l'organe.

Témoin à réponse connue, rejoué par `pytest tests/test_image_provenance.py -k temoin` : un mot
de contenu de l'`alt` se retrouve dans le texte de la diapositive PPTX reconstituée **118 fois
sur 189 essais**, contre **29** pour une diapositive tirée au hasard (graine 7, 6 decks
certifiés). Sans cet écart, deux erreurs de cumul pourraient se compenser sans qu'on le voie.
L'écart agrégé ne dit pas qu'il tient deck par deck :

| Deck certifié | Essais | Touches | Hasard tiré | Hasard attendu | P(≥ ces touches) au hasard | Témoin |
|---|---|---|---|---|---|---|
| `03-logique` | 43 | 33 | 9 | 6.9 | 2.3e-21 | soutient |
| `04-probabilites` | 51 | 31 | 9 | 7.5 | 2.7e-16 | soutient |
| `05-theorie-des-jeux` | 48 | 22 | 2 | 3.9 | 9.8e-15 | soutient |
| `06-apprentissage` | 11 | 8 | 2 | 2.0 | 4.2e-05 | soutient |
| `S1-argumentation` | 8 | 1 | 0 | 0.3 | 0.247 | non concluant |
| `S2-ia-exploratoire-symbolique` | 28 | 23 | 7 | 7.9 | 3.3e-14 | soutient |

« Hasard tiré » est la part de chaque deck dans les 29 du tirage au sort ; « hasard attendu »
est l'espérance exacte du même tirage ; la colonne suivante est la probabilité d'obtenir au
moins autant de touches par hasard. Le témoin **soutient** un deck tant que cette probabilité
reste au plus de 1 %.

Sur `S1-argumentation` (1 touche sur 8 essais), le témoin est **non concluant** : la
certification « PPTX » de ce deck repose sur le compte des rangs, pas sur le témoin.

**Première piste d'origine, pour une image nommée à la main** : son commit d'entrée.

```bash
git log --diff-filter=A --format='%h %ad %s' --date=short -- slides/<deck>/<chemin>
```

C'est ainsi que les déclarations déjà versées ont été établies : les six images du deck 07
viennent d'un seul commit, `554062be033`, qui les dit « from Wikimedia Commons » ; les deux
QR codes d'Argumentum encodent la même URL ; le robot du deck S3 est extrait de son PPTX
(`05cba7e95fd`). Un commit qui nomme la source établit l'origine ; il n'établit pas la
licence par fichier, et c'est la distinction que portent les deux colonnes.

**Ce que l'arbre ne porte pas** : l'auteur d'une figure et sa licence. Un média du PPTX
peut être un schéma maison comme une figure recopiée d'un manuel ; seul un texte qui nomme
sa source, ou une déclaration, l'établit. La colonne `origine` reste donc vide pour la
grande majorité, et c'est la mesure, pas un oubli.

## Résultat — un deck, une ligne

| Deck | Images référencées | Origine non établie | Origine déclarée, licence non établie | Hors EPIC | Porteurs | PPTX | Médias PPTX non montrés | Sur disque, non référencées |
|---|---|---|---|---|---|---|---|---|
| 01-introduction | 38 | 38 | 0 | 0 | PPTX-media 34, PPTX-rendu 4 | partiel (38/40) | 4 | 43 |
| 02-resolution-problemes | 58 | 58 | 0 | 0 | PPTX-media 54, nomme 4 | partiel (55/56) | 1 | 94 |
| 03-logique | 45 | 44 | 0 | 1 | PPTX-media 44, nomme 1 | certifié | 1 | 67 |
| 04-probabilites | 110 | 110 | 0 | 0 | PPTX-media 110 | certifié | 0 | 98 |
| 05-theorie-des-jeux | 48 | 48 | 0 | 0 | PPTX-media 48 | certifié | 6 | 35 |
| 06-apprentissage | 140 | 138 | 2 | 0 | PPTX-media 140 | certifié | 0 | 128 |
| 07-elargissements | 8 | 2 | 6 | 0 | PPTX-media 2, nomme 6 | — | — | 37 |
| 08-ia-generative | 33 | 33 | 0 | 0 | PPTX-media 33 | partiel (33/36) | 0 | 20 |
| 09-traitement-automatique-langues | 0 | 0 | 0 | 0 | — | — | — | 6 |
| S1-argumentation | 20 | 19 | 0 | 1 | PPTX-media 9, nomme 11 | certifié | 0 | 30 |
| S2-ia-exploratoire-symbolique | 54 | 54 | 0 | 0 | PPTX-media 54 | certifié | 0 | 54 |
| S3-acculturation | 124 | 119 | 4 | 1 | PPTX-media 122, genere 1, nomme 1 | partiel (123/135) | 1 | 64 |
| S4-trading-algorithmique | 0 | 0 | 0 | 0 | — | — | — | 243 |

**678 images référencées** : 663 d'origine non établie, 12 d'origine déclarée sans licence
établie, hors EPIC. Les fichiers d'image qu'aucun `slides.md` ne montre sont hors du census,
comptés par deck dans la dernière colonne du tableau.

**13 médias du PPTX sont sur le disque sans être montrés** par le `slides.md` de leur deck
(`05-theorie-des-jeux` en porte 6) : un lecteur du PPTX les voit, pas un lecteur du deck. Ils
ont leur propre colonne et restent compris dans « sur disque, non référencées » ; l'univers des
lignes est l'image montrée.

## La liste — images dont l'origine n'est pas établie

C'est elle qui ouvre les tranches. Une image en sort par une déclaration qui nomme son
origine **et** une licence claire.

### 01-introduction — 38 image(s)

`img_002.png`, `img_004.png`, `img_005.jpg`, `img_006.jpg`, `img_007.png`, `img_008.png`, `img_009.png`, `img_010.png`, `img_011.jpg`, `img_012.png`, `img_013.png`, `img_014.png`, `img_015.png`, `img_016.png`, `img_017.png`, `img_018.png`, `img_019.png`, `img_020.png`, `img_021.png`, `img_023.png`, `img_027.jpg`, `img_028.png`, `img_029.png`, `img_030.png`, `img_031.png`, `img_032.png`, `img_033.png`, `img_034.png`, `img_035.png`, `img_036.png`, `img_037.png`, `img_038.png`, `img_039.png`, `img_040.png`, `slide-25.png`, `slide-27.png`, `slide-28.png`, `slide-29.png`

### 02-resolution-problemes — 58 image(s)

`img_001.png`, `img_002.png`, `img_003.png`, `img_004.png`, `img_005.png`, `img_006.png`, `img_007.png`, `img_008.png`, `img_009.png`, `img_010.png`, `img_011.png`, `img_012.png`, `img_013.png`, `img_014.png`, `img_015.png`, `img_016.png`, `img_017.png`, `img_019.png`, `img_020.png`, `img_021.png`, `img_022.png`, `img_023.png`, `img_024.png`, `img_025.png`, `img_026.png`, `img_027.png`, `img_028.png`, `img_029.png`, `img_030.png`, `img_031.png`, `img_032.png`, `img_033.gif`, `img_034.png`, `img_035.png`, `img_036.png`, `img_037.png`, `img_038.png`, `img_039.png`, `img_040.png`, `img_042.png`, `img_043.png`, `img_043_local_search.png`, `img_044.png`, `img_045.png`, `img_046.png`, `img_047.png`, `img_048.png`, `img_049.png`, `img_050.png`, `img_051.png`, `img_052.png`, `img_053.png`, `img_054.png`, `img_055.png`, `img_056.png`, `img_ga_8queens_solution.png`, `img_pptx_52_aspirateur.png`, `img_pptx_53_belief.png`

### 03-logique — 44 image(s)

`img_001.png`, `img_002.png`, `img_003.png`, `img_004.png`, `img_005.png`, `img_006.png`, `img_007.png`, `img_008.png`, `img_009.png`, `img_010.png`, `img_011.png`, `img_012.png`, `img_013.png`, `img_014.png`, `img_016.png`, `img_017.png`, `img_018.png`, `img_019.png`, `img_020.png`, `img_021.jpg`, `img_022.png`, `img_023.png`, `img_024.png`, `img_025.png`, `img_026.png`, `img_027.png`, `img_028.png`, `img_029.png`, `img_030.png`, `img_031.png`, `img_032.png`, `img_033.png`, `img_034.png`, `img_035.png`, `img_036.png`, `img_037.png`, `img_038.png`, `img_039.png`, `img_040.png`, `img_041.png`, `img_042.jpg`, `img_043.png`, `img_044.png`, `img_045.png`

### 04-probabilites — 110 image(s)

`img_001.png`, `img_002.png`, `img_003.png`, `img_004.png`, `img_005.png`, `img_006.png`, `img_007.png`, `img_008.png`, `img_009.png`, `img_010.png`, `img_011.png`, `img_012.png`, `img_013.png`, `img_014.png`, `img_015.png`, `img_016.png`, `img_017.png`, `img_018.png`, `img_019.png`, `img_020.png`, `img_021.png`, `img_022.png`, `img_023.png`, `img_024.png`, `img_025.png`, `img_026.png`, `img_027.jpg`, `img_028.png`, `img_029.png`, `img_030.png`, `img_031.png`, `img_032.png`, `img_033.png`, `img_034.png`, `img_035.png`, `img_036.png`, `img_037.png`, `img_038.png`, `img_039.png`, `img_040.png`, `img_041.png`, `img_042.png`, `img_043.png`, `img_044.png`, `img_045.png`, `img_046.png`, `img_047.png`, `img_048.png`, `img_049.png`, `img_050.png`, `img_051.png`, `img_052.png`, `img_053.png`, `img_054.png`, `img_055.png`, `img_056.png`, `img_057.png`, `img_058.png`, `img_059.png`, `img_060.png`, `img_061.png`, `img_062.png`, `img_063.png`, `img_064.png`, `img_065.png`, `img_066.png`, `img_067.png`, `img_068.png`, `img_069.png`, `img_070.png`, `img_071.png`, `img_072.png`, `img_073.png`, `img_074.png`, `img_075.png`, `img_076.png`, `img_077.png`, `img_078.png`, `img_079.png`, `img_080.png`, `img_081.png`, `img_082.png`, `img_083.png`, `img_084.png`, `img_085.png`, `img_086.png`, `img_087.png`, `img_088.png`, `img_089.png`, `img_090.png`, `img_091.png`, `img_092.png`, `img_093.png`, `img_094.png`, `img_095.png`, `img_096.png`, `img_097.png`, `img_098.png`, `img_099.png`, `img_100.png`, `img_101.png`, `img_102.png`, `img_103.png`, `img_104.png`, `img_105.png`, `img_106.png`, `img_107.png`, `img_108.png`, `img_109.png`, `img_110.png`

### 05-theorie-des-jeux — 48 image(s)

`img_001.png`, `img_004.png`, `img_006.png`, `img_007.png`, `img_008.png`, `img_009.png`, `img_010.png`, `img_011.png`, `img_012.png`, `img_013.png`, `img_014.png`, `img_015.png`, `img_016.png`, `img_017.png`, `img_018.png`, `img_019.png`, `img_020.png`, `img_021.png`, `img_025.png`, `img_026.png`, `img_027.png`, `img_028.png`, `img_029.png`, `img_030.png`, `img_031.png`, `img_032.png`, `img_033.png`, `img_034.png`, `img_035.png`, `img_036.png`, `img_037.png`, `img_038.png`, `img_039.png`, `img_040.png`, `img_041.png`, `img_042.png`, `img_043.png`, `img_044.png`, `img_045.png`, `img_046.png`, `img_047.png`, `img_048.png`, `img_049.png`, `img_050.png`, `img_051.png`, `img_052.png`, `img_053.png`, `img_054.png`

### 06-apprentissage — 138 image(s)

`img_001.png`, `img_002.png`, `img_003.png`, `img_004.png`, `img_005.png`, `img_006.png`, `img_008.png`, `img_009.png`, `img_010.png`, `img_011.png`, `img_012.png`, `img_013.png`, `img_014.png`, `img_015.png`, `img_016.png`, `img_017.png`, `img_018.png`, `img_019.png`, `img_020.png`, `img_021.png`, `img_022.png`, `img_023.png`, `img_024.png`, `img_025.png`, `img_026.png`, `img_027.png`, `img_028.png`, `img_029.png`, `img_030.png`, `img_032.png`, `img_033.png`, `img_034.png`, `img_035.jpg`, `img_036.png`, `img_037.png`, `img_038.png`, `img_039.png`, `img_040.png`, `img_041.png`, `img_042.png`, `img_043.png`, `img_044.png`, `img_045.png`, `img_046.png`, `img_047.png`, `img_048.png`, `img_049.png`, `img_050.png`, `img_051.png`, `img_052.png`, `img_053.png`, `img_054.png`, `img_055.png`, `img_056.png`, `img_057.png`, `img_058.png`, `img_059.png`, `img_060.png`, `img_061.png`, `img_062.png`, `img_063.jpg`, `img_064.jpg`, `img_065.png`, `img_066.png`, `img_067.png`, `img_068.png`, `img_069.png`, `img_070.png`, `img_071.png`, `img_072.png`, `img_073.png`, `img_074.png`, `img_075.png`, `img_076.png`, `img_077.png`, `img_078.png`, `img_079.png`, `img_080.png`, `img_081.png`, `img_082.png`, `img_083.png`, `img_084.png`, `img_085.png`, `img_086.png`, `img_087.png`, `img_088.png`, `img_089.png`, `img_090.png`, `img_091.png`, `img_092.png`, `img_093.png`, `img_094.png`, `img_095.png`, `img_096.png`, `img_097.png`, `img_098.png`, `img_099.png`, `img_100.png`, `img_101.png`, `img_102.png`, `img_103.png`, `img_104.png`, `img_105.png`, `img_106.png`, `img_107.png`, `img_108.png`, `img_109.png`, `img_110.png`, `img_111.png`, `img_112.png`, `img_113.png`, `img_114.png`, `img_115.png`, `img_116.png`, `img_117.png`, `img_118.png`, `img_119.png`, `img_120.png`, `img_121.png`, `img_122.png`, `img_123.png`, `img_124.png`, `img_125.png`, `img_126.png`, `img_127.png`, `img_128.png`, `img_129.png`, `img_130.png`, `img_131.png`, `img_132.png`, `img_133.png`, `img_134.png`, `img_135.png`, `img_136.png`, `img_137.gif`, `img_138.png`, `img_139.png`, `img_140.png`

### 07-elargissements — 2 image(s)

`slide_20_img_000.png`, `slide_20_img_001.png`

### 08-ia-generative — 33 image(s)

`img_001.png`, `img_002.png`, `img_003.png`, `img_004.png`, `img_005.png`, `img_006.png`, `img_007.png`, `img_008.png`, `img_009.png`, `img_010.png`, `img_011.png`, `img_012.png`, `img_013.png`, `img_015.png`, `img_016.png`, `img_017.png`, `img_018.jpg`, `img_019.jpg`, `img_020.png`, `img_021.png`, `img_022.jpg`, `img_023.png`, `img_024.png`, `img_026.png`, `img_027.png`, `img_028.png`, `img_029.png`, `img_031.jpg`, `img_032.png`, `img_033.png`, `img_034.png`, `img_035.png`, `img_036.png`

### S1-argumentation — 19 image(s)

`aristotle_bust.jpg`, `circular_reasoning.png`, `debate_pyramid.png`, `ethos_pathos_logos.png`, `fallacy_ad_hominem.png`, `fallacy_straw_man.png`, `ibis_argument_graph.png`, `img_001.jpg`, `img_002.png`, `img_003.jpg`, `img_004.png`, `img_005.png`, `img_006.png`, `img_007.png`, `img_008.png`, `img_009.png`, `inductive_deductive.png`, `modus_barbara.png`, `toulmin_model.gif`

### S2-ia-exploratoire-symbolique — 54 image(s)

`img_001.jpg`, `img_002.png`, `img_003.png`, `img_004.jpg`, `img_005.jpg`, `img_006.png`, `img_007.jpg`, `img_008.png`, `img_009.jpg`, `img_010.jpg`, `img_011.png`, `img_012.jpg`, `img_013.png`, `img_014.png`, `img_015.png`, `img_016.png`, `img_017.png`, `img_018.png`, `img_019.png`, `img_020.png`, `img_021.png`, `img_022.png`, `img_023.png`, `img_024.png`, `img_025.png`, `img_026.png`, `img_027.png`, `img_028.png`, `img_029.png`, `img_030.png`, `img_031.png`, `img_032.png`, `img_033.png`, `img_034.png`, `img_035.png`, `img_036.png`, `img_037.png`, `img_038.png`, `img_039.png`, `img_040.png`, `img_041.png`, `img_042.png`, `img_043.png`, `img_044.png`, `img_045.png`, `img_046.png`, `img_047.jpg`, `img_048.png`, `img_049.png`, `img_050.png`, `img_051.png`, `img_052.png`, `img_053.png`, `img_054.png`

### S3-acculturation — 119 image(s)

`img_001.png`, `img_002.png`, `img_003.png`, `img_005.png`, `img_006.png`, `img_007.jpg`, `img_008.jpg`, `img_009.png`, `img_010.png`, `img_011.png`, `img_012.png`, `img_013.jpg`, `img_014.png`, `img_015.jpg`, `img_017.png`, `img_018.png`, `img_019.png`, `img_021.png`, `img_023.png`, `img_024.png`, `img_025.png`, `img_026.png`, `img_027.png`, `img_028.png`, `img_029.png`, `img_030.png`, `img_031.png`, `img_032.png`, `img_033.png`, `img_035.png`, `img_036.png`, `img_037.png`, `img_038.png`, `img_039.png`, `img_040.png`, `img_041.jpg`, `img_043.png`, `img_044.png`, `img_045.png`, `img_046.png`, `img_048.png`, `img_049.png`, `img_050.png`, `img_051.png`, `img_052.png`, `img_053.png`, `img_054.png`, `img_055.png`, `img_056.png`, `img_057.png`, `img_058.png`, `img_059.png`, `img_061.png`, `img_062.png`, `img_063.png`, `img_064.png`, `img_067.png`, `img_068.png`, `img_069.png`, `img_070.png`, `img_072.png`, `img_073.png`, `img_074.png`, `img_075.png`, `img_076.png`, `img_078.png`, `img_080.png`, `img_081.png`, `img_082.png`, `img_083.png`, `img_084.png`, `img_085.png`, `img_086.png`, `img_087.png`, `img_088.png`, `img_089.png`, `img_090.png`, `img_091.png`, `img_092.png`, `img_093.png`, `img_094.png`, `img_095.png`, `img_096.png`, `img_097.png`, `img_098.png`, `img_099.png`, `img_100.png`, `img_102.png`, `img_103.png`, `img_104.png`, `img_105.jpg`, `img_106.png`, `img_107.png`, `img_108.png`, `img_109.png`, `img_110.png`, `img_111.png`, `img_112.png`, `img_113.png`, `img_114.png`, `img_115.png`, `img_116.png`, `img_117.png`, `img_118.png`, `img_119.png`, `img_120.png`, `img_121.png`, `img_122.png`, `img_123.png`, `img_124.png`, `img_125.png`, `img_126.png`, `img_127.png`, `img_128.png`, `img_129.png`, `img_130.png`, `img_131.png`, `img_132.png`, `img_133.png`

## Origine déclarée, licence non établie

La source est nommée dans le deck ; la licence de la figure ne l'est pas. C'est le cas des
figures d'AIMA, de Russell & Norvig, de Wikipedia : remplacer la figure par une sortie de
carnet est souvent la seule voie, et la déclaration doit le dire.

### 06-apprentissage — 2 image(s)

- `images/img_007.png` (diapo Slidev 14, PPTX 14) — alt : « Pseudocode APPRENTISSAGE-ARBRE-DECISION (AIMA) »
- `images/img_031.png` (diapo Slidev 41, PPTX 40) — alt : « Pseudocode BACK-PROP-LEARNING (AIMA) »

### 07-elargissements — 6 image(s)

- `images/decision_tree_xai.png` (diapo Slidev 18) — Wikimedia Commons
- `images/federated_learning.png` (diapo Slidev 16) — Wikimedia Commons
- `images/gan_architecture.png` (diapo Slidev 29) — Wikimedia Commons
- `images/recursive_self_improvement.png` (diapo Slidev 32) — Wikimedia Commons
- `images/trolley_problem.png` (diapo Slidev 14) — Wikimedia Commons
- `images/turing_test.png` (diapo Slidev 8) — Wikimedia Commons

### S3-acculturation — 4 image(s)

- `images/img_004.png` (diapo Slidev 2, PPTX 2) — alt : « Couverture AIMA Russell & Norvig »
- `images/img_016.png` (diapo Slidev 17, PPTX 11) — alt : « Carte de la Roumanie : Arad, Sibiu, Bucharest et distances routières (exemple canonique AIMA) »
- `images/img_020.png` (diapo Slidev 19, PPTX 15) — alt : « Arbre d'exploration Arad → Bucharest (Roumanie, AIMA) — exemple canonique de recherche dans un graphe d'états »
- `images/img_robot_extracted.png` (diapo Slidev 18) — extrait du PPTX du deck S3

## Hors EPIC — origine et licence établies

Ces images sortent de l'EPIC : leur origine est déclarée et leur licence est établie.

### 03-logique — 1 image(s)

- `images/argumentum_qrcode.png` — QR code encodant https://www.argumentum.games/fallacies_fr.html ; remplaçable : nc

### S1-argumentation — 1 image(s)

- `images/argumentum_qrcode.png` — QR code encodant https://www.argumentum.games/fallacies_fr.html ; remplaçable : nc

### S3-acculturation — 1 image(s)

- `images/img_101.png` — figure generee par slides/S3-acculturation/images/gen_img_101.py ; remplaçable : nc

## Frontière du census

Ce qui n'est pas une ligne, et pourquoi :

- les **rendus de page** `pptx-reference/slide-NNN.png` que nul `slides.md` ne montre : ce
  sont des références de comparaison, pas du contenu de deck ;
- les **exports** `slidev-export/` et les **captures** `screenshots/` d'un deck qui ne les
  référence pas dans son `slides.md` ;
- les **sources `deck-*.md`** d'un deck multi-fichiers, l'énumération ne lisant que `slides.md`
  : 5 sources de ce nom sont hors census.
  Elles montrent 7 images distinctes (`S3-acculturation/deck-executif.md` 3,
  `S4-trading-algorithmique/deck-1-fondamentaux.md` 1,
  `S4-trading-algorithmique/deck-2-strategies.md` 3), dont 4 sans ligne — les autres sont déjà
  montrées par le `slides.md` de leur deck.
  Aucune n'est incluse par un `src:` d'un `slides.md` : ce ne sont pas des images qu'un lecteur
  voit, et elles entrent dans le census le jour où une source les inclut.

Reprise : `python slides/_tools/image_provenance.py --check` sort en 1 si cette page ou la
table ont dérivé de ce que l'organe produit.
