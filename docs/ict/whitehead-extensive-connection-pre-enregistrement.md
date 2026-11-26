# Pré-enregistrement — Whitehead, *Process and Reality* IV.II, connexion extensive (case 28 : quelles hypothèses tiennent dans tout modèle, quelles ne tiennent que dans un modèle choisi)

> **Grade C explicite.** Ce document **scelle** le protocole de la tranche Whitehead de la veille [#8182](https://github.com/jsboige/CoursIA/issues/8182) **AVANT toute écriture du banc de mesure** — même discipline que les cases 18, 19, 21-22, 23-25 : source primaire lue et archivée, pré-enregistrement commité avant l'implémentation et la mesure, verdict borné. Le banc (`ict/whitehead_extensive_connection.py`) vient dans un commit fils — la relation de parenté des commits porte l'antériorité (leçon case 8c).
>
> **Cycle du 2026-11-26**, lane `myia-po-2023:CoursIA`. Claim : `[CLAIMED]` sur [#8182](https://github.com/jsboige/CoursIA/issues/8182) (c.7183877069), clause `paths:` bornée aux cinq fichiers de la tranche.
>
> **Ce que la tranche répond.** Une note antérieure de la veille écartait Whitehead comme « œuvre ancienne, domaine public mais pas falsifiable en jouet CPU ». La seconde moitié de cette note est fausse, et le chapitre visé le montre : IV.II n'est pas un essai mais **un système formel** — 24 définitions et 31 hypothèses numérotées, dont l'auteur dit lui-même qu'elles sont « some provable and some axiomatic » (p. 459) et qu'il ne cherche pas à les réduire à un minimum logique (p. 450). Un système formel se vérifie hypothèse par hypothèse sur des substrats explicites. C'est cette tranche.

## 1. Source primaire et archivage

**Source** : Alfred North Whitehead, *Process and Reality — An Essay in Cosmology*, Gifford Lectures, University of Edinburgh, session 1927-28, The Macmillan Company, New York, 1929. Texte de la première édition, pagination d'origine (le tirage consulté est le cinquième, 1960, mais le texte est celui de 1929). Domaine public aux États-Unis depuis le 1er janvier 2025 (publication 1929 + 95 ans ; renouvellement de 1957, « Copyright renewed 1957 by Evelyn Whitehead »).

**Archivage gisement** ([bibliography-hygiene](../../.claude/rules/bibliography-hygiene.md)) : `G:\Mon Drive\MyIA\IA\Bibliographie IA\Consciousness\1929 - Whitehead - Process and Reality - An Essay in Cosmology (Gifford Lectures Edinburgh 1927-28, Macmillan New York, texte de la 1re edition, 5e tirage 1960, domaine public US depuis 2025, IA processrealityes0000unse).pdf` — 21 132 402 octets, SHA-256 `a74f45e4a10195ebf3cbbf05fff9c8ba2ac79dce77bdc164567ae5f522a4d533`, identique à l'octet au fichier servi par l'item Internet Archive `processrealityes0000unse` (LCCN 29023503, « xii, 547 pages », 566 images). Recherche par auteur ET titre avant dépôt : aucune autre copie de Whitehead au gisement, le rayon `Consciousness` en porte exactement une.

**Identité vérifiée** : sur la couche texte de l'item (même scan) — « PROCESS AND REALITY / AN ESSAY IN COSMOLOGY / Gifford Lectures Delivered in the University of Edinburgh During the Session 1927-28 / BY ALFRED NORTH WHITEHEAD … The Macmillan Company, New York / Copyright, 1929 … Fifth Printing, 1960 ».

**Limite de méthode, déclarée** : la page du PDF archivé **n'a pas été rendue localement** (`pdftoppm` absent de la machine ; `fitz` et `pypdf` absents de l'interpréteur système). L'identité a donc été lue sur la couche OCR du même scan, et la taille de l'archive confrontée au manifeste de l'item — pas sur une image de page. Toute citation ci-dessous vient de cette couche texte, contrôlée sur les deux scans indépendants que l'item expose (`processrealityes0000unse` et `processrealityes00whit_1`).

**Ce que la lecture a corrigé chez moi** : je croyais me souvenir des titres de sections de l'édition corrigée. Les titres lus dans la table de 1929 sont : ch. I « Coordinate Division », ch. II « Extensive Connection » (I. General Description · II. Assumptions, i.e. Postulates, i.e. Axioms and Propositions for a Deductive System · III. Extensive Abstraction, Geometrical Elements, Points, Segments · IV. Points, Regions, Loci; Irrelevance of Dimensions), ch. III « Flat Loci », ch. IV « Strains », ch. V « Measurement ». Le quatrième point de la table — « Irrelevance of Dimensions » — est précisément ce que la prédiction P5 met à l'épreuve.

## 2. Le cadre en deux phrases

L'extension n'est pas première chez Whitehead, la **connexion extensive** l'est : « For Descartes the primary attribute of physical bodies is extension; for the philosophy of organism the primary relationship of physical occasions is extensive connection. This ultimate relationship is *sui generis*, and cannot be defined or explained. But its formal properties can be stated » (p. 441). Le chapitre II fait exactement cela : il pose la connexion comme relation première entre **régions**, en dérive l'inclusion (D2, « due to Professor de Laguna »), l'overlap (D3), la dissection (D4), l'intersect (D5), la connexion externe et l'inclusion tangentielle (D7-D9), puis reconstruit **point, segment et lieu** non pas comme des individus premiers mais comme des classes d'ensembles abstractifs convergents (D10-D16).

**La question que l'auteur laisse ouverte, et qui est la nôtre** : « it is difficult to draw the line distinguishing characteristics so general that we cannot conceive any alternatives, from characteristics so special that we imagine them to belong merely to our cosmic epoch » (p. 442) — et, deux pages avant, la licence d'un espace à « three hundred and thirty-three dimensions ». Le chapitre affirme donc deux choses distinctes : (i) ces hypothèses décrivent la connexion extensive en général ; (ii) certaines au moins ne valent que pour notre époque cosmique. **La tranche sépare (i) de (ii) par la mesure** : on instancie la connexion dans plusieurs substrats, on évalue chaque hypothèse dans chacun, et la partition tombe — nécessaire sur la famille (vraie partout) *vs* d'époque (fausse quelque part).

## 3. La question falsifiable

**Le système à vérifier** — tel qu'imprimé, pp. 450-457, lu intégralement : définitions **D1** (connexion médiate), **D2** (inclusion), **D3** (overlap), **D4** (dissection), **D5** (intersect), **D6.1** (intersection unique / multiple), **D7** (connexion externe), **D8** (inclusion tangentielle), **D9** (inclusion non tangentielle), **D10** (ensemble abstractif), **D11** (couvrir), **D12** (équivalence), **D13** (élément géométrique), **D14** (associé), **D15** (incident), **D16** (point) ; hypothèses **A1-A12, A15-A26** — **24 hypothèses** (la numérotation imprimée saute 13 et 14 ; l'écart apparaît à l'identique sur les deux scans indépendants, il est donc une propriété du texte imprimé, pas un artefact d'OCR — je ne bâtis rien dessus).

**Hors périmètre, tranche suivante** : A27-A33 et D16A, D17-D24 (segments, extrémités, points situés, surfaces, volumes, lieux complets). Ces énoncés exigent une relation d'ordre entre points et des lieux infinis ; les mêler ici doublerait le banc sans changer la question posée.

**La question** : parmi les 24 hypothèses, lesquelles sont **satisfaites dans tout substrat de la famille** (nécessaires au sens faible : aucune alternative trouvée parmi les cinq familles), et lesquelles **admettent un contre-exemple** (elles ne décrivent alors pas la connexion extensive en général, mais une géométrie particulière — celle de notre époque, ou celle d'une convention de frontière) ?

**Relation aux cases existantes** (anti-duplication). Les cases 13-27 testent des **thèses empiriques** sur la conscience (combinaison, décombinaison, accès relativiste, Orch-OR, émergence causale) : leur objet est un prédicat sur un système. La case 28 change d'objet : elle teste **l'appareil formel** qui sert de toile de fond à ces thèses — la géométrie de l'extension elle-même. Aucune case existante n'évalue des axiomes ; aucun module `ict/` n'implémente de méréotopologie (les plus proches, `basin_geometry.py`, `factor_geometry*.py`, `geometry_contrast.py`, `workspace.py`, manipulent des géométries de **représentation** — distances, angles, partitions — jamais une relation de connexion entre régions avec inclusion dérivée). La case 28 n'invoque donc aucun organe et n'en réimplémente aucun : elle n'a pas de prédécesseur. Elle partage avec la série la forme (seuil scellé, substrat jouet, graines disjointes), pas la matière.

**Les lectures retenues, déclarées avant mesure.** Deux énoncés imprimés ne peuvent pas être lus au pied de la lettre ; les lemmes L1 et L2 le prouvent (section 4). Le banc adopte donc deux conventions, et les mesure comme telles :

- **K1 — irréflexivité conventionnelle.** C et la connexion médiate sont irréflexives par convention de nomenclature (le texte le dit de A4 : « merely a convenient arrangement of nomenclature »). La lecture littérale est traitée en L2, pas dans la matrice.
- **K2 — inclusion (v1, remplacée par K2′ en v2 : voir §8).** `A ⊒ B` ssi *(toute région connectée avec B est connectée avec A)* **et** `A ≠ B`. E1 est l'émendation minimale de D2 : elle rend A7 satisfiable (L1) sans rendre A5 vacueux (A5 reste une thèse à mesurer, non un corollaire de la définition).
- **K3 — tautologies déclarées.** A21 (équivalence réflexive) et A26 (non-incidence en soi) sont des conséquences de D12 et D15 (« merely a convenient arrangement of nomenclature ») : le banc les compte vraies et les marque **par définition**, jamais « mesurées ». A1 est mesuré pour sa moitié « connexion » et **prouvé** pour sa moitié « connexion médiate » (le texte le dit, p. 451 : « can be proved from the terms of the definition »).
- **K4 — « any two regions » = paires distinctes** (A2, seconde clause). Sans cela A2 et A4 sont contradictoires (L2).

## 4. Prédictions scellées (case 28)

### Substrats

Cinq familles, toutes en **arithmétique rationnelle exacte** (`fractions.Fraction` dans la bibliothèque standard) : aucun flottant n'intervient dans une décision vraie/faux. Une décision exacte vaut pour la batterie finie que le banc énumère ; elle ne vaut pas preuve sur la famille entière — c'est la limite 1 de la section 6, et les quatre énoncés qui *sont* prouvables sont isolés en L1-L4.

| # | régions | connexion `C(A,B)` | inclusion (D2 dérivée) | rôle |
|---|---|---|---|---|
| **S1** `closed` | unions finies d'intervalles fermés rationnels `[a,b]`, `a<b`, deux à deux séparés, `d=1` | `A ∩ B ≠ ∅` | inclusion ensembliste | modèle candidat |
| **S2** `open` | unions finies d'intervalles ouverts rationnels `(a,b)`, `d=1` (contacts d'extrémités permis) | adhérences sécantes | inclusion des adhérences | discerne la convention de frontière |
| **S3** `atomic` | sous-ensembles non vides de `{0..5}` | `A ≠ B` et `∃c∈A, c'∈B : abs(c − c') ≤ 1` | D2 dérivée, puis E1 | substrat atomique (témoin A9, A2) |
| **S4** `boxes_dN` | boîtes fermées uniques rationnelles `∏[lo_i,hi_i]`, `N ∈ {1,2,3,4}` | intersection non vide | inclusion coordonnée à coordonnée | invariance de dimension (p. 442) |
| **S5** `tree` | nœuds de profondeur 1..3 de l'arbre binaire complet (racine exclue) | imbrication stricte (préfixe) | D2 dérivée, puis E1 | témoin de structure arborescente |

**Batterie** : S1/S2 — 40 régions construites sur la grille de coupures rationnelles `{0, 1/3, 1/2, 2/3, 1, 3/2, 2, 3, 4, 6, 8, 10}`, plus un tirage seedé ; S3 — les 63 parties non vides ; S4 — 30 boîtes tirées par dimension ; S5 — les 14 nœuds. **Graines de test `0, 1, 7, 42, 99`** (convention de la famille) pour tout tirage ; **graines de contrôle `11, 22, 33`** pour le témoin aléatoire, jamais pour déplacer un seuil.

### Observables (par substrat, par hypothèse)

Pour chaque case `(substrat, hypothèse)` : `true` / `false` / `par_définition`, plus, quand elle est fausse, **un témoin nommé** (les régions qui violent l'énoncé, sérialisées dans le JSON). Les hypothèses universellement quantifiées sont évaluées sur la batterie entière ; les existentielles par recherche de témoin constructif. Le vecteur stable d'un substrat est celui qui ne dépend pas de la graine ; une instabilité entre graines est rapportée comme telle et **n'est pas** moyennée.

### Prédictions (scellées — aucun seuil ne sera déplacé après mesure)

| # | Prédiction | Critère |
|---|---|---|
| **P1** (H1, satisfiabilité) | S1 satisfait les 24 hypothèses sous E1+K | **24/24**, aucun contre-exemple sur la batterie |
| **P2** (S2, frontière) | S2 échoue sur **exactement** A16 ; le contre-exemple est celui qui est construit ici et le banc doit le retrouver | échecs = `{A16}` ; témoin attendu : `{(0,1/3), (1/3,2/3), (2/3,1)}` est une dissection de `(0,1)` **et** de `(0,1)\{1/3,2/3}` |
| **P3** (S3, atomicité) | S3 échoue sur **au moins** A2 et A9, et **pas** sur A16 | `{A2, A9} ⊆ échecs(S3)` et `A16 ∉ échecs(S3)` |
| **P4** (S5, arborescence) | S5 échoue sur **au moins** A2 et A3 | `{A2, A3} ⊆ échecs(S5)` |
| **P5** (H3, dimension) | le vecteur de S4 est **identique** pour `N = 1, 2, 3, 4` et vaut 24/24 | 4 vecteurs égaux, tous pleins |
| **P6** (null, sensibilité de l'instrument) | une relation symétrique irréflexive **aléatoire** sur 8 régions viole au moins **12** des 24 hypothèses | sur **5/5** graines de test — sinon `NON_CONCLUSIF_INSTRUMENT` |
| **Porte de partition** (H2) | la partition tombe des deux côtés avec de la marge : au moins 15 hypothèses nécessaires sur la famille, au moins 3 d'époque, **et** les quatre nommées d'avance y sont (A16 par S2, A2 par S3 et S5, A3 par S5, A9 par S3 et S5) | `card(nécessaires) ≥ 15` ∧ `card(époque) ≥ 3` ∧ les 4 nommées ∈ époque — sinon `NON_CONCLUSIF` |
| **Contrôle** (graines 11/22/33) | la marge du témoin aléatoire est large, elle ne frôle pas le seuil | violations ≥ 14/24 sur 3/3 — sinon le seuil de P6 est mal placé et le rapport le dit |

**Lemmes prouvés** (statut distinct de la mesure : ce sont des arguments de deux lignes, chacun doublé d'une vérification exhaustive par énumération — toutes les relations symétriques irréflexives sur `n ≤ 5`, soit 1 099 relations) :

- **L1 — D2 littérale rend l'inclusion réflexive, donc A7 insatisfiable.** `D2(A,A)` est vraie pour toute région : toute région connectée avec A est connectée avec A. A7 (« a region does not include itself ») est donc fausse dans **toute** famille non vide. ⇒ K2 (E1) est l'émendation minimale ; elle est retenue, et la lecture littérale est rapportée comme insatisfiable, jamais comme un échec d'un substrat.
- **L2 — D1 + A4 littérale sont incompatibles dès qu'une paire est connectée.** Si `C(A,B)` avec `A ≠ B`, alors `C(B,A)` (A1) et donc `C_m(A,A)` par D1 : la seconde clause de A4 (« or mediately connected with itself ») tombe. Et A2, lue sur la paire `(A,A)`, contredirait A4. ⇒ K1 (irréflexivité conventionnelle) et K4 (« paires distinctes ») sont des lectures, déclarées, non des mesures.
- **L3 — l'infinitude des ensembles abstractifs est un corollaire de A9, pas de D10.** Le texte l'affirme (p. 454 : « since every region includes other regions, and since the relation of inclusion is transitive, it is evident that every abstractive set must be composed of an infinite number of members ») — et la phrase nomme bien elle-même ses deux prémisses. Conséquence mesurable : dans un substrat qui viole A9 (S3), D10 admet les **singletons**, et les éléments géométriques de S3 sont des atomes, non des limites. Le banc compte les ensembles abstractifs par substrat pour départager.
- **L4 — A16 dépend de la convention de frontière.** Pour toute famille de régions **fermées**, A16 est vraie : si `{M_i}` dissèque A, alors `cl(A) = cl(∪M_i) ⊆ cl(A') = A'`; et si `A' ⊋ A`, une région assez petite dans `A'∖A` (à distance positive puisque A est fermé) est incluse dans `A'`, n'est dans aucun `M_i` et n'en chevauche aucun — ce qui viole (iii), donc `A' = A`. Pour la famille **ouverte**, le contre-exemple de P2 existe. ⇒ A16 discrimine le choix ouvert/fermé, elle ne décrit pas la connexion extensive en général.

**Verdict borné** (convention de la famille) : `SUPPORTED` si P1-P6 tenues et la porte ouverte ; `PARTIEL` si une prédiction non structurelle dévie (une hypothèse de plus ou de moins dans un vecteur) — le rapport nomme laquelle et pourquoi ; `REFUTÉ` si P1 tombe (aucun substrat ne satisfait les 24, le système n'est pas réalisable dans la famille) ; `NON_CONCLUSIF` sinon.

## 5. Greffe sur la lentille (lecture, jamais un claim)

La lentille grothendieckienne lit D10-D16 comme une **complétion** : les régions sont des ouverts d'une topologie grossière, les points les germs à l'infini de chaînes décroissantes — la construction est exactement celle d'un complété de Cauchy, et ce que D16 appelle « point » est une classe d'équivalence de suites décroissantes, pas un objet premier. Ce que la case 28 mesure alors, en L3, c'est que **la complétion suppose la non-atomicité** : sans A9 la chaîne s'arrête sur un atome, et le « point » dégénère en région minimale. Cette lecture n'est pas testée par la case 28 ; elle en est l'horizon.

## 6. Honnêteté grade C (limites)

1. **Une batterie finie ne prouve rien sur une famille infinie.** Les 24 évaluations sont exactes *sur la batterie* ; l'absence de contre-exemple est une **borne**, pas une preuve. Seuls L1, L2, L3 et L4 sont des arguments — et ils sont signalés comme tels, jamais fondus dans la matrice.
2. **24 hypothèses sur 31, 16 définitions sur 25.** A27-A33 (segments, extrémités, points situés, surfaces, volumes, lieux complets) et D16A-D24 sont hors tranche. Le titre du chapitre annonce « Points, Regions, Loci » : la moitié « Loci » n'est pas touchée ici.
3. **L'invariance de dimension n'est mesurée que sur le palier « boîtes ».** S4 ne teste pas A15/A16 (une boîte unique n'a pas de dissection non triviale dans cette famille) ; P5 porte donc sur les hypothèses communes aux quatre dimensions, pas sur les 24.
4. **Les artefacts de finitude sont déclarés.** S3 est fini (6 cellules) et S5 tronqué à la profondeur 3 : dans ces deux substrats, l'absence de région plus petite est un artefact du substrat, pas une thèse. C'est précisément ce qui les rend utilisables comme témoins de A9 — et c'est aussi pourquoi je ne leur demande pas de verdict sur les hypothèses d'abstraction fine.
5. **« Nécessaire » veut dire nécessaire-sur-cette-famille.** La partition de la porte est un résultat sur cinq familles, pas une thèse métaphysique. Une sixième famille pourrait déplacer une hypothèse de la colonne « nécessaire » vers « d'époque » ; le rapport le dira en ces termes, jamais « Whitehead avait tort ».
6. **Le vocabulaire « époque » est celui de Whitehead** (p. 442), pas une reconstruction : la tranche ne fait que lui donner un contenu mesurable dans un jouet.
7. **L'observation de numérotation (12 → 15) n'est pas exploitée.** Elle est constatée sur deux scans et mentionnée pour que personne ne la « corrige » en croyant à un trou d'OCR ; aucune hypothèse de la tranche n'en dépend.
8. **Une case 28 SUPPORTED dirait** : *les 24 hypothèses imprimées du chapitre II se réalisent dans une famille de régions fermées, et la partition nécessaire/époque tombe avec quatre hypothèses nommées d'avance* — rien de plus. Elle ne dirait pas que Whitehead avait raison sur la nature de l'extension.

## 7. Ce qui suit

1. **Ce document, commité, est le scellé.** Toute modification des prédictions se fait par amendement **pré-exécution** horodaté dans ce fichier (`v1 → v2 AVANT run`), jamais silencieusement.
2. Le banc `MyIA.AI.Notebooks/IIT/ICT-Series/ict/whitehead_extensive_connection.py`, les tests `ict/tests/test_whitehead_extensive_connection.py` et les mesures `ict/results/whitehead_extensive_connection_results.json` vivront dans un commit fils, avec la ligne du tableau `docs/ict/README.md` ajoutée dans la même PR.
3. Verdict rapporté sur [#8182](https://github.com/jsboige/CoursIA/issues/8182) avec la matrice brute par substrat et par graine. La veille ne se clôt pas sur une tranche.

## 8. Amendement v2 — pré-exécution (2026-11-26, avant toute ligne de banc)

Rédigé en spécifiant le banc, **avant qu'il existe**. Le commit du scellé v1 (`8d46c8047a8`) reste le parent ; cet amendement en est le fils ; le banc sera le petit-fils. Aucune mesure n'a été prise à cette date.

### L5 — le chapitre emploie un seul mot pour deux relations

K2 (v1) lisait « include » comme l'inclusion **propre** partout. Appliquée à D11, elle interdit à un ensemble abstractif de se couvrir lui-même (aucun membre ne s'inclut proprement), et A21 — « an abstractive set is equivalent to itself… An abstractive set **obviously** satisfies the conditions for such reflexive equivalence » (p. 456) — devient **fausse**. Le texte dit « obviously » : dans D11-D12, « include » est donc **réflexif**. Dans A7 (« a region does not include itself »), il est **irréflexif** — L1 montre que A7 est insatisfiable sous la lecture réflexive. Les deux emplois sont forcés, et ils sont incompatibles : le même mot désigne deux relations.

### K2′ (remplace K2)

- `A ⊑ B` (inclusion **faible**) := D2 littérale : toute région connectée avec B est connectée avec A. Réflexive.
- `A ⊏ B` (inclusion **propre**) := `A ⊑ B` et `A ≠ B`.
- **A5-A9** sont évaluées sur `⊏` (elles parlent d'asymétrie, A7-A8, et « includes *other* regions », A9).
- **D3** (« a third region which they both include ») : la troisième région est distincte de A et de B, où `⊑` et `⊏` coïncident — aucune convention n'est nécessaire.
- **D8-D9** (« B is included in A ») : sur `⊏`.
- **D10-D15** (couvrir, équivalence, élément, incident) : sur `⊑`.

### Statuts de cellule et critère « 24/24 »

Une case `(substrat, hypothèse)` vaut `true`, `false`, `par_definition` (K1, K3, A7 sous `⊏`) ou `partiel` — ce dernier quand une partie du domaine ne peut être évaluée sur la batterie. Une région sans coupure interne dans la batterie n'a pas de dissection constructible : c'est un **artefact de batterie**, compté et nommé, jamais rangé parmi les contre-exemples. **« 24/24 » signifie : aucune case `false`.** Chaque case `partiel` porte son nombre de régions exclues et son motif.

### Tailles de batterie (fixées)

S1/S2 — toutes les paires de la grille `{0, 1/2, 1, 3/2, 2, 3, 4, 6, 10}` (36 intervalles), 6 unions, 8 régions tirées par graine : **50** ; S3 — les 63 parties non vides (déterministe : les graines coïncident par construction) ; S4 — 30 boîtes par dimension ; S5 — 14 nœuds (déterministe).

### Dissections : le constructeur propose, la définition dispose

Les générateurs de dissections sont propres à chaque substrat (coupure interne pour S1/S2/S4, retrait d'une cellule pour S3, sous-arbres fils pour S5). **Chaque candidat est vérifié contre D4 avant d'être compté** ; un candidat rejeté est rapporté, jamais déposé en silence.

### A21-A26 : palier d'abstraction, pouvoir discriminant déclaré faible

Ces six hypothèses portent sur des ensembles abstractifs **infinis**. Le banc les évalue sur des chaînes explicites (S1 seulement : familles `[-2^-n, 2^-n]`, `[-3^-n, 3^-n]` convergeant vers 0, et `[1-2^-n, 1+2^-n]` convergeant vers 1 — un tronçon de longueur finie, la fin de chaîne étant incluse dans toute région de la batterie). Aucune de ces hypothèses ne peut y échouer pour une raison non triviale : leur statut est rapporté `true` **avec la marque « peu discriminant »**, et il n'entre pas dans le compte des hypothèses qui portent le verdict.

### v2.1 — trois précisions, toujours avant mesure

1. **D10(ii) se lit avec l'inclusion propre.** « There is no region included in every member of the set » : sous l'inclusion *faible*, le dernier membre d'une chaîne finie s'inclut lui-même et (ii) échoue toujours — aucun ensemble abstractif n'existerait, même dans l'espace usuel. Le texte tranche lui-même : l'argument de la p. 454 (« since every region includes other regions, and since the relation of inclusion is transitive, it is evident that every abstractive set must be composed of an infinite number of members ») n'a de sens que si (ii) parle d'inclusion propre — il invoque A9 pour exclure la fin de chaîne, ce qui serait inutile sous la lecture faible. Donc **(ii) := aucune région proprement incluse dans chaque membre**. Sur les chaînes infinies les deux lectures coïncident ; elles ne diffèrent que sur les chaînes finies, et c'est précisément là que L3 se mesure.
2. **La chaîne `[0, 2^-n]` n'est pas un ensemble abstractif.** D10(i) exige que l'inclusion entre membres soit **non tangentielle** ; or 0 est un point frontière de `[0, 2^-n]` et appartient à `[0, 2^-(n+1)]` : la région `[-δ, 0]` est connectée extérieurement avec les deux, l'inclusion est tangentielle. Une chaîne d'abstraction doit resserrer **autour** de sa limite, limite à l'intérieur de chaque membre. La v2 citait cette chaîne naïve : c'était une erreur de rédaction, corrigée ci-dessus. Le banc en fait un **témoin** : il doit la rejeter.
3. **Grille de coupure et sous-batteries.** La grille de S1/S2 porte les tiers du témoin scellé de P2 : `{0, 1/3, 1/2, 2/3, 1, 3/2, 2, 3, 4, 6, 10}` (55 intervalles), et la liste des unions contient le témoin lui-même, `(0,1/3) ∪ (1/3,2/3) ∪ (2/3,1)`. Les hypothèses dont le coût est en quatrième puissance du nombre de régions (A15-A20) sont évaluées sur une **sous-batterie déclarée** — les 21 intervalles simples à extrémités dans `{0, 1/3, 1/2, 2/3, 1, 3/2, 2}` pour S1/S2 ; les parties de `{0,1,2,3}` pour S3 ; la batterie entière pour S4 et S5 —, la recherche du contre-exemple de A16 portant elle sur la batterie entière. Les autres hypothèses (A1-A12) le sont sur la batterie entière.

Un substrat **exploratoire, non scellé**, est ajouté pour interpréter S2 : `S2r`, la même famille **régularisée** (deux ouverts de même adhérence sont une seule région). Il n'entre dans aucune prédiction ; il sert à dire si un échec de S2 tient à l'ouverture ou à l'irrégularité.
