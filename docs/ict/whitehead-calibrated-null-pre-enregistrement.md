# Pré-enregistrement — case 28b : portée exacte et null calibré de l'instrument relationnel de la case 28

> **Grade C explicite.** Ce document **scelle** le protocole de la case 28b de la veille [#8182](https://github.com/jsboige/CoursIA/issues/8182) **AVANT toute mesure à `n ≥ 6`** — même discipline que la case 28 : pré-enregistrement commité seul, le banc venant dans un commit fils (la parenté des commits porte l'antériorité). Il ne déplace **aucune** ligne du scellé de la case 28 : celui-ci reste la référence de ce qu'elle a mesuré, et ses résultats ne sont pas rejoués ici.
>
> **Cycle du 2026-11-28**, lane `myia-po-2023:CoursIA`. Claim : `[CLAIMED]` sur [#8182](https://github.com/jsboige/CoursIA/issues/8182), amendé en `c.7229881293` avec une clause `paths:` bornée aux cinq fichiers de la tranche (module, tests, résultats, ce document, la ligne d'index).
>
> **Ce que la case 28b répond.** La case 28 a mesuré la matrice des 24 hypothèses sur neuf substrats, puis constaté que ses deux nulls étaient hors d'atteinte **par construction**, et laissé la portée de l'instrument à un recensement de `n ≤ 5`. Trois choses restaient ouvertes, et la case 28 les nomme elle-même : la portée **exacte** (quelles hypothèses sont violables, combien peuvent l'être à la fois), un null **calibré** (quelle fréquence de violation attendre sous une loi explicite), et la dépendance à la densité que le balayage posait sans théorie. La case 28b les prend une par une, sur la même relation, avec le même organe invoqué par import.

## 1. Source, organe, périmètre

**Source primaire** : inchangée. Alfred North Whitehead, *Process and Reality — An Essay in Cosmology*, Macmillan, New York, 1929, texte de la première édition, domaine public aux États-Unis depuis le 1er janvier 2025. La copie archivée au gisement ([bibliography-hygiene](../../.claude/rules/bibliography-hygiene.md)) est celle de la case 28 — `G:\Mon Drive\MyIA\IA\Bibliographie IA\Consciousness\1929 - Whitehead - Process and Reality - An Essay in Cosmology (Gifford Lectures Edinburgh 1927-28, Macmillan New York, texte de la 1re edition, 5e tirage 1960, domaine public US depuis 2025, IA processrealityes0000unse).pdf`, 21 132 402 octets, SHA-256 `a74f45e4a10195ebf3cbbf05fff9c8ba2ac79dce77bdc164567ae5f522a4d533`. **Aucune nouvelle pièce n'a été récupérée** : la case 28b ne relit pas le chapitre, elle recalibre l'instrument que la case 28 en a tiré. Aucune citation nouvelle n'est donc introduite, et l'identité de la source se vérifie à l'identique (section 1 du scellé de la case 28).

**Organe** : `ict/whitehead_extensive_connection.py` — le banc de la case 28. La case 28b l'invoque **par import** et n'en réimplémente rien : `Relational` pour la famille finie de régions, `assess` pour les 24 statuts, `_failures` pour la liste des hypothèses fausses. Elle **n'ajoute aucune sémantique** : elle énumère des relations, appelle l'organe, et agrège. Si un agrégat de la case 28b divergeait de l'organe, c'est l'agrégat qui serait faux.

**Périmètre, ce qui n'est pas touché** : le scellé de la case 28, son module, ses tests et son artefact de résultats restent tels quels, octet pour octet. La case 28b est un jeu de fichiers neufs et une ligne d'index.

## 2. Ce que la case 28 a laissé ouvert, dans ses propres mots

Deux passages du scellé de la case 28 v2.2 fixent la dette. Le lemme L7 (§4) :

> Treize des vingt-quatre hypothèses sont des conventions ou des théorèmes dans toute famille : A4, A7, A21, A26 ; A5, A6 ; A10 ; A19 ; A22-A25 (D11-D13, sous K5) ; A1, puisque chaque générateur construit une relation symétrique. **Onze au plus peuvent être violées** : A2, A3, A8, A9, A11, A12, A15, A16, A17, A18, A20. **Le seuil de P6 (12) et celui du contrôle (14) sont donc hors de portée par construction.** Ils ne sont pas déplacés : l'échec de P6 sera mesuré et rapporté, et le verdict suivra la règle scellée. Un **recensement exhaustif** — toutes les relations symétriques irréflexives sur `n ≤ 5` régions, nombre d'hypothèses violées par relation — est ajouté : il mesure la portée réelle de l'instrument et servira de base à un rescellement.

Et le §8 :

> **8. Témoin aléatoire : balayage exploratoire, hors verdict.** Les mêmes graines de test à densité `p ∈ {0.15, 0.3, 0.7}` […]. Motif déclaré : une relation dense a peu d'inclusions dérivées, donc beaucoup d'hypothèses vides ; savoir si la portée dépend de la densité est la question qu'un rescellement devra poser.

Trois dettes, donc, et une quatrième que la case 28 n'écrit pas mais que son artefact montre : le recensement s'arrête à `n = 5`, et sa liste `jamais_violees` compte **dix-sept** entrées dont **A17** — alors que A17 est précisément une hypothèse dont la clause existentiale demande un candidat **distinct à la fois de la paire et du pool**, ce qui n'a pas de place à `n ≤ 5`. La liste mélange donc des théorèmes et des hypothèses que la taille du recensement n'a pas exercées. C'est la quatrième dette, et c'est celle que la case 28b paie en premier : **une hypothèse jamais violée par un recensement trop petit n'est pas une hypothèse non violable.**

## 3. Théorèmes de lecture (certificats papier)

Les quatre énoncés ci-dessous sont **lus dans le code de la case 28**, ligne à ligne, dans l'état où il est committé. Ils ne sont **pas recalculés par machine avant cette écriture** : la mesure exhaustive du §4 est ce qui les vérifie, et ce document les déclare avant elle. Ils portent sur la famille `Relational` telle que le banc la construit — `conn` = appartenance à la matrice d'adjacence, `includes(i,j)` = `N[j] ⊆ N[i]` (clôtures réflexives), `ov` = existence d'une tierce région incluse dans l'intersection des clôtures, `proper_in` = inclusions propres.

**T1 — A12 est un théorème de la lecture.** A12 se mesure par `ovm[i] & ~cnm[i]` : un recouvrement non connecté. Soit `ov(x,y)` avec `x ≠ y` : il existe `t ∉ {x,y}` tel que `N[t] ⊆ N[x] ∩ N[y]`. Alors `t ∈ N[y]`, donc `t ~ y`, donc `y ∈ N(t) ⊆ N[t] ⊆ N[x]`, donc `x ~ y`. Le masque est donc vide sur **toute** relation. A12 n'est pas violable ; L7 la comptait à tort parmi les onze.

**T2 — A20 est un théorème de la lecture, par l'élément minimal du pool.** Le pool d'une paire est `{z : N[z] ⊆ W}` avec `W = N[x] ∩ N[y]`, non vide dès que `ov(x,y)`. `_is_intersect` écarte un candidat `c` quand il existe `o` du pool, `o ∉ {x,y,c}`, tel que `ov(o,c)` et `¬includes(c,o)`. Si `x` est dans le pool, `x` est le minimum et passe (le disqualifier demanderait `¬includes(x,o)`, impossible puisque `N[o] ⊆ N[x]`). Sinon, soit `m` **minimal** dans le pool : si un `o` du pool le disqualifiait, on prendrait `t ∉ {o,m}` avec `N[t] ⊆ N[o] ∩ N[m]` — `t` est dans le pool ; si `N[t] = N[m]` alors `N[m] ⊆ N[o]`, donc `includes(m,o)`, contradiction ; sinon `N[t] ⊊ N[m]` contredit la minimalité de `m`. Le pool n'est donc jamais vidé et A20 n'est pas violable. (Une preuve par l'élément **maximal**, que j'avais d'abord écrite, est fausse : deux éléments maximaux incomparables se disqualifient mutuellement. Le lemme tient par le minimum.)
 Une conséquence : A20 n'est pas seulement vraie sur les neuf substrats, elle est **vraie partout**, et sa case `true` dans la matrice de la case 28 n'était pas une mesure.

**T3 — A9 est fausse sur toute relation non vide.** `disjoint_pair` délègue à `disjoint_pair_constructed`, qui rend `None` sans override dans `Relational` ; `assess` classe alors la région en `no_pair` dès qu'elle a une partie propre, et en `no_part` sinon. Toute relation a donc au moins une région fautive : `q₉ = 0` exactement, à toute densité et toute taille.

**T4 — A3 et A17 s'excluent.** A3 fausse signifie que la connexion est transitive, donc que la relation est une union de cliques ; dans une clique de taille au moins trois, toutes les régions se recouvrent, le pool d'une paire est la clique entière, aucun membre n'est disqualifié, l'ensemble des intersects est la clique, et aucun candidat n'existe hors de lui — A17 est vraie. Réciproquement une relation qui n'est pas une union de cliques viole A3. Donc `A3 ∧ A17` n'est jamais fausse deux fois.

**Conséquences, scellées comme telles.** La portée exacte de l'instrument relationnel est `R = {2, 3, 8, 9, 11, 15, 16, 17, 18}` — **neuf** hypothèses, et non onze : A12 et A20 en sortent par T1 et T2. Le plafond du nombre de violations simultanées est **huit**, par T4 et par le cardinal de `R`. Ce plafond est **atteint** : le certificat est `G = K₃ ⊔ K₂ ⊔ K₁` sur six régions, dont l'évaluation à la main contre le code donne exactement `{2, 3, 8, 9, 11, 15, 16, 18}` — A2 (une région isolée sans voisin, et la paire inter-cliques sans intermédiaire), A3 (union de cliques, donc transitive), A8 (les jumeaux de la K₃), A9 (T3), A11 (la paire de la K₂ s'inclut sans se recouvrir), A15 (la région de la K₂ n'a qu'une dissection valide), A16 (le jeu `{b}` de la K₃ dissèque aussi `c`), A18 (la paire de la K₃ a trois intersects) — et A17 vraie, comme T4 l'exige.

**Témoin d'A17 à `n = 6`.** `W = K₆ ∖ {cf, ef}`, treize arêtes : `a:{b,c,d,e,f}`, `b:{a,c,d,e,f}`, `c:{a,b,d,e}`, `d:{a,b,c,e,f}`, `e:{a,b,c,d}`, `f:{a,b,d}`. Vérifié à la main contre le code : les paires qui se recouvrent sont `(a,b), (a,c), (a,d), (a,e), (b,c), (b,d), (b,e), (c,d), (c,e)` ; sur `(a,b)`, `intersects` rend `[a, b, d, f]` (`c` et `e` disqualifiés par `d`) ; le candidat `c` a pour tenants `[a, b, d]`, soit **trois** — A17 est fausse. A3 est vraie sur `W` (`f ~ a ~ c` avec `f ≁ c`), donc `W` est compatible avec T4.

**Ce que ces certificats ne sont pas.** Ils ne sont pas une mesure : ils sont une lecture du code, écrite avant la mesure, et c'est le recensement du §4 qui les vérifie sur les 32 768 relations.

## 4. Questions scellées

**Le plan de mesure.** Le recensement est **exhaustif** sur `n = 6` : les `2^15 = 32 768` relations symétriques irréflexives, chacune évaluée par `assess`. Aucune graine, aucun échantillon, aucune cellule `partiel` possible : à `n = 6` une région a au plus `2^5 = 32` jeux candidats, très en dessous du plafond d'énumération (50 000), donc l'énumération des dissections est exacte partout et A15/A16 sont mesurées, jamais `partiel`. Le null exact est **la loi uniforme** sur ces 32 768 relations, et la courbe de densité en est la version pondérée : la probabilité d'une relation à `m` arêtes vaut `p^m (1-p)^{15-m}`, en fractions exactes, sans bruit d'échantillonnage.

**Ce que `q_i` désigne.** `q_i(d)` = probabilité que l'hypothèse `i` soit **vraie** sous cette loi ; `P_i(d) = 1 - q_i(d)` est la probabilité de violation. `K` = nombre d'hypothèses violées parmi les vingt-quatre imprimées (les quinze non violables ne comptent jamais).

### Q1 — Portée exacte (recensement exhaustif, `n = 6`)

- **Q1a.** La réunion des ensembles de violations sur les 32 768 relations est **exactement** `R = {2, 3, 8, 9, 11, 15, 16, 17, 18}` : aucune hypothèse hors de `R` n'est violée une seule fois, et chacune des neuf est violée au moins une fois.
- **Q1b.** A12 et A20 sont violées sur **zéro** relation (T1, T2). A9 sur **toutes** (T3).
- **Q1c.** Le maximum de `K` vaut **8**, et il est atteint.
- **Q1d.** A3 et A17 ne sont **jamais** fausses ensemble (T4) ; en particulier aucune relation n'a `K = 9`.
- **Q1e.** Le témoin `W` du §3 est évalué **par son nom**, non par sa position dans l'énumération : il est violé sur un ensemble contenant `{2, 8, 9, 11, 17, 18}` et A3 y est vraie. `G = K₃ ⊔ K₂ ⊔ K₁` est violé exactement sur `{2, 3, 8, 9, 11, 15, 16, 18}`.

### Q2 — Null exact (uniforme, `n = 6`, 32 768 relations)

- **Q2a.** `q₉ = 0`, `q₁₂ = 1`, `q₂₀ = 1` — exactement.
- **Q2b.** L'ensemble des hypothèses violées avec probabilité au moins `9/10` est **inclus dans `R`** et **contient** `{2, 9, 11, 15}`. Autrement dit le noyau du null est un sous-ensemble de la portée, et il contient les quatre hypothèses que le null publié à `n = 8` trouvait sur toutes les graines.
- **Q2c.** Le seuil calibré `k*`, plus grand entier tel que `P(K ≥ k) ≥ 95/100`, appartient à `{3, 4}`. Il est donc strictement inférieur aux seuils 12 et 14 de la case 28, et strictement inférieur au plafond 8.

### Q3 — Transfert à `n = 8` sur graines fraîches

Graines de test `(101, 202, 303, 404, 505)`, contrôles `(111, 222, 333)`, taille 8, densité scellée `1/2` — soit, dans la loi que `random_substrate` échantillonne, `p = 499/1000`. Disjointes de `(0, 1, 7, 42, 99)`, `(11, 22, 33)` et des graines de balayage `(500, 501, 507, 542, 599)`.

- **Q3a.** A9 est violée sur **8/8** (T3) ; A15 sur **au moins 7/8** ; A2 sur **au moins 6/8** ; A11 sur **au moins 5/8**.
- **Q3b.** Sur chacune des huit relations, l'ensemble des violations est **inclus dans `R`**.
- **Q3c.** `K ≥ 3` sur **au moins 6/8**, et le minimum de `K` sur les huit est **inférieur ou égal à 4**.

### Q4 — Courbe de densité exacte (`n = 6`, fractions)

Grille scellée : `k/20` pour `k = 0..20`, plus les quatre points que le balayage échantillonne réellement (`149/1000`, `299/1000`, `699/1000`, `849/1000`).

- **Q4a.** À toute densité de la grille, l'ensemble des violations de chaque relation est inclus dans `R` (la portée est indépendante de la densité).
- **Q4b.** `q₉(d) = 0` à toute densité (T3).
- **Q4c.** À `d = 1` (graphe complet `K₆`) : `{2, 3, 8, 9, 18}` sont violées, et **A11, A15 et A17 sont vraies**. A16 est violée.
- **Q4d.** La table `q_i(d)` est la **livraison** de cette question, pas une prédiction : elle se calcule exactement, et le scellé ne fixe que les propriétés ci-dessus.

### Q5 — Balayage à `n = 8` sur graines fraîches (confirmatoire)

Graines `(611, 722, 833, 944, 1055)`, densités `3/20`, `3/10`, `7/10` — la quatrième densité `17/20` est **exploratoire, hors verdict** (elle ne figure dans aucun critère ci-dessous ; son intérêt est de pousser le balayage publié d'un cran vers le dense).

- **Q5a.** À `3/20` : `{2, 9, 15}` inclus dans les violations sur **5/5**.
- **Q5b.** À `3/10` : `{2, 9, 15}` inclus sur **5/5**.
- **Q5c.** À `7/10` : `{9, 11, 15}` inclus sur **5/5**, et A18 sur **au moins 3/5**.
- **Q5d.** Sur les quinze relations tirées : violations incluses dans `R` sur **15/15**, A9 violée sur **15/15**, `K ≤ 8` partout.

## 5. Règle de verdict

Comme la case 28, la case 28b rend **deux verdicts bornés et un combiné**, sur l'échelle `SUPPORTED` / `PARTIEL` / `RÉFUTÉ` / `NON_CONCLUSIF` / `NON_CONCLUSIF_INSTRUMENT` :

- **`verdict_portee`** — Q1, Q4a à Q4c, et les jambes structurelles de Q3b et Q5d. `SUPPORTED` si toutes les clauses tiennent ; `PARTIEL` si l'une tombe ; `RÉFUTÉ` si un théorème du §3 est démenti par le recensement (cas le plus grave : un certificat papier faux).
- **`verdict_null`** — Q2, Q3a, Q3c, Q5a à Q5c. `SUPPORTED` si toutes tiennent ; `PARTIEL` si une seule tombe ; `RÉFUTÉ` si deux tombent ou plus.
- **`verdict`** — combiné : `SUPPORTED` si les deux le sont, `NON_CONCLUSIF_INSTRUMENT` si le recensement n'a pas pu s'achever ou si plus de 1 % des relations ont une cellule indécise (impossible à `n = 6` par le §4, la clause est écrite pour être honnête et non pour servir), `PARTIEL` sinon.

**Aucune bande n'est déplacée après mesure.** Si une clause tombe, elle tombe : le document de résultats la rapporte avec sa valeur, et la conclusion suit. Un théorème démenti se rapporte comme erreur de lecture, pas comme résultat.

## 6. Honnêteté : ce que je sais déjà, et ce que je n'ai pas fait

- **Le recensement `n ≤ 5` de la case 28 est publié** (1 099 relations) : A2 et A9 sur toutes, A3 sur 75, A8 sur 473, A11 sur 1 032, A15 sur 1 096, A16 sur 212, A18 sur 388, plafond observé 8, A17 jamais violée. Le null à `n = 8` est publié aussi (graines 0/1/7/42/99 : `K` = 4, 4, 6, 3, 5 ; contrôles 11/22/33 : 5, 3, 4). **Conséquence déclarée** : Q3 et Q5 sont pour l'essentiel **confirmatoires**, et leurs seuils sont calibrés sous les valeurs publiées, pas au-dessus. Le contenu neuf de la case 28b est Q1, Q2 et Q4 — l'exhaustif à `n = 6`, le null exact, la courbe exacte.
- **Aucun statut à `n ≥ 6` n'a été lu avant cette écriture.** Le seul contact antérieur avec `n = 6` est un chronométrage : 200 relations tirées au hasard, durée mesurée (0,26 ms par relation), **statuts non lus et non conservés**. Il est déclaré ici parce qu'il a eu lieu.
- **T1 à T4 sont des certificats papier**, non recalculés par machine avant cette écriture. C'est le recensement qui les vérifie.
- **Une erreur de lecture de la case 28 est consignée** : j'y avais affirmé qu'une relation `K₅` privée de deux arêtes violait A17 à `n = 5`, en prenant la région de la paire elle-même pour disqualifieur — que `_is_intersect` écarte. Le recensement publié l'a démentie ; la case 28b ne la répète pas. De même, deux certificats de ma note préparatoire ont été corrigés contre le code avant cette écriture : la preuve d'A20 par le maximum (fausse) et le certificat de plafond par `K₃` plus sommets isolés (faux : un sommet isolé n'est inclus dans personne, et `K₃` seul ne fait pas huit).
- **Le null exact et le null échantillonné ne sont pas la même loi** : `random_substrate` tire chaque arête sur la grille `1/1000` avec seuil strict, donc « densité `1/2` » y vaut `499/1000` et « `17/20` » y vaut `849/1000`. Le null exact est évalué à `499/1000` pour Q2, et la courbe porte les quatre valeurs réellement échantillonnées.
- **Une borne d'instrument est déclarée, pas corrigée** : A16 ne sonde que les quatre premiers jeux valides par région (`want = 4`), et l'organe ne rend `partiel` que sur le plafond d'énumération. Un `A16 = true` signifie donc « aucun contre-exemple parmi ces quatre-là ». La case 28 partageait déjà cette borne ; la case 28b la nomme.
- **La borne de la case 28 §6.3 ne s'applique pas ici** : sur `Relational`, les dissections sont énumérées par sous-ensembles, pas par le générateur de quatre motifs des familles continues. A15/A16 ne sont donc jamais `partiel` sur la famille relationnelle, et aucune correction de générateur n'est due.

## 7. Ce que la calibration change pour la case 28

1. **Les seuils 12 et 14 sont retirés comme inatteignables, pas seulement échoués.** Le plafond exact est 8, prouvé (T4) et atteint (`G`). Un seuil au-dessus de 8 ne mesure rien : il ne peut pas être franchi, quelle que soit la relation. La case 28 avait raison de les déclarer hors de portée ; elle avait tort sur le chiffre de la portée (11 au lieu de 9) et sur la raison d'A12 et A20 (théorèmes, non « violables »).
2. **Le seuil d'un futur test de type P6 se dérive du null exact** : `k*` — plus grand `k` tel que `P(K ≥ k) ≥ 95/100` sous la loi uniforme à `n = 6` — et il vaut 3 ou 4. C'est le rescellement que L7 appelait : la valeur est mesurée, la règle qui la produit est scellée ici.
3. **La liste `jamais_violees` est remplacée par `R`.** Une hypothèse jamais violée par un recensement de taille `n` n'est pas non violable : A17 en est le cas d'école, et elle demande six régions pour s'exercer. Toute publication ultérieure de portée doit donc déclarer la taille de son recensement **et** l'arité minimale de chaque hypothèse.
4. **La portée ne dépend pas de la densité** (Q4a) : ce que la densité déplace, c'est la **fréquence** de chaque violation, pas l'ensemble des violables. Le §8 de la case 28 posait la question ; la réponse est que la question était mal posée, et Q4 en donne la vraie forme — une courbe, pas une portée.

## 8. Ce qui n'est pas pris

- L'extension du générateur de dissections et la réécriture du critère de P5, tous deux nommés par l'errata v2.4 de la case 28 comme des resellements : ils restent des resellements, et ne sont pas pris ici.
- Le pas `n = 7` (le recensement exact y demande `2^21 = 2 097 152` relations, soit environ neuf minutes à la vitesse chronométrée) : hors budget de la tranche, et sans changement qualitatif attendu — la portée est déjà pleine à `n = 6`.
- Les familles **structurées** (treillis, hypercubes, graphes aléatoires à blocs) comme null alternatif : la case 28b ne calibre que la loi uniforme.
- Un null non uniforme ou biaisé par une contrainte de degré : la case 28 en use déjà un implicitement (le tirage indépendant), et le séparer est une autre question.
- A27-A33 et D16A-D24, hors périmètre depuis la case 28.

**Livraison attendue** : module `ict/whitehead_calibrated_null.py`, tests `ict/tests/test_whitehead_calibrated_null.py`, résultats `ict/results/whitehead_calibrated_null_results.json` (aucun horodatage, deux exécutions identiques), une ligne d'index dans `docs/ict/README.md`. Aucun fichier de la case 28 n'est modifié.
