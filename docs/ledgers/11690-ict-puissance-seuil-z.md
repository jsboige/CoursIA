# ICT-35 — puissance reelle du seuil `|z| > 3` (la regle de detection)

**Ancre** : #11690 (EPIC consolidation ICT) · serie ICT-35 (carnets 35b/35c/35d) ·
complement de la lecture « null global sur le maximum » (PR #27208).

**Statut** : mesure publiee. Le module `ict/humor_power.py` et ses tests
(`ict/tests/test_humor_power.py`) sont la partie executable de cette lecture.

---

## 1. Ce que la lecture ajoute

ICT-35d conclut `AUCUNE_FEATURE_STABLE` : sur les 18 jambes du protocole
(3 couches x 3 types x trained/control), aucune feature ne franchit le
seuil `|z| > 3` du meme cote. La lecture « null global sur le maximum »
(PR #27208) a montre que **ce zero est l'issue typique du null** (96,7 % des
tirages nuls ne produisent aucune feature au-dela du seuil) : le verdict
n'est donc pas une absence de signal, c'est une absence de *puissance*.

La presente lecture quantifie la puissance : **quelle taille d'effet
faudrait-il pour que la regle de detection s'ecole ?** Sans cette reponse,
« aucune feature » ne peut pas etre lu comme « l'effet n'existe pas ».

**Les lectures, dans l'ordre ou elles s'enchainent :**

| # | Question | Section |
| ---: | --- | ---: |
| 1 | quelle taille d'effet faut-il, en unites de la statistique ? | 3 |
| 2 | le null de l'instrument confirme-t-il la queue nulle publiee ? | 4 |
| 3 | combien de paires faut-il ? (lecture **brute**, corrigee en 11) | 8 |
| 4 | la puissance est-elle la meme sur toutes les jambes ? | 9 |
| 5 | que **coute** la convention pre-enregistree `\|z\| > 3` ? | 10 |
| 6 | jusqu'ou l'extrapolation en nombre de paires est-elle valide ? | 11 |

## 2. Modele (declare)

Sous H1, la statistique observee d'une feature est

```text
z = z_nul + delta
```

où `z_nul` est un tirage du null de l'instrument (flip de signe intra-paire,
construction de `ict/humor_pairs.measure_humor_differential`) et `delta` est
le deplacement de la moyenne par paire exprime **en unites de dispersion
nulle** (la meme unite que le z). Le deplacement est suppose additif sur la
moyenne par paire : la dispersion de la statistique est alors inchangee, ce
qui rend le modele exact plutot qu'approximatif.

La regle de detection est celle de l'instrument, inchangee : **au moins
`min_same_side = 3` features au-dela de `threshold = 3`, du meme cote**.

Deux bornes structurent la lecture :

* **`|z| <= sqrt(n)`** — le z d'une feature vaut `<a_f, 1> / ||a_f||` ;
  Cauchy-Schwarz le borne par `sqrt(n)`. Avec 30 paires, le plafond est
  **`sqrt(30) = 5,477`** : aucune feature ne peut le depasser, quelle que
  soit la taille de l'effet. Une courbe qui monte au-dela decrit un effet
  inaccessible.
* **le seuil est une convention de l'instrument**, pas une propriete de la
  loi : la courbe se lit « si le seuil etait `t`, quel effet faudrait-il ? ».

## 3. Mesure

Traces : `humor35b_qwen35-2b-base_layer12of24_trained.npz` (layer 12/24,
Qwen3.5-2B-Base, SAE-Res-W32K-L0.50), 30 paires minimales du corpus
GT-24b. 1000 replicats, `seed=42`. Features plantees tirees uniformement
parmi les **5 642 features actives** (sur 32 768, les 27 126 autres ont une
différence de zone exactement nulle : elles ne peuvent porter aucun effet).

| `delta` | % du plafond | P(au moins 1 feature > 3) | **P(la regle s'ecole)** | features > 3 (moyenne) |
| ---: | ---: | ---: | ---: | ---: |
| 0,0 | 0 % | 0,026 | **0,000** | 0,026 |
| 1,0 | 18 % | 0,027 | **0,000** | 0,027 |
| 2,0 | 37 % | 0,263 | **0,001** | 0,295 |
| 2,5 | 46 % | 0,821 | **0,082** | 1,321 |
| 3,0 | 55 % | 0,871 | **0,119** | 1,514 |
| 3,5 | 64 % | 0,906 | **0,177** | 1,704 |
| 4,0 | 73 % | 0,940 | **0,240** | 1,885 |
| 4,5 | 82 % | 1,000 | **0,954** | 2,979 |
| 5,0 | 91 % | 1,000 | **0,998** | 3,024 |
| 5,4 | 99 % | 1,000 | **1,000** | 3,026 |

**Sensibilite au nombre de features affectees** (meme trace, meme seed) :

| `delta` | 0 | 2 | 3 | 3,5 | 4 | 4,5 | 5 |
|---| ---: | ---: | ---: | ---: | ---: |---:|---:|
| `k = 1`, P(regle) | 0,000 | 0,000 | 0,000 | 0,000 | 0,000 | 0,000 | 0,000 |
| `k = 3`, P(regle) | 0,000 | 0,001 | 0,119 | 0,177 | 0,240 | 0,954 | 0,998 |
| `k = 10`, P(regle) | 0,000 | 0,069 | 0,948 | 0,984 | 0,993 | 1,000 | 1,000 |

## 4. Ancre de coherence avec l'organe natif

| Mesure | Organe natif (PR #27208, ICT-35d « Lecture 5 bis ») | Ce module | Ecart |
| --- | ---: | ---: | --- |
| P(le null produit **zero** feature au-dela de 3) | 0,967 | 0,974 | 0,007 (1,4 sigma de l'estimateur, D = 2048 / 1000) |
| Features au-dela de 3 sur la jambe agregee observee | 0 | 0 | 0 |
| `max |z|` median sous null | 2,57 | 2,57 | 0 |

Les deux lectures sont **independantes** dans leur implementation (dispersion
empirique sur 2048 tirages d'un cote, formule exacte `||diffs_f||_2 / n` de
l'autre) et convergent : la formule exacte de la dispersion nulle est bien la
limite de l'estimation empirique de l'instrument.

## 5. Ce que la mesure dit (et ne dit pas)

1. **La regle n'a de puissance que dans le haut de la plage atteignable.**
   80 % de puissance exigent `delta ~ 4,3` (± 0,2), soit **~79 % du plafond
   theorique** `sqrt(30) = 5,477`. La fenetre de detection est etroite :
   `delta` compris entre 4,2 et 4,6.
2. **Le seuil franchi n'est pas le seuil detecte.** A `delta = 3` (l'effet
   qui fait franchir le seuil a une feature), une feature passe le seuil
   dans 87 % des cas mais **la regle ne s'ecole que dans 12 %** : les trois
   features doivent passer **du meme cote**, et une feature plantee sur un
   tirage de signes peut tomber du mauvais cote.
3. **Le nombre de features affectees compte davantage que leur taille.** A
   `delta = 3`, dix features affectees declenchent la regle dans 95 % des
   cas, trois dans 12 %.
4. **Consequence pour la lecture d'ICT-35d.** Le verdict `AUCUNE_FEATURE_STABLE`
   n'informe que si les effets plausibles se situent dans le haut de la
   plage atteignable. En deçà de `delta ~ 2,5` (46 % du plafond), la regle
   ne s'ecole **pas** — le zero observe est alors une propriete de
   l'instrument, pas une propriete des donnees. C'est la lecture
   complementaire de la « Lecture 7 » d'ICT-35d, qui declarait l'absence
   de preuve sans quantifier la preuve manquante.

## 6. Limites (declarees)

* Local au triplet **Qwen3.5-2B-Base x SAE-Res-W32K-L0.50 x couche 12/24**,
  aux 30 paires du corpus GT-24b. Rien ne transpose a un autre modele, SAE,
  corpus, couche ou nombre de paires.
* `delta` est exprime en **unites de dispersion nulle de la statistique**,
  pas en unites d'activation : `delta = 4` signifie que la moyenne par paire
  se deplace de quatre fois la dispersion nulle de cette moyenne.
* Le modele suppose un effet additif sur la moyenne par paire, de
  dispersion inchangee. Un effet qui modifie la dispersion (variance), ou
  heterogene d'une paire a l'autre, sort du modele.
* La realisation de l'effet est tiree uniformement parmi les features
  actives ; une concentration de l'effet sur des features de profil
  particulier (forte norme) n'est pas couverte.
* Le plafond `sqrt(n)` est une propriete de l'estimateur : **plus de paires
  l'elargissent**. Une lecture de puissance sur 100 paires donnerait un
  plafond de 10 et une fenetre de detection plus large. C'est la voie
  d'amelioration de l'instrument que la mesure designe — et c'est
  l'objet de la section 8, qui la chiffre.
* **L'extrapolation en nombre de paires est une lecture brute** : elle est
  produite par un substitut (bootstrap sur les 30 paires reelles) dont la
  queue nulle se degrade avec `n`. La section 11 mesure cette degradation
  et corrige les sections 8 et 9 en consequence. Seul `n = 30` est mesure
  de maniere exacte.

## 8. Combien de paires pour 80 % de puissance ?

La section 3 exprime `delta` en **unites de dispersion nulle de la
statistique**, une unite qui **depend du nombre de paires** (elle vaut
`||diffs_f||_2 / n`). A effet identique, la puissance ne change donc pas
quand on change `n` : la question « combien de paires faut-il ? » n'a pas
de reponse dans cette unite. Il faut une unite **independante de `n`**.

C'est la **taille d'effet par paire** `d` : chaque paire decale la feature
de `d` fois son **bruit par paire** (`per_pair_rms` = `||diffs_f||_2 /
sqrt(n)`). Le z observe se deplace alors de `d * sqrt(n)` : le gain d'une
paire vaut `sqrt(n)`, pas `n` — la loi classique de la puissance.

Sur les traces reelles : 5 642 features actives sur 32 768 (17,2 %), bruit
par paire median **0,0111** (p25 0,0058 · p75 0,0216 · max 0,343).

Les paires sont **tirees avec remise** (bootstrap) depuis les 30 paires
reelles pour atteindre `n` : la zone d'edition d'une paire est calculee
independamment des autres, donc reechantillonner les paires est legitime
(hypothese : les paires minimales sont approximativement exchangeables).

**P(la regle s'ecole)** selon `n` et `d` (8 bootstraps x 100 replicats,
`seed=42`, `k = 3` features plantees) :

| `n` \ `d` | 0,20 | 0,30 | 0,40 | 0,50 |
| ---: | ---: | ---: | ---: | ---: |
| 30 (actuel) | 0,001 | 0,003 | 0,041 | **0,079** |
| 60 | 0,030 | 0,090 | 0,284 | 0,477 |
| 90 | 0,129 | 0,226 | 0,531 | **0,964** |
| 120 | 0,185 | 0,404 | **0,819** | 0,999 |
| 180 | 0,343 | **0,812** | 0,995 | 1,000 |
| 240 | 0,496 | 0,931 | 1,000 | 1,000 |

**Le nombre de paires qu'il faut pour 80 % de puissance** :

| `d` (effet par paire) | `n` pour 80 % de puissance | decontenance vs 30 paires |
| ---: | ---: | ---: |
| 0,50 | ~90 paires | x3 |
| 0,40 | ~120 paires | x4 |
| 0,30 | **~210 paires** (grille fine, section 9) | x7 |
| 0,20 | > 240 paires (47 % a 240) | > x8 |

> **Correction (section 11).** Ce tableau est une **puissance brute** : il
> compte l'ecol de la regle sous l'effet, **effet nul compris**. Or le
> substitut qui produit ces nombres (bootstrap sur les 30 paires reelles)
> a une **queue nulle qui se degrade avec `n`** : a `n = 90`, la regle
> s'ecole deja dans **9,3 %** des cas *sans aucun effet* ; a `n = 210`, dans
> **23,9 %**. Lue en **contraste** (puissance brute moins taux de faux
> positifs), la ligne `d = 0,50` resiste (0,871 a `n = 90`, au-dessus de
> 0,80), mais les lignes `d = 0,40` et `d = 0,30` **ne resistent pas** :
> leur contraste plafonne a **0,78** et **0,70**, quel que soit `n`.
> Ce que ces lignes etablissent n'est donc pas un nombre de paires, mais
> une **borne** : ces 30 paires ne permettent pas d'extrapoler un
> protocole, et le nombre de paires **independantes** necessaire n'est pas
> estimable ici. Le seul `n` mesure de maniere exacte est **30**.

> **Correction (section 9).** La grille grossiere de cette section (n =
> 30, 60, 90, 120, 180, 240 ; 8 bootstraps x 100 replicats) plaçait `d = 0,3`
> a **~180 paires** (P(regle) = 0,812 a `n = 180`). La grille fine (pas de 15
> paires) a double budget (16 bootstraps x 200 replicats, soit 3 200
> tirages par point, erreur type ~0,4 point) donne **P(regle) = 0,787** a
> `n = 180` et **0,878** a `n = 210` : le seuil de 80 % est donc atteint a
> **~210 paires**, pas 180. L'ecart de la premiere lecture (2,5 points)
> est de l'ordre de l'erreur de Monte-Carlo de son dispositif ; la valeur
> publiee est desormais celle de la grille fine.

**Ce que cela dit.**

1. **A 30 paires, la regle est sous-equipee meme pour un effet net.** Un
   effet par paire de 0,5 (chaque paire decale la feature de la moitie de
   son bruit propre) ne fait s'ecoler la regle que dans **7,9 %** des cas.
   Le zero d'ICT-35d n'interdit donc pas un effet « net » : il l'interdit
   *a 30 paires*.
2. **Le cout des paires est en `sqrt(n)`, pas en `n`** : passer de 30 a 90
   paires triple l'instrumentation pour un effet detectable de 0,5 par
   paire. Le cout material dominant n'est pas le calcul (numpy seul, 3,5 s
   pour 1 000 replicats) mais la **collecte** de paires minimales
   interpretees.
3. **Le gain est mesure en paires, pas en fichiers.** Le meme calcul sur un
   nombre de paires accru rendrait la lecture « null global sur le maximum »
   (#27208) plus concluante elle aussi : c'est la meme geometrie.
4. **La limite declaree de la section 3 est levee, pas subvertie** : la
   section 3 concluait « plus de paires elargissent le plafond » ; cette
   section chiffre l'elargissement et son cout.

## 9. La puissance est-elle la meme sur toutes les jambes ?

Les sections 3 et 8 mesurent **une** jambe (couche 12/24, bras *trained*).
La question que le protocole d'ICT-35 pose -- 18 jambes : 3 couches x 3 types
x *trained/control* -- est plus large : **la regle est-elle sous-equipee
partout, ou sur une jambe particulierement ?**

L'echelle par paire (`per_pair_rms` = `||diffs_f||_2 / sqrt(n)`) est une
echelle **relative a la jambe** : chaque feature est normalisee par son
propre bruit. Deux jambes dont les bruits different d'un facteur cinq sont
donc directement comparables dans l'unite `d` -- ce qui n'etait pas vrai
dans l'unite de la section 3 (dispersion nulle de la statistique, qui
depend de `n` **et** de l'echelle des activations).

Les **six** traces humour disponibles dans le depot sont mesurees
(3 couches x 2 bras ; les 3 « types » du protocole n'ont pas de trace
humour commitee) : `power_by_trace`, meme graine `seed=42`, 16 bootstraps
x 200 replicats par point (3 200 tirages, erreur type ~0,4 point), grille
`n` = 30, 45, 60, 75, 90, 105, 120, 150, 180, 210, 240.

| Jambe (couche, bras) | features actives | bruit par paire median (p25 · p75 · max) | **n pour 80 %** a `d=0,5` / `0,4` / `0,3` | P(regle) a `n=30`, `d=0,5` |
| --- | ---: | --- | --- | ---: |
| couche 4, control | 4 678 | 0,00742 (0,00435 · 0,01449 · 0,2326) | **90 / 120 / 210** | 0,103 |
| couche 4, trained | 5 776 | 0,00629 (0,00341 · 0,01353 · 0,2349) | **90 / 120 / 210** | 0,089 |
| couche 12, control | 3 154 | 0,01123 (0,00657 · 0,02225 · 0,2426) | **90 / 120 / 210** | 0,102 |
| couche 12, trained | 5 642 | 0,01111 (0,00579 · 0,02156 · 0,3435) | **90 / 120 / 210** | 0,083 |
| couche 19, control | 3 538 | 0,03333 (0,01915 · 0,06603 · 0,7523) | **90 / 120 / 210** | 0,099 |
| couche 19, trained | 5 195 | 0,03368 (0,01794 · 0,07253 · 1,1613) | **90 / 120 / 210** | 0,098 |

### Ce que la mesure dit

1. **La sous-puissance est une propriete du protocole, pas d'une jambe.**
   Les six jambes franchissent le seuil de 80 % de puissance aux **memes**
   nombres de paires : 90 a `d=0,5`, 120 a `d=0,4`, 210 a `d=0,3`, jamais
   a `d=0,2` (47 % a 240 paires). Aucune jambe n'est « la jambe faible ».
   *(Lecture brute : le seuil de 80 % est ici la puissance **brute**,
   effet nul compris — voir la correction de la section 11, qui ne laisse
   debout que la ligne `d = 0,5`.)*
2. **L'heterogeneite des traces est reelle mais sans effet sur la
   puissance.** Le bruit par paire median varie d'un facteur **5,4** (de
   0,00629 a la couche 4 *trained* a 0,03368 a la couche 19 *trained*) et
   le nombre de features actives de 1,8 (3 154 a 5 776) -- mais a `(n, d)`
   fixe, l'ecart entre jambes est de l'ordre du **point de pourcentage**,
   soit l'erreur de Monte-Carlo du dispositif : a `n = 90`, `d = 0,5`,
   P(regle) va de 0,951 a 0,958. C'est exactement ce que l'unite `d`
   relativise par construction : elle compare des **effets relatifs au
   bruit de chaque jambe**.
3. **Consequence pour ICT-35d.** Le verdict `AUCUNE_FEATURE_STABLE` ne
   s'explique par une jambe degradee : avec 30 paires, la regle
   s'ecole dans **8 a 10 %** des cas a `d=0,5` sur *toutes* les jambes.
   Le protocole manque d'environ **x3** les paires pour un effet net, et
   d'environ **x7** pour un effet de 0,3 par paire -- quel que soit le
   point du reseau ou l'on se place.
   *(Les multiplicateurs `x4` et `x7` sont des lectures **brutes** ;
   la section 11 montre qu'ils ne resistent pas a la lecture en
   contraste, et qu'ils doivent etre lus comme une **borne** plutot que
   comme un nombre de paires a commander.)*
4. **Ce que cela ne dit pas.** La mesure porte sur six traces sur dix-huit
   jambes : les douze autres (les « 3 types » du protocole) n'ont pas de
   trace humour commitee. Rien ici ne les couvre.

### Limites de cette lecture

* L'effet `d` reste exprime **par rapport au bruit par paire de la jambe** ;
  une jambe qui aurait un bruit de fond plus **heterogene** d'une paire a
  l'autre n'est pas couverte par le modele additif.
* Le « `n` pour 80 % de puissance » est le **plus petit `n` mesure** qui
  franchit 0,80 : la resolution de la grille est de 15 paires, donc la
  valeur est donnee a +/- une maille.
* L'erreur de Monte-Carlo du dispositif est ~0,4 point (3 200 tirages par
  point) : les ecarts de quelques points entre jambes ne sont pas
  significatifs, et ne sont pas interpretes comme tels.

## 10. Le seuil : ce que la convention pre-enregistree coute

`|z| > 3` est une **convention** de l'instrument, pas une propriete de la
loi. Les sections precedentes mesurent la puissance a ce seuil-la ; celle-ci
mesure ce qu'il **coute**, et ce qu'un seuil different rapporterait.

Deux mesures se lisent ensemble, a `n = 30` (couche 12/24, bras *trained*) :

* la **queue nulle exacte** (`exact_null_rates`, 20 000 retournements de
  signe intra-paire sur les 30 paires reelles, **aucun re-tirage**) : ce que
  la regle ferait si le signal etait absent ;
* la **puissance brute** au meme seuil (substitut bootstrap, 8 bootstraps x
  100 replicats, `seed=42`, `k = 3` features plantees) : ce que la regle
  fait quand l'effet est present.

| Seuil | queue nulle exacte : `p_any` | queue nulle exacte : **`p_rule`** | puissance brute `d=0,3` | puissance brute `d=0,5` |
| ---: | ---: | ---: | ---: | ---: |
| 1,5 | 1,0000 | **1,0000** | 1,000 | 1,000 |
| 2,0 | 1,0000 | **0,9986** | 0,889 | 0,946 |
| 2,5 | 0,6066 | **0,0423** | 0,259 | 0,451 |
| **3,0 (pre-enregistre)** | 0,0345 | **0,0001** | 0,003 | **0,079** |
| 3,5 | 0,0006 | **0,0000** | 0,000 | 0,031 |
| 4,0 | 0,0000 | **0,0000** | 0,000 | 0,000 |

### Ce que la mesure dit

1. **Le seuil n'est pas un detail de forme : c'est lui qui tient la
   specificite.** A un seuil de 2, la regle s'ecole sous null dans
   **99,86 %** des cas -- l'instrument ne mesurerait plus rien, il
   declarerait une humidity. A 2,5, la regle deborde encore dans 4,2 % des
   cas. A **3**, elle est quasi muette : **0,01 %**. Toute la specificite de
   l'instrument tient dans ce choix de convention.
2. **L'ancre de l'organe natif se confirme a 0,15 point.** ICT-35d publie
   que le null global sur le maximum produit zero feature au-dela de 3
   sigma dans **96,7 %** des cas (soit `p_any` = 3,3 %). Le null exact
   mesure ici `p_any` = **3,45 %** -- l'ecart (0,15 point) est dans la
   bande d'erreur type des 1 000 tirages de l'organe natif. Les deux
   lectures, faites par deux chemins differents (estimateur empirique
   d'un cote, null exact de l'autre), convergent.
3. **Le prix du seuil est une puissance, pas une erreur.** A `d=0,5` par
   paire, la regle passe de **45 %** (seuil 2,5) a **7,9 %** (seuil 3) :
   un facteur 5,7 de puissance pour 4,2 points de faux positifs. L'instrument
   a 30 paires est donc **precis et muet** -- et c'est un choix coherent :
   sans la convention `|z| > 3`, ICT-35d aurait mesure l'humidite.
4. **Le seuil 3 est au coude de la courbe.** Au-dela, la specificite
   continue de monter (`p_any` passe de 0,0345 a 0,0006 a 3,5) mais la
   puissance est **deja nulle** a 3,5 (0 % a `d=0,3`) : le seuil n'achete
   plus rien. En deçà, il vend de la puissance contre de la specificite.
   Le seuil 3 est le point ou les deux courbes se croisent -- c'est la
   lecture qui justifie la convention, et non une convention heritee.

## 11. Une borne sur l'extrapolation : le substitut n'ajoute pas d'information independante

Les sections 8 et 9 extrapolent a plus de 30 paires en **reechantillonnant
les 30 paires reelles avec remise** (bootstrap). Ce substitut est valide a
`n = 30`. Au-dela, il n'ajoute pas des observations : il ajoute des
**repetitions**. Cette section mesure ce que cela coute, et corrige les
sections 8 et 9 en consequence.

### 11.1 Le null exact, qui ne degrade pas

`exact_null_rates` (module `ict/humor_power.py`) retourne le signe de
chaque paire independamment, **sans jamais remplacer une paire** : c'est
le null exact de l'instrument, et il n'est defini que pour le `n` observe.
Sur les 30 paires reelles (20 000 retournements) :

| Seuil | `p_any` (exact) | `p_rule` (exact) | features au-dela, en moyenne |
| ---: | ---: | ---: | ---: |
| 1,5 | 1,0000 | 1,0000 | 193,9 |
| 2,0 | 1,0000 | 0,9986 | 14,9 |
| 2,5 | 0,6066 | 0,0423 | 1,00 |
| **3,0** | **0,0345** | **0,0001** | 0,036 |
| 3,5 | 0,0006 | 0,0000 | 0,001 |
| 4,0 | 0,0000 | 0,0000 | 0,000 |

### 11.2 Le substitut se degrade avec `n`

La table est **regeneree depuis une grille documentee**, et non saisie
separement de la section 11.3. Les deux tables partagent les memes tirages.

**Grille de regeneration** — trace `humor35b_qwen35-2b-base_layer12of24_trained.npz`,
30 paires reelles du corpus GT-24b, seuil `t = 3`, regle d'au moins trois
features du meme cote, `d = 0` (aucun effet plante), 8 bootstraps x 100
replicats, `seed=42` :

| Critere de la grille | Derivation de la valeur de la table |
| --- | --- |
| `n` = 30, 60, 90, 120, 180, 210, 240 | Une ligne par valeur de `n` ; chaque bootstrap tire `n` indices avec remise parmi les 30 paires. |
| paires distinctes / maximum de copies | Moyenne sur les 8 bootstraps de `#{i : c_i > 0}` et de `max_i c_i`, ou `c_i` est le nombre de fois que la paire `i` est tiree. |
| `p_rule` et `p_any` a `t=3` | `power_vs_pairs(..., n_values, [0.0], n_bootstraps=8, n_replicates=100, seed=42)` : comptes sur les **800 tirages**, divises par 800. Les memes tirages produisent les faux positifs de 11.3. |
| effectif effectif median (Kish) | Pour chaque feature active et chaque bootstrap, `(sum_i abs(x_i))^2 / sum_i(x_i^2)` sur les `n` lignes reechantillonnees ; mediane sur les features actives, puis mediane sur les 8 bootstraps. |
| part de `n` | Effectif de Kish median divise par `n`, arrondi a deux decimales. |

| `n` | paires **distinctes** utilisees (max de copies) | `p_rule` a `t=3` | `p_any` a `t=3` | effectif effectif median (Kish) |
| ---: | --- | ---: | ---: | ---: |
| 30 | 19,5 / 30 (3,5) | 0,00125 | 0,05375 | 2,0 (0,07 n) |
| 60 | 25,8 / 30 (5,1) | 0,0200 | 0,20125 | 3,0 (0,05 n) |
| 90 | 28,1 / 30 (7,8) | 0,0925 | 0,34125 | 4,0 (0,04 n) |
| 120 | 29,8 / 30 (8,4) | 0,1350 | 0,4175 | 5,2 (0,04 n) |
| 180 | 30,0 / 30 (11,1) | 0,2175 | 0,49625 | 8,0 (0,04 n) |
| 210 | 30,0 / 30 (12,5) | 0,23875 | 0,5075 | 9,0 (0,04 n) |
| 240 | 30,0 / 30 (14,8) | 0,24625 | 0,5225 | 10,0 (0,04 n) |

Trois faits, tous mesures :

1. **A 30 paires, le substitut est deja un peu plus bavard que l'exact**
   (`p_any` 0,05375 contre 0,0345 ; `p_rule` 0,00125 contre 0,0001) : le
   reechantillonnage n'est pas neutre, il perd des paires (19,5 distinctes
   sur 30) et change la geometrie du design.
2. **La queue nulle du substitut se degrade avec `n`** : la regle s'ecole
   sous null dans 2,0 % des cas a 60 paires, 9,3 % a 90, 24,6 % a 240. La
   degradation vient du fait que les lignes ajoutees sont des repetitions
   du meme couple (paire, signe) : le design s'aplatit, et l'information
   effective par feature (**effectif effectif de Kish**
   `(Σ|x|)² / Σx²`) plafonne autour de **4 % de `n`** a partir de 60 paires
   -- « 240 paires » ne
   transportent qu'une dizaine de paires effectives par feature. La part
   des features a effectif effectif < 10 passe de 98 % (a `n = 30`) a 45 %
   (a `n = 240`).
3. **Le `n` mesure n'est donc pas un protocole realisable.** Une vague de
   240 paires **independantes** n'a pas la meme queue nulle que le
   substitut : la queue nulle reelle d'un design de paires independantes
   ne se degrade pas comme cela. Le substitut ne mesure donc pas « la
   puissance a 240 paires » : il mesure « ce que donne un design qui
   repete 240 fois 30 paires ».

### 11.3 La lecture en contraste, et ce qu'elle corrige

La grandeur qui resteinterpretable est le **contraste** : puissance brute
moins taux de faux positifs au meme `n` et au meme seuil. Les deux
termes sont mesures sur les memes tirages, au seuil pre-enregistre
`t = 3` (couche 12/24 *trained*, 8 bootstraps x 100 replicats) :

| `n` | faux positifs (brut) | `d=0,3` | `d=0,4` | `d=0,5` |
| ---: | ---: | --- | --- | --- |
| 30 | 0,00125 | 0,003 / **0,001** | 0,041 / **0,040** | 0,079 / **0,078** |
| 60 | 0,0200 | 0,090 / **0,070** | 0,284 / **0,264** | 0,478 / **0,458** |
| 90 | 0,0925 | 0,226 / **0,134** | 0,531 / **0,439** | 0,964 / **0,871** |
| 120 | 0,1350 | 0,404 / **0,269** | 0,819 / **0,684** | 0,999 / **0,864** |
| 180 | 0,2175 | 0,813 / **0,595** | 0,995 / **0,778** | 1,000 / **0,783** |
| 210 | 0,23875 | 0,889 / **0,650** | 1,000 / **0,761** | 1,000 / **0,761** |
| 240 | 0,24625 | 0,943 / **0,696** | 1,000 / **0,754** | 1,000 / **0,754** |

*(cellule = brut / contraste ; le contraste est en gras)*

**Ce que cette lecture corrige** (correction visible, dans le ledger et
dans le body de la PR) :

| Ce qui etait publie | Lecture brute | Lecture en contraste | Verdict |
| --- | --- | --- | --- |
| `d=0,5` : ~90 paires | 0,964 | **0,871** | **resiste** (au-dessus de 0,80) |
| `d=0,4` : ~120 paires | 0,819 | 0,684 | **ne resist pas** (plafond 0,78) |
| `d=0,3` : ~210 paires | 0,889 | 0,650 | **ne resist pas** (plafond 0,70) |

Le contraste **plafonne** : l'ecol brute sature a 1 pendant que le taux de
faux positifs continue de monter. Ce plateau n'est pas une loi de la
puissance -- c'est la signature du substitut : on ne peut pas acheter de la
puissance en repetant les memes 30 paires.

**Ce qui reste etabli, et qui est la seule lecture defensive :**

1. **A 30 paires, l'instrument est sous-equipe**, sur les six jambes
   (section 9) : 8 a 10 % d'ecol a `d=0,5`, et une queue nulle de 0,01 %
   pour la regle complete (exact) ou 3,45 % pour « au moins une feature
   au-dela de 3 ». Le zero d'ICT-35d n'interdit donc pas un effet net : il
   l'interdit *a 30 paires*.
2. **Le cout est en paires independantes**, pas en fichiers ni en
   calcul : chaque paire independante ajoute une observation, la regle
   gagne `sqrt(n)` de contraste, et rien de ce que nous mesurons ici ne
   peut etre obtenu en repetant les 30 paires existantes.
3. **Le nombre de paires independantes necessaires n'est pas estimable
   depuis ces 30 paires** : il faut des paires *nouvelles*, dont le
   protocole ne dispose pas. Les nombres « ~120 » et « ~210 » des sections
   8 et 9 doivent donc etre lus comme des **bornes** (« au-dela de 120
   paires independantes, l'effet `d=0,4` devient plausible »), pas comme
   un nombre a commander.

### Limites de cette lecture

* Le contraste est mesure sur **une** jambe (couche 12/24 *trained*) avec le
  budget de la grille grossiere (8 bootstraps x 100 replicats, erreur type
  ~1 point sur les taux, ~2 points sur les contrastes). La section 9 montre
  que l'ecart entre jambes est de l'ordre du point de pourcentage : la
  correction est donc **commune aux six jambes**, sans qu'il faille la
  remesurer sur chacune.
* Le mecanisme de degradation est **mesure** (multiplicite, effectif
  effectif, taux de faux positifs), pas **modelise** : la section dit
  *que* le substitut se degrade et de combien, pas pourquoi la queue nulle
  se deploie exactement de cette maniere.
* L'exactitude du null est etablie **pour `n = 30`** : elle ne se transpose
  pas a un `n` superieur, faute de paires independantes.

## 12. Reproduction

```bash
cd MyIA.AI.Notebooks/IIT/ICT-Series
python -m pytest ict/tests/test_humor_power.py -q
```

La courbe se relit par :

```python
from ict.humor_pairs import build_pairs, load_corpus_dur
from ict.humor_power import zone_diffs, power_curve
d = zone_diffs("traces/humor35b_qwen35-2b-base_layer12of24_trained.npz",
               build_pairs(load_corpus_dur()))
power_curve(d, [0, 1, 2, 2.5, 3, 3.5, 4, 4.5, 5], n_planted=3,
            n_replicates=1000, seed=42)
```

Duree : 3,5 s pour 1000 replicats x 10 valeurs de `delta` sur 32 768
features (numpy seul, aucune resource GPU).

La section 8 (puissance en fonction du nombre de paires) se relit par :

```python
from ict.humor_power import power_vs_pairs
power_vs_pairs(d, [30, 60, 90, 120, 180, 240], [0.2, 0.3, 0.4, 0.5],
               n_bootstraps=8, n_replicates=100, seed=42)
```

La section 9 (puissance jambe par-jambe) se relit par :

```python
from pathlib import Path
from ict.humor_power import n_for_power, power_by_trace
res = power_by_trace(
    sorted(Path("traces").glob("humor35b_*.npz")), build_pairs(load_corpus_dur()),
    [30, 45, 60, 75, 90, 105, 120, 150, 180, 210, 240], [0.2, 0.3, 0.4, 0.5],
    n_bootstraps=16, n_replicates=200, seed=42)
for leg in res["legs"]:
    print(leg["trace"], leg["n_active_features"],
          {d: n_for_power(leg["rows"], d) for d in (0.2, 0.3, 0.4, 0.5)})
```

Duree : ~4 min pour les six jambes (numpy seul, aucune resource GPU).

La section 10 (cout du seuil) se relit par :

```python
from ict.humor_power import power_vs_threshold
res = power_vs_threshold(d, [1.5, 2.0, 2.5, 3.0, 3.5, 4.0], [0.0, 0.3, 0.5],
                          n_values=[30], n_bootstraps=8, n_replicates=100, seed=42)
```

La section 11 (null exact) se relit par :

```python
from ict.humor_power import exact_null_rates
exact_null_rates(d, [1.5, 2.0, 2.5, 3.0, 3.5, 4.0], n_flips=20000, seed=42)
```

Duree : ~26 s pour 20 000 retournements sur 32 768 features (numpy seul,
memoire bornee par blocs de 256 retournements).

Les sections 11.2 et 11.3 partagent une seule grille, regeneree par :

```python
import numpy as np
from ict.humor_power import power_vs_pairs

n_values = [30, 60, 90, 120, 180, 210, 240]
res = power_vs_pairs(d, n_values, [0.0, 0.3, 0.4, 0.5],
                     n_bootstraps=8, n_replicates=100, seed=42)
for row in res["rows"]:
    print(row["n_pairs"], row["effect_size"], row["p_rule"], row["p_any"])

rng = np.random.default_rng(42)
for n in n_values:
    for _ in range(8):
        idx = rng.integers(0, d.shape[0], size=n)
        sample = d[idx]
        copies = np.bincount(idx, minlength=d.shape[0])
        sums = np.abs(sample).sum(axis=0)
        squares = (sample**2).sum(axis=0)
        active = squares > 0
        kish = sums[active]**2 / squares[active]
        print(n, "distinct=", (copies > 0).sum(), "max_copies=", copies.max(),
              "kish_median=", np.median(kish), "kish_lt10=", np.mean(kish < 10))
```

La colonne `p_rule` de `d=0` est commune aux tables 11.2 et 11.3 ; dans
11.3, chaque contraste est le `p_rule` brut du meme `n` et du meme `d`
moins ce faux-positif de la grille. Les `p_any` et les statistiques de
multiplicite sont tires de cette meme execution.
