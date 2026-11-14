# Reproduction hors carnet des sondes wavelet scattering (WS-00c, WS-03)

> REFERENCE — vivante — dernière révision 2026-11-11

**Provenance** : issue #21823, suite de la revue [NanoClaw] du 2026-10-21 sur la PR #21771
(« pas de cache Fashion-MNIST ici ; chiffres cités comme mesure de l'auteur »).

**Objet** : établir si les quatre valeurs citées par la série wavelet scattering sont
reproductibles **hors du carnet**, c'est-à-dire indépendamment de l'ordre d'exécution et
de l'état de cache d'une session notebook.

**Outil** : [`scripts/repro/ws_probes_repro.py`](../../scripts/repro/ws_probes_repro.py) —
autonome, graine fixe, imprime les versions, sort en `1` en cas d'écart.

## Paramètres relevés dans les carnets

| Sonde | Carnet, cellule | Corpus | Prétraitement | Classifieur |
|---|---|---|---|---|
| WS-00c | `WS-00c-Scattering-from-scratch.ipynb`, cellules 20-21 (§6) | Fashion-MNIST **train**, **80 premières** images de chaque classe (`np.where(labs == c)[0][:80]`) | pad 28→32, split 75/25 stratifié | `LogisticRegression(max_iter=3000, C=1.0)`, **sans** `random_state` |
| WS-03 | `WS-03-Synthese-Scattering-vs-ResNet.ipynb`, cellule 8 | Fashion-MNIST **train et test**, 150 / 75 par classe tirées par `default_rng(42)` | 28×28 brut, `StandardScaler` ajusté sur le **train seul** | `LogisticRegression(max_iter=3000, C=1.0, random_state=42)` |

Le test translaté a le même **geste** dans les deux carnets (décalage ±2 px alterné, périodique
aux bords, `np.roll`) mais **pas le même index de parité** — et c'est un finding de série, pas
un détail d'implémentation :

- WS-00c alterne sur la parité **globale** (`for i in te_i`, où `te_i` indexe le corpus entier) ;
- WS-03 alterne sur la parité **locale** (`enumerate(X_te)`, donc `0..n-1`).

Sur un même jeu de test, les images des deux parités ne sont donc pas les mêmes : deux carnets
qui se présentent comme comparables appliquent deux tests translatés différents. Le script
respecte chacune (`probe_ws00c` itère `te_i` ; `alternating_shift` prend la parité locale, pour
WS-03).

## Résultat mesuré

Exécution du 2026-10-24, Python 3.13.3, numpy 2.3.5, **scikit-learn 1.6.1**, graine 42,
corpus `torchvision` (cache `~/.cache/ft00a`).

| Sonde | État | Mesuré | Cité | Écart | Verdict |
|---|---|---:|---:|---:|---|
| WS-00c | test propre | 0.7900 | 0.790 | 0.0000 | **ok** |
| WS-00c | test translaté | 0.4300 | 0.430 | 0.0000 | **ok** |
| WS-03 | test propre | 0.7800 | 0.780 | 0.0000 | **ok** |
| WS-03 | test translaté | 0.3107 | 0.311 | −0.0003 | **ok** |

**Verdict contre l'artefact committé d'octobre : `MISMATCH`** — trois valeurs sur quatre
reproduites à la précision d'affichage ; la quatrième (WS-00c translaté) s'écarte d'**un
item** (`86/200` mesuré vs `85/200` cités — la ligne `pixels` committait alors `0.425`).
C'est cet écart qui a ouvert #21823. **Contre l'artefact committé au head** — `0.430`
(`86/200`) depuis le rejeu du 2026-11-01 (#23812) — **la mesure du 10-24 est exacte** : la
dérive étudiée ici a rattrapé l'artefact lui-même. La colonne « Cité » des tables de ce
document référence le head.

### Contre-mesure du 2026-11-01 : même script, environnement différent

Exécution du 2026-11-01 sur ce même siège, Python 3.13.14, numpy 2.4.2, **scikit-learn 1.8.0**,
graine 42, corpus `torchvision`, cache `~/.cache/ft00a`. **Le script est inchangé** — mais
**trois** versions ont bougé depuis le 2026-10-24 (Python `3.13.3 → 3.13.14`,
numpy `2.3.5 → 2.4.2`, scikit-learn `1.6.1 → 1.8.0`). La comparaison ci-dessous porte donc
sur **deux environnements**, pas sur deux versions d'une seule bibliothèque.

| Sonde | État | 2026-10-24 | 2026-11-01 | Cité | Verdict 11-01 |
|---|---|---:|---:|---:|---|
| WS-00c | test propre | 0.7900 | 0.7900 | 0.790 | **ok** |
| WS-00c | test translaté | 0.4300 | **0.4350** | 0.430 | écart |
| WS-03 | test propre | 0.7800 | 0.7800 | 0.780 | **ok** |
| WS-03 | test translaté | 0.3107 | 0.3107 | 0.311 | **ok** |

Le test **propre** de WS-00c et **les deux** valeurs de WS-03 sont identiques au chiffre près
d'un environnement à l'autre. Seul le test **translaté** de WS-00c se déplace : `0.4300 → 0.4350`,
soit **un item de plus** — **un item** au-dessus de la valeur committée au head (`0.430`,
`86/200`), deux au-dessus de l'artefact d'octobre (`0.425`, `85/200`, committé jusqu'au
rejeu du 2026-11-01, #23812).

### Troisième point : même version de scikit-learn, deux résultats

Une contre-mesure indépendante (lane `myia-po-2025:CoursIA-2`, 2026-11-01) rejoue **le script
du dépôt, inchangé**, sous **la même version de scikit-learn** que ci-dessus (1.8.0) et le même
Python (3.13.14), sur un autre siège, six exécutions et deux caches distincts :

| Siège | Python | numpy | scikit-learn | WS-00c translaté |
|---|---|---|---:|---:|
| po-2024 (ce siège) | 3.13.14 | 2.4.2 | 1.8.0 | **0.4350** (87/200) |
| po-2025 | 3.13.14 | 2.4.6 | 1.8.0 | **0.4300** (86/200), 6/6 runs |
| po-2024, 2026-10-24 | 3.13.3 | 2.3.5 | 1.6.1 | 0.4300 (86/200) |

La ligne de référence vaut donc `0.4300`, et elle se retrouve **sous deux versions différentes**
de scikit-learn (1.6.1 comme 1.8.0). Sous 1.8.0, deux sièges rendent deux valeurs différentes.
Le déplacement observé le 2026-11-01 sur ce siège n'est donc pas attribuable à `scikit-learn`.

Noter l'interpréteur : les exécutions du 2026-11-01 et la campagne du 2026-11-02 ont tourné
sous `Python 3.13.14` ; le siège est passé à `3.13.15` dans la matinée du 01/11 — le rejeu du
carnet de #23812 (mergé 08:50Z) déclare déjà `3.13.15` en `language_info` — et c'est encore sa
version au jour de cette PR. L'interpréteur n'est donc pas tenu constant **à l'intérieur même
du 01/11**, ce qui laisse intact son statut « ouvert » dans la table des causes ci-dessous.

### Quatrième point : les versions n'expliquent rien — élimination contrôlée sur un seul siège (2026-11-02)

Les mesures ci-dessus font varier **plusieurs facteurs à la fois** : du 2026-10-24 au 2026-11-01,
trois versions ont bougé ensemble. Une campagne à **un seul facteur** départage autrement. Elle
porte sur le siège `po-2024`, sur le script du dépôt inchangé (`ebba155ebae`, aucun diff avec
`main`), et ne change **qu'une** chose à la fois — une version de paquet surchargée par
`PYTHONPATH`, ou une variable d'environnement — sans toucher à l'environnement de base :

| numpy | scikit-learn | threads OpenBLAS | WS-00c translaté | facteur mis en cause |
|---|---|---:|---:|---|
| 2.4.2 (base) | 1.8.0 (base) | 24 (base) | **0.4350** | référence du jour |
| **2.4.6** | 1.8.0 | 24 | **0.4350** | `numpy` seul |
| 2.4.2 | 1.8.0 | **1** | **0.4350** | threads BLAS seuls |
| 2.4.2 | **1.6.1** | 24 | **0.4350** | `scikit-learn` seul |
| **2.3.5** | **1.6.1** | 24 | **0.4350** | les deux versions du 2026-10-24 |

Cinq exécutions, aucune ne s'écarte de `0.4350`. **Les versions de `numpy` et de
`scikit-learn`, ainsi que le parallélisme BLAS, sont donc réfutés comme cause** : sur ce siège,
la valeur ne bouge pas quand ils changent, y compris en reconstituant exactement le jeu de
bibliothèques qui rendait `0.4300` le 2026-10-24.

Le seul facteur que cette campagne n'a pas pu tenir constant entre ce `0.4300` et le `0.4350`
d'aujourd'hui est l'**interpréteur lui-même** — `Python 3.13.3` le 24/10, `3.13.14` le 01/11,
`3.13.15` aujourd'hui —
qu'on ne remplace pas sans reconstruire l'environnement du siège. Cela reste une **hypothèse non
testée**, pas une attribution.

Conséquence pour la lecture de l'écart : ce n'est pas « `numpy 2.4.6` contre `2.4.2` » qui sépare
les deux sièges. **C'est le siège.** Deux machines peuvent rendre deux valeurs sans qu'aucune
version de paquet ne les distingue, et épingler les paquets ne fait donc pas converger deux
exécutions.

## Lecture de l'écart WS-00c : dépendance d'environnement, cause non établie

Le test propre de WS-00c se reproduit **à l'identique** partout (`0.7900 = 158/200`), ainsi que
les deux valeurs de WS-03. Seul le test translaté de WS-00c varie : `0.4350` et `0.4300` sous
`scikit-learn 1.8.0` selon le siège, `0.4300` sous `1.6.1`. Un point de test vaut `1/200 = 0.005`.

Ce qui **est** établi : la valeur du test translaté de WS-00c n'est pas une propriété du carnet —
elle dépend de l'environnement d'exécution, et le `LogisticRegression` de cette sonde est
instancié **sans `random_state`**.

Ce qui n'est **pas** établi : **lequel** des facteurs est causal. L'état de chaque candidat après
la campagne d'élimination contrôlée du 2026-11-02 (section « Quatrième point ») :

| Candidat | État | Ce qui l'établit |
|---|---|---|
| la version de `scikit-learn` | **réfutée** | à version identique (1.8.0) deux sièges divergent ; et `1.6.1` sur ce siège ne reproduit pas `0.4300` |
| la version de `numpy` | **réfutée** | `2.4.2`, `2.4.6` et `2.3.5` rendent `0.4350` sur ce siège ; elle n'était « le seul facteur visible » que d'une comparaison **entre deux sièges**, où elle covariait avec le siège lui-même |
| le parallélisme BLAS | **réfuté** | `OPENBLAS_NUM_THREADS=1` contre 24 threads : `0.4350` dans les deux cas |
| la chaîne BLAS du siège (sélection de noyau à l'exécution) | **ouverte** | reste le mécanisme plausible par lequel deux sièges aux mêmes paquets divergent ; non départageable sur un seul siège |
| l'interpréteur (`3.13.3` → `3.13.14` → `3.13.15`) | **ouvert, non testé** | seul facteur non tenu entre le `0.4300` du 24/10 et le `0.4350` du jour ; non remplaçable sans reconstruire l'environnement |

Ce qui **reste** à faire pour départager : relever la chaîne BLAS des deux sièges
(`numpy.show_config()`, version d'OpenBLAS et noyau sélectionné) et comparer — c'est une mesure
de siège, pas de bibliothèque. **Non faite à ce jour** ; ce document ne la remplace pas par une
attribution.

La lecture « l'écart est de l'ordre d'un ou deux items, comparable à la variabilité intrinsèque de
la sonde » vaut donc pour les environnements qui l'ont produite, pas au-delà. Le chiffre d'un
carnet qui ne fixe ni la source de données, ni les versions, ni le siège est une **mesure
d'environnement**.

Les valeurs citées sont **les sorties committées au head** du carnet WS-00c, ligne `pixels` de
la table de `WS-00c-Scattering-from-scratch.ipynb` (artefact committé :
`pixels | 0.790 | 0.430`) — et non les lignes `scattering S1` (`0.805 / 0.700`) ni
`scattering complet` (`0.825 / 0.760`). La sonde reproduit le classifieur linéaire sur pixels
bruts, donc cette ligne-là. La ligne committée elle-même a dérivé : `0.425` (`85/200`) jusqu'au
2026-11-01, `0.430` (`86/200`) depuis le rejeu sous noyau 3.13.15 (#23812, `fb453c45aca`),
puis `tol=1e-8` épinglée le 2026-11-02 (#24083, `c1174b7f84f`) sans que la valeur bouge.

**Provenance du couple `0.773 / 0.431` cité par une version antérieure de ce script : non
établie.** Deux mesures indépendantes l'écartent de WS-00c :

- il n'apparaît dans **aucun fichier** de la série (`git grep` sur les fichiers de
  `05-Wavelet-Scattering` à `origin/main` : 0 occurrence des deux valeurs) — alors que
  `0.425` y est traçable : un commentaire de la cellule 21 le cite, la ligne `pixels`
  committée le portait jusqu'au rejeu du 01/11, et WS-03 l'imprime comme score de
  scattering construit ;
- il est **arithmétiquement impossible** sur le corpus de WS-00c : la cellule 20 imprime
  `corpus : 600 train / 200 test`, et aucune accuracy sur 200 items ne peut s'écrire `0.773`
  ni `0.431` (il faudrait un `k` tel que `k/200` s'arrondisse à ces valeurs ; il n'en existe
  pas). Le couple est en revanche compatible avec un test d'environ 750 items — la taille du
  découpage de WS-03 — mais cette compatibilité **n'est pas une provenance** : elle dit
  seulement que ce n'est pas une mesure de WS-00c.

Deux causes candidates pour ce décalage, la première restant non testée, la seconde
désormais mesurée :

1. **Fork de source dans la cellule du carnet (cause structurelle).** La cellule 20 essaie
   `torchvision.datasets.FashionMNIST` puis retombe sur `fetch_openml("Fashion-MNIST")`.
   Les deux sources ne rangent pas les images dans le même ordre, et la sonde sélectionne
   les **80 premières** de chaque classe : c'est donc un **sous-ensemble différent** selon
   la branche empruntée. La valeur citée dépend de la machine qui l'a produite, sans que le
   carnet le dise.
   **Non testé ici** : `fetch_openml` est injoignable depuis cette machine
   (`URLError: [WinError 10060]`), donc la branche openml n'a pas pu être exécutée. Le script
   expose `--source openml` pour que le test soit rejouable sur une machine qui atteint OpenML.

2. **Dérive de version de scikit-learn — testée le 2026-11-01, non concluante.** La version
   employée par l'auteur n'est pas consignée dans le carnet ; une évolution du comportement de
   `LogisticRegression` (solveur, multimodal) pouvait déplacer une prédiction. Le test est fait,
   sans réimplémentation : **le script de ce dépôt, inchangé**, rejoué sous `scikit-learn 1.8.0`
   rend `0.4350` sur ce siège — mais `0.4300` sur un second siège sous **la même version 1.8.0**
   et le même Python (tableau ci-dessus). Une version qui rend deux valeurs n'explique pas le
   déplacement à elle seule : **la cause reste plausible, elle n'est pas établie.** Le test propre
   et WS-03 ne bougent pas, ni ici ni là-bas.

Ce qui est **mesuré** : sur la branche `torchvision`, le test propre est exact partout et le test
translaté s'écarte de la valeur committée d'octobre (`0.425`) — d'un item sur deux sièges, de
deux sur un troisième ; contre le head (`0.430`), l'écart d'un item ne subsiste que sur ce
siège. Le
chiffre dépend donc de l'**environnement** d'exécution, et cette dépendance est reproductible au
sens où elle se répète run après run sur un siège donné (6/6 sur po-2025, déterministe ici) ;
**quel** facteur de l'environnement la porte n'est pas établi.

**Contrôle indépendant du finding de parité (2026-11-01).** Une réimplémentation
indépendante de WS-00c, écrite sans lire cette section, a fait basculer le test translaté sur
la parité **locale** au lieu de la parité **globale** `te_i`, et a obtenu `0.410` au lieu de
`0.430`. C'est exactement le piège décrit plus haut, et il coûte quatre items — soit plus que
l'écart total étudié. Le finding de parité n'est donc pas théorique : il a été vérifié par un
agent qui s'y est fait prendre.

## Troisième cause, celle-ci mesurée : la tolérance d'arrêt du solveur

Les deux causes ci-dessus sont restées non testées. Une troisième, absente de la liste, est
maintenant **mesurée** : `LogisticRegression` ne s'arrête pas sur un optimum unique mais sur
un **critère de norme de gradient** (`tol`, défaut `1e-4`). L'objectif L2 est strictement
convexe, donc l'optimum est unique — mais deux chemins numériques différents (version de
scikit-learn, chaîne BLAS, ordre de réduction) peuvent s'arrêter à des points **différents**,
et l'écart entre ces points n'est pas de l'ordre du bruit d'arrondi.

L'outil est [`scripts/repro/ws_probes_margin.py`](../../scripts/repro/ws_probes_margin.py).
Il mesure les deux moitiés de cette phrase.

**1. L'amplitude nécessaire pour déplacer un item.** La classe prédite d'un item ne change
que si son écart `score(top1) − score(top2)` traverse zéro ; cet écart est donc la
perturbation **minimale** que le mécanisme doit atteindre pour changer le compte. Ajustement
du carnet au siège `po-2024` (Python 3.13.14, numpy 2.4.2, scikit-learn 1.8.0), test
translaté, 200 items :

| Mesure | Valeur |
|---|---|
| marge minimale du jeu (item 123) | `9.282508e-03` |
| marge la moins chère pour **gagner** un item (item 123, classe réelle = second score) | `9.282508e-03` |
| marge la moins chère pour **perdre** un item (item 178) | `1.240631e-02` |
| items sous `1e-3` | `0` |
| items sous `1e-2` | `1` |
| perturbation requise pour l'écart d'un item observé | `1.240631e-02`, soit `1,2e7` fois le seuil de bruit `1e-9` |

Un désaccord d'un item exige donc de l'ordre de `1e-2`, là où une réduction de somme en
float64 déplace un score de `1e-16` relatif : l'écart entre sièges **n'est pas** un effet
d'ordre de réduction, il faut que le modèle ajusté diffère réellement.

**Le sens de l'écart décide du vivier.** Ce siège mesure `0.4350`, l'autre `0.4300` : nous
sommes **plus haut**, donc réconcilier les deux suppose de **détruire** un item que nous
réussissons — pas d'en gagner un. La marge pertinente est celle des items **perdables**
(`1.240631e-02`), et non la plus petite marge du jeu (`9.282508e-03`, item 123, qui est
*winnable*). Ce sont deux nombres différents, et prendre le premier pour le second sous-estime
la perturbation requise. L'instrument sépare les deux sens pour cette raison.

**2. La tolérance suffit, à elle seule, à produire cet écart.** Même siège, mêmes données,
même graine, même version : seule la tolérance change.

| `tol` | exactitude | itérations | déplacement max des coefficients | items qui changent |
|---|---:|---:|---|---|
| `1e-4` (défaut du carnet) | `0.4350` | 210 | référence | aucun |
| `1e-6` | `0.4300` | 492 | `1.76e-02` | item 181 (**perte**) |
| `1e-8` | `0.4300` | 765 | `1.74e-02` | item 181 (**perte**) |

Trois lectures, dans l'ordre de ce qu'elles changent pour la série :

- Les deux valeurs observées entre sièges (`0.4350` et `0.4300`) sont **reproduites sur un
  seul siège** par un réglage de solveur légitime. Aucune différence de données ni de version
  n'est nécessaire pour les obtenir.
- À `1e-4` l'ajustement s'arrête à 210 itérations ; à `1e-6` il en faut 492 et les
  coefficients se déplacent de `1.76e-02`, du même ordre que la marge à franchir. C'est le
  mécanisme : le critère d'arrêt laisse le modèle à une distance des données qui suffit à
  faire basculer un item.
- L'item qui bascule est **181** (`1.328711e-02`). Ni **123**, la marge minimale du jeu
  (`9.282508e-03`, et de surcroît *winnable*, mauvais sens), ni **178**, le perdable le moins
  cher (`1.240631e-02`). La marge est une **borne** sur la perturbation requise, elle n'est pas
  un **sélecteur** : elle dit ce qu'il faut au minimum pour que *quelque chose* bascule, pas ce
  qui basculera. La perturbation a une direction propre, et c'est elle qui décide. Annoncer
  « c'est l'item le plus proche qui bougera » serait doublement faux — de sens et de sélection —
  et c'est exactement ce que la mesure évite.

Cette lecture **réunit les deux premières causes** au lieu de les opposer. La valeur mesurée
en 1.6.1 (section précédente) est `0.4300` ; l'ajustement 1.8.0 **convergé** rend `0.4300` ;
seul l'ajustement 1.8.0 arrêté au défaut rend `0.4350`. Un changement de version déplace le
chemin des itérées, et le critère d'arrêt transforme ce déplacement en un item d'écart. Épingler
la source et la version, comme le demande la section suivante, **ne suffit donc pas** : la
tolérance doit être fixée elle aussi — c'est fait depuis le 2026-11-02 (#24083).

**Ce qui n'est pas établi** : que le siège `po-2025` s'arrête effectivement plus près de
l'optimum. La mesure démontre qu'un tel arrêt **suffit** à produire l'écart, pas qu'il en est
la cause là-bas. Les deux premières causes restent donc ouvertes.

## Ce que WS-03 établit, en revanche

Les deux valeurs de `WS-03` sont reproduites à la troisième décimale **et** la sonde WS-03
est la plus contrainte des deux (corpus disjoint train/test, `StandardScaler` sur le train
seul, `random_state` explicite). Cela confirme que la **recette** de la sonde est saine ;
c'est la variabilité de son **approvisionnement en données** (WS-00c) qui n'est pas figée.

## Conséquence pour la série (hors périmètre de cette PR)

La cellule WS-00c gagnerait à **épingler sa source** au lieu de laisser un `try/except`
choisir implicitement, et à consigner l'environnement (versions et siège) à côté des valeurs
citées. La **tolérance du solveur est épinglée depuis le 2026-11-02** (#24083, `c1174b7f84f` :
`tol=1e-8`, la sortie committée porte `tol=1e-8 epingle` et rend `0.430`) — le levier mesuré
en troisième cause ci-dessus est retiré. Tant que la source n'est pas épinglée, un chiffre de
WS-00c reste une **mesure d'environnement**, pas une propriété du carnet : deux sièges sous les
mêmes versions de `scikit-learn` et de Python en rendent deux différentes. Le suivi ouvert est
**#24075**.

Épingler les paquets ne suffit donc **pas** à faire converger deux exécutions — c'est le résultat
direct de la campagne du 2026-11-02 : sur un siège donné, faire varier `numpy`, `scikit-learn` et
le parallélisme BLAS ne déplace pas la valeur ; ce sont les sièges qui diffèrent entre eux. Une
valeur citée sans son siège reste donc une mesure d'environnement, **quelles que soient** les
versions consignées à côté.

Un `random_state` ne remplacerait pas cette prescription : sous `lbfgs`, le solveur par défaut
de `LogisticRegression`, la graine est **inerte** — mesuré sur scikit-learn 1.8.0, `random_state`
42, 7 et 123 rendent des coefficients identiques au bit près, alors qu'elle les déplace sous
`saga` (`3.45e-04`, contrôle positif) : l'inertie est une propriété du solveur, pas du test.
Le levier opérant est la **tolérance** : mesuré sur cette sonde (#21823), à données, graine et
versions identiques, passer de `tol=1e-4` à `1e-6` déplace les coefficients de `1.76e-02` et un
item. Fixer la graine ne coûte rien, mais c'est la tolérance qui opère ici — et si un jour le
solveur change, la graine redeviendra pertinente. Le suivi est ouvert : **#24075** (source du
corpus et chaîne BLAS ; la tolérance y est réglée par #24083). Cette PR ne modifie aucun carnet.

## Reproduction

```bash
python scripts/repro/ws_probes_repro.py                     # source torchvision (auto)
python scripts/repro/ws_probes_repro.py --source openml      # branche de repli du carnet
python scripts/repro/ws_probes_repro.py --out rapport.json   # rapport structure
```

### Élimination contrôlée : une seule variable à la fois

Les paquets variants sont installés dans un répertoire isolé et surchargés par `PYTHONPATH` —
l'environnement de base n'est pas modifié, et le script reste celui du dépôt :

```bash
SP=/chemin/isolé            # numpy 2.4.6, puis scikit-learn 1.6.1
SP2=/chemin/isolé-2         # numpy 2.3.5

pip install --target $SP "numpy==2.4.6"
PYTHONPATH=$SP python scripts/repro/ws_probes_repro.py            # numpy seul

pip install --target $SP --no-deps "scikit-learn==1.6.1"
PYTHONPATH=$SP python scripts/repro/ws_probes_repro.py            # scikit-learn seul

OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 \
  python scripts/repro/ws_probes_repro.py                         # threads BLAS seuls

pip install --target $SP2 "numpy==2.3.5"                          # + le 1.6.1 ci-dessus
PYTHONPATH=$SP2:$SP python scripts/repro/ws_probes_repro.py       # les deux versions du 24/10
```

Relever la chaîne BLAS du siège, à joindre à toute valeur citée :

```bash
python -c "import numpy; numpy.show_config()"
```

Le script sort `0` si les quatre valeurs concordent, `1` sinon.

```bash
python scripts/repro/ws_probes_margin.py                             # structure de marge seule
python scripts/repro/ws_probes_margin.py --observed 0.4300 --strict   # l'ecart d'un item est-il arithmetique ?
python scripts/repro/ws_probes_margin.py --observed 0.4300 --tol 1e-4 --tol 1e-6 --tol 1e-8
python scripts/repro/ws_probes_margin.py --out marges.json
```

`--strict` sort `1` quand la perturbation requise depasse `--noise-bound` : l'ecart observe
n'est alors pas de l'arithmetique. Il sort `2` quand l'ecart depasse le vivier (question reelle,
indecidable a cette taille de jeu) — jamais `0`, qu'une CI lirait « rien a signaler » ; `0`
reste l'accord au dixieme d'item pres ou l'arithmetique. `--tol` rejoue l'ajustement a chaque
tolerance et nomme les items dont la classe predite change.

## Voir aussi

- #21823 — issue de suivi (revue NanoClaw du 2026-10-21)
- #20893 — série wavelet scattering (WS-00a à WS-03)
- #21771 — PR de la correction de prose sur laquelle porte la revue